/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.Assignment;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;
import soot.dava.internal.javaRep.DAssignStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        ArrayDeque<Stmt> stmts = new ArrayDeque<>();
        Set<Stmt> r1 = new HashSet<>(); // 可以到达的
        Set<Stmt> r2 = new HashSet<>(); // 已经到达的
        stmts.addLast(cfg.getEntry());
        r1.add(cfg.getEntry());
        r1.add(cfg.getExit());

        while(!stmts.isEmpty()){
            Stmt stmt = stmts.pollFirst();
            r2.add(stmt);
            // 赋值语句
            if(stmt instanceof AssignStmt){
                AssignStmt Astmt = (AssignStmt)stmt;
                SetFact<Var> LVresult = liveVars.getResult(Astmt);
                LValue LV = Astmt.getLValue();
                RValue RV = Astmt.getRValue();
                // 处理特殊情况： 左值是死变量，右值是没有副作用的语句
                if(LV instanceof Var && !LVresult.contains((Var)LV) && hasNoSideEffect(RV)){
                    System.err.println("特殊情况： 左值是死变量，右值是没有副作用的语句，不用添加到可达");
                }
                else r1.add(Astmt);
                // 向前缀扩散
                for(Stmt succ : cfg.getSuccsOf(Astmt)){
                    if (!r2.contains(succ))
                        stmts.addLast(succ);
                }
            }
            // 控制流语句 if
            else if (stmt instanceof If){
                If Ifstmt = (If) stmt;
                CPFact result = constants.getResult(Ifstmt);
                ConditionExp condition = Ifstmt.getCondition();
                ConditionExp.Op operator = condition.getOperator();
                Value evaluate = ConstantPropagation.evaluate(condition,result);
                r1.add(Ifstmt);
                // if条件永真或者永假时
                if(evaluate.isConstant()){
                    boolean stmt_is_const = evaluate.getConstant() != 0;
                    Edge.Kind EdgeKind = stmt_is_const? Edge.Kind.IF_TRUE: Edge.Kind.IF_FALSE;
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                        if(edge.getKind() == EdgeKind){
                            Stmt target = edge.getTarget();
                            if(!r2.contains(target))
                                stmts.add(target);
                        }
                    }
                }
                // 正常的if条件
                else{
                    for(Stmt succ : cfg.getSuccsOf(stmt)){
                        if(!r2.contains(succ))
                            stmts.addLast(succ);
                    }
                }
            }
            // 控制流语句 switch
            else if(stmt instanceof SwitchStmt){
                SwitchStmt Sstmt = (SwitchStmt)stmt;
                Var var = Sstmt.getVar();
                CPFact result = constants.getResult(Sstmt);
                r1.add(Sstmt);
                // switch表达式是常数时
                if(result.get(var).isConstant()){
                    int const_case = result.get(var).getConstant();
                    // 查找有没有匹配的项
                    boolean match = false;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(Sstmt)){
                        // 有匹配的项
                        if(edge.getKind() == Edge.Kind.SWITCH_CASE
                            && edge.getCaseValue() == const_case){
                            match = true;
                            Stmt target = edge.getTarget();
                            if(!r2.contains(target))
                                stmts.add(target);
                        }
                    }
                    // 没有匹配的项
                    if(!match){
                        Stmt Dtarget = Sstmt.getDefaultTarget();
                        if(!r2.contains(Dtarget))
                            stmts.add(Dtarget);
                    }
                }
                else{
                    for (Stmt succ : cfg.getSuccsOf(Sstmt)) {
                        if (!r2.contains(succ))
                            stmts.addLast(succ);
                    }
                }
            }
            // 其他类型的语句
            else{
                r1.add(stmt);
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!r2.contains(succ))
                        stmts.addLast(succ);
                }
            }

        }
        for(Stmt stmt : ir.getStmts()){
            if(!r1.contains(stmt)){
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }


    private void getAllDeadCodeSucc(CFG<Stmt> cfg, Stmt stmt, Set<Stmt> deadCode) {
        if(stmt != cfg.getEntry() && stmt != cfg.getExit()) {
            Set<Stmt> succsOf = cfg.getSuccsOf(stmt);
            Set<Stmt> predsOf = cfg.getPredsOf(stmt);
            if (predsOf.size() == 1 || deadCode.containsAll(predsOf)) {
                deadCode.add(stmt);
                for (Stmt succStmt : succsOf) {
                    getAllDeadCodeSucc(cfg, succStmt, deadCode);
                }
            }
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
