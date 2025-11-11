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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;


public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        List<Var> params = cfg.getIR().getParams();
        CPFact cpFact = new CPFact();
        for (Var var : params) {
            if(canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            target.update(var, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1 == null)return v2;
        if(v2 == null)return v1;
        if(v1.isNAC() || v2.isNAC()) return Value.getNAC();
        else if (v1.isUndef()) return v2;
        else if (v2.isUndef()) return v1;
        else if (v1 == v2 || (v1.getConstant() == v2.getConstant())) return v1;
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact gen = new CPFact();
        CPFact inTmp = in.copy();
        if(stmt instanceof DefinitionStmt) {
            DefinitionStmt assign = (DefinitionStmt) stmt;
            LValue lValue = assign.getLValue();
            RValue rValue = assign.getRValue();
            if(lValue instanceof Var && canHoldInt((Var) lValue)) {
                Var lv = (Var) lValue;
                if(rValue instanceof IntLiteral) {
                    gen.update(lv, Value.makeConstant(((IntLiteral) rValue).getValue()));
                } else if(rValue instanceof Var) {
                    gen.update(lv, in.get((Var)rValue));
                } else if(rValue instanceof BinaryExp) {
                    gen.update(lv, evaluate(rValue, in));
                } else {
                    gen.update(lv, Value.getNAC());
                }
                inTmp.remove(lv);
            }
            boolean isChange = out.copyFrom(gen);
            return out.copyFrom(inTmp) || isChange;
        } else {
            return out.copyFrom(inTmp);
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var) {   // 变量
            return in.get((Var) exp);
        }
        else if (exp instanceof IntLiteral) {  // 常量
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        // 二元表达式
        Value v1 = in.get(((BinaryExp) exp).getOperand1());
        Value v2 = in.get(((BinaryExp) exp).getOperand2());
        BinaryExp.Op operator = ((BinaryExp) exp).getOperator();
        if(exp instanceof ArithmeticExp
                && (((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.DIV
                    ||((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.REM)
                && v2.isConstant()
                && v2.getConstant() == 0) {
            // 除数是0. 返回UNDEF
            return Value.getUndef();
        }
        if(v1.isNAC() || v2.isNAC()){
            // 至少有一个NAC，返回NAC
            return Value.getNAC();
        }
        if(v1.isUndef() || v2.isUndef()){
            // 至少有一个Undef，返回Undef
            return Value.getUndef();
        }
        if(v1.isConstant() && v2.isConstant()) {
            // 二元表达式 1. 返回运算的值 2. 返回NAC
            int i1 = v1.getConstant();
            int i2 = v2.getConstant();
            if (exp instanceof ArithmeticExp) {
                if((((ArithmeticExp.Op) operator) == ArithmeticExp.Op.DIV
                        || ((ArithmeticExp.Op) operator) == ArithmeticExp.Op.REM)
                        && i2 == 0) {
                    return Value.getUndef();
                }
                switch ((ArithmeticExp.Op) operator) {
                    case ADD -> {return Value.makeConstant(i1+i2);}
                    case SUB -> {return Value.makeConstant(i1-i2);}
                    case MUL -> {return Value.makeConstant(i1*i2);}
                    case DIV -> {return Value.makeConstant(i1/i2);}
                    case REM -> {return Value.makeConstant(i1%i2);}
                    default -> {
                        System.out.println("panic: Unknown Arithmetic operator");
                        return Value.makeConstant(0);
                    }
                }
            }
            if (exp instanceof ShiftExp) {
                switch ((ShiftExp.Op) operator) {
                    case SHL -> {return Value.makeConstant(i1<<i2);}
                    case SHR -> {return Value.makeConstant(i1>>i2);}
                    case USHR -> {return Value.makeConstant(i1>>>i2);}
                    default -> {
                        System.out.println("panic: Unknown Shift operator");
                        return Value.makeConstant(0);
                    }
                }
            }
            if (exp instanceof BitwiseExp) {
                switch ((BitwiseExp.Op) operator) {
                    case OR -> {return Value.makeConstant(i1|i2);}
                    case AND -> {return Value.makeConstant(i1&i2);}
                    case XOR -> {return Value.makeConstant(i1^i2);}
                    default -> {
                        System.out.println("panic: Unknown Bitwise operator");
                        return Value.makeConstant(0);
                    }
                }
            }
            if (exp instanceof ConditionExp){
                switch((ConditionExp.Op) operator){
                    case EQ -> {return Value.makeConstant((i1==i2)?1:0);}
                    case GE -> {return Value.makeConstant((i1>=i2)?1:0);}
                    case GT -> {return Value.makeConstant((i1> i2)?1:0);}
                    case LE -> {return Value.makeConstant((i1<=i2)?1:0);}
                    case LT -> {return Value.makeConstant((i1< i2)?1:0);}
                    case NE -> {return Value.makeConstant((i1!=i2)?1:0);}
                    default -> {
                        System.out.println("panic: Unknown Condition operator");
                        return Value.makeConstant(0);
                    }
                }
            }
            return Value.getNAC();
        }
        return Value.getUndef();
    }
}
