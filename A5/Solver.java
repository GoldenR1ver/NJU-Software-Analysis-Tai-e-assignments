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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.awt.*;
import java.util.ArrayDeque;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.IntStream;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    //添加队列 reachableStmts
    private Queue<Stmt> reachableStmts = new ArrayDeque<>();

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            List<Stmt> stmts = method.getIR().getStmts();
            for(Stmt stmt: stmts){
                reachableStmts.add(stmt);
                stmt.accept((stmtProcessor));
            }
        }
    }


    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(stmt.getLValue()),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);

                // 和A4中处理一样
                if(callGraph.getCalleesOf(stmt).contains(method))return null;

                Edge call = new Edge<>(CallGraphs.getCallKind(stmt),stmt,method);
                callGraph.addEdge(call);
                addReachable(method);

                List<Var> args = stmt.getInvokeExp().getArgs();
                List<Var> params = method.getIR().getParams();
                for (int i=0; i<args.size(); i++) {
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(args.get(i)),
                            pointerFlowGraph.getVarPtr(params.get(i))
                    );
                }

                List<Var> vars = method.getIR().getReturnVars();
                if(stmt.getLValue() != null){
                    for (Var var : vars) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(var),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if(pointerFlowGraph.getSuccsOf(source).contains(target)) return;
        pointerFlowGraph.addEdge(source,target);
        Set<Pointer> pointers = pointerFlowGraph.getPointers();
        for(Pointer pointer: pointers){
            if(pointer == source && !pointer.getPointsToSet().isEmpty())
                workList.addEntry(target, pointer.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if(!(entry.pointer() instanceof VarPtr))continue;
            Var var = ((VarPtr) entry.pointer()).getVar();

            for(Obj obj : delta){
                List<StoreField> SF = var.getStoreFields();
                for(StoreField sf: SF)addPFGEdge(
                        pointerFlowGraph.getVarPtr(sf.getRValue()),
                        pointerFlowGraph.getInstanceField(obj, sf.getFieldRef().resolve())
                );

                List<StoreArray> SA = var.getStoreArrays();
                for(StoreArray sa: SA)addPFGEdge(
                        pointerFlowGraph.getVarPtr(sa.getRValue()),
                        pointerFlowGraph.getArrayIndex(obj)
                );

                List<LoadField> LF = var.getLoadFields();
                for(LoadField lf: LF)addPFGEdge(
                        pointerFlowGraph.getInstanceField(obj, lf.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(lf.getLValue())
                );

                List<LoadArray> LA = var.getLoadArrays();
                for(LoadArray la: LA)addPFGEdge(
                        pointerFlowGraph.getArrayIndex(obj),
                        pointerFlowGraph.getVarPtr(la.getLValue())
                );

                processCall(var,obj);
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        PointsToSet pset = pointer.getPointsToSet();
        if(!pointsToSet.isEmpty()){
            Set<Obj> objs = pointsToSet.getObjects();
            for(Obj obj : objs){
                if(pset.contains(obj))continue;
                pset.addObject(obj);
                delta.addObject(obj);
            }
        }
        if(!delta.isEmpty()){
            Set<Pointer> succptrs = pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer succptr:succptrs){
                workList.addEntry(succptr,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        List<Invoke> callsites = var.getInvokes();
        for(Invoke callsite : callsites){
            JMethod method = resolveCallee(recv, callsite);
            Var newvar = method.getIR().getThis();
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(newvar),
                    new PointsToSet(recv)
            );

            if(callGraph.getCalleesOf(callsite).contains(method))continue;

            Edge call = new Edge(CallGraphs.getCallKind(callsite), callsite, method);
            callGraph.addEdge(call);
            addReachable(method);

            List<Var> args = callsite.getInvokeExp().getArgs();
            List<Var> params = method.getIR().getParams();

            for(int i = 0; i < args.size(); ++i){
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(args.get(i)),
                        pointerFlowGraph.getVarPtr(params.get(i))
                );
            }

            List<Var> rvars = method.getIR().getReturnVars();
            Var lv = callsite.getLValue();
            if(lv!=null){
                for(Var rvar: rvars)addPFGEdge(
                        pointerFlowGraph.getVarPtr(rvar),
                        pointerFlowGraph.getVarPtr(lv)
                );
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
