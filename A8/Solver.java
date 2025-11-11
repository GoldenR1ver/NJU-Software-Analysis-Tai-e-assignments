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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        // 完全照抄A6
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            List<Stmt> stmts = csMethod.getMethod().getIR().getStmts();
            for(Stmt stmt: stmts){
                StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
                stmt.accept((stmtProcessor));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        // 完全照抄A6
        @Override
        public Void visit(New stmt){
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(heapContext,obj))
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }


        // 静态调用的污点分析
        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if(method == null)return null;

                CSCallSite csCallSite = csManager.getCSCallSite(context,stmt);
                Context csContext = contextSelector.selectContext(csCallSite, method);
                CSMethod csMethod = csManager.getCSMethod(csContext, method);


                if(callGraph.getCalleesOf(csCallSite).contains(csMethod))return null;

                Edge call = new Edge<>(CallGraphs.getCallKind(stmt),csCallSite,csMethod);
                callGraph.addEdge(call);
                addReachable(csMethod);

                List<Var> args = stmt.getInvokeExp().getArgs();
                List<Var> params = method.getIR().getParams();
                for (int i=0; i<args.size(); i++) {
                    addPFGEdge(
                            csManager.getCSVar(context, args.get(i)),
                            csManager.getCSVar(csContext, params.get(i))
                    );
                }

                List<Var> vars = method.getIR().getReturnVars();
                if(stmt.getLValue() != null){
                    for (Var var : vars) {
                        addPFGEdge(
                                csManager.getCSVar(csContext, var),
                                csManager.getCSVar(context,stmt.getLValue())
                        );
                    }
                    // 添加污点传播逻辑
                    if(stmt.getLValue() != null){
                        PointsToSet sourcePts = taintAnalysis.dealSource(stmt, method);
                        if(sourcePts != null) {
                            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), sourcePts);
                        }
                    }
                }

                // 污点分析部分
                taintAnalysis.dealTaintTransfer(csCallSite, method, null);
                taintAnalysis.dealSinkCallSite(csCallSite, method);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me

        if(pointerFlowGraph.getSuccsOf(source).contains(target)) return;
        pointerFlowGraph.addEdge(source,target);
        if(!source.getPointsToSet().isEmpty()) workList.addEntry(target, source.getPointsToSet());

    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me

        //完全复制自A6
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            // 添加污点传播逻辑
            PointsToSet taint = taintAnalysis.propagate(entry.pointer(), entry.pointsToSet());
            delta.addAll(taint);
            if(!(entry.pointer() instanceof CSVar))continue;

            CSVar csPtr = (CSVar) entry.pointer();
            Var var = csPtr.getVar();
            Context csContext = csPtr.getContext();

            for(CSObj obj : delta){
                List<StoreField> SF = var.getStoreFields();
                for(StoreField sf: SF)addPFGEdge(
                        csManager.getCSVar(csContext, sf.getRValue()),
                        csManager.getInstanceField(obj, sf.getFieldRef().resolve())
                );

                List<StoreArray> SA = var.getStoreArrays();
                for(StoreArray sa: SA)addPFGEdge(
                        csManager.getCSVar(csContext,sa.getRValue()),
                        csManager.getArrayIndex(obj)
                );

                List<LoadField> LF = var.getLoadFields();
                for(LoadField lf: LF)addPFGEdge(
                        csManager.getInstanceField(obj, lf.getFieldRef().resolve()),
                        csManager.getCSVar(csContext, lf.getLValue())
                );

                List<LoadArray> LA = var.getLoadArrays();
                for(LoadArray la: LA)addPFGEdge(
                        csManager.getArrayIndex(obj),
                        csManager.getCSVar(csContext,la.getLValue())
                );

                processCall(csPtr,obj);
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // 使用工厂模式
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet pset = pointer.getPointsToSet();
        if(!pointsToSet.isEmpty()){
            Set<CSObj> objs = pointsToSet.getObjects();
            for(CSObj obj : objs){
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me

        Var var = recv.getVar();
        Context context = recv.getContext();

        List<Invoke> callsites = var.getInvokes();
        for(Invoke callsite : callsites){
            JMethod method = resolveCallee(recvObj, callsite);

            CSCallSite csCallSite = csManager.getCSCallSite(context,callsite);
            Context csContext = contextSelector.selectContext(csCallSite,recvObj,method);
            CSMethod csMethod = csManager.getCSMethod(csContext,method);


            if(callGraph.getCalleesOf(csCallSite).contains(csMethod))continue;

            // 这个在重复检查之后执行
            CSVar csPtr = csManager.getCSVar(context, method.getIR().getThis());
            Var csVar = csPtr.getVar();
            workList.addEntry(
                    csPtr,
                    PointsToSetFactory.make(recvObj)
            );



            Edge call = new Edge(CallGraphs.getCallKind(callsite), csCallSite, csMethod);
            callGraph.addEdge(call);
            addReachable(csMethod);

            List<Var> args = callsite.getInvokeExp().getArgs();
            List<Var> params = method.getIR().getParams();

            for(int i = 0; i < args.size(); ++i){
                addPFGEdge(
                        csManager.getCSVar(context,args.get(i)),
                        csManager.getCSVar(csContext,params.get(i))
                );
            }

            List<Var> rvars = method.getIR().getReturnVars();
            Var lv = callsite.getLValue();
            if(lv!=null){
                for(Var rvar: rvars)addPFGEdge(
                        csManager.getCSVar(csContext,rvar),
                        csManager.getCSVar(context,lv)
                );
            }

            // 添加污点传播逻辑
            if(lv != null){
                PointsToSet sourcePts = taintAnalysis.dealSource(callsite, method);
                if(sourcePts != null) {
                    workList.addEntry(csManager.getCSVar(context, lv), sourcePts);
                }
            }


            taintAnalysis.dealTaintTransfer(csCallSite, method, recv);
            taintAnalysis.dealSinkCallSite(csCallSite, method);
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        // 得判断是否是null（虽然不知道哪里处了问题）
        if (result == null) {result = new PointerAnalysisResultImpl(csManager, callGraph);}
        return result;
    }

    public void addWorkList(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }



}
