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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final MultiMap<Pointer, Pointer> taintFlowGraph;
    private final List<Map.Entry<CSCallSite, Sink>> sinkCallSites;


    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        taintFlowGraph = Maps.newMultiMap();
        sinkCallSites = new ArrayList<>();
    }

    // TODO - finish me

    /**
     * Processes source method calls and creates tainted objects
     *
     * @param callSite The invocation site of the source method
     * @param m The source method being called
     * @return PointsToSet containing the created taint object, or null if not a source
     */
    public PointsToSet dealSource(Invoke callSite, JMethod m) {
        // Check if the method matches any configured source
        for (Source source : config.getSources()) {
            if (source.method().getSignature().equals(m.getSignature())) {
                // Create a taint object for the source call
                Obj taintObj = manager.makeTaint(callSite, m.getReturnType());
                // Return points-to set with the context-sensitive taint object
                return PointsToSetFactory.make(
                        csManager.getCSObj(emptyContext, taintObj));
            }
        }
        return null;
    }

    /**
     * Records sink call sites for later taint flow checking
     *
     * @param csCallSite The context-sensitive call site
     * @param jMethod The method being called at the sink
     */
    public void dealSinkCallSite(CSCallSite csCallSite, JMethod jMethod) {
        // Check if the method matches any configured sink
        for (Sink sink : config.getSinks()) {
            if (sink.method().getSignature().equals(jMethod.getSignature())) {
                // Store the sink call site with its corresponding sink
                sinkCallSites.add(new AbstractMap.SimpleEntry<>(csCallSite, sink));
            }
        }
    }

    /**
     * Adds a taint flow edge between source and target pointers
     *
     * @param source The source pointer in the taint flow
     * @param target The target pointer in the taint flow
     * @param type The type of the transferred value
     */
    private void addTFGEdge(Pointer source, Pointer target, Type type) {
        if (!taintFlowGraph.get(source).contains(target)) {
            taintFlowGraph.put(source, target);

            source.getPointsToSet().forEach(csObj -> {
                Obj obj = csObj.getObject();
                if (manager.isTaint(obj)) {
                    Invoke sourceCall = manager.getSourceCall(obj);
                    Obj propagatedTaint = manager.makeTaint(sourceCall, type);
                    solver.addWorkList(target,
                            PointsToSetFactory.make(
                                    csManager.getCSObj(emptyContext, propagatedTaint)));
                }
            });
        }
    }

    /**
     * Propagates taint information from a pointer to its successors
     *
     * @param pointer The pointer from which to propagate taint
     * @param pts The points-to set containing potential tainted objects
     * @return PointsToSet containing only the tainted objects
     */
    public PointsToSet propagate(Pointer pointer, PointsToSet pts) {
        PointsToSet taint = PointsToSetFactory.make();

        // Filter out only the tainted objects from the points-to set
        pts.objects()
                .filter(obj -> manager.isTaint(obj.getObject()))
                .forEach(taint::addObject);

        // If there are tainted objects, propagate them to successors
        if (!taint.isEmpty()) {
            taintFlowGraph.get(pointer).forEach(succPointer ->
                    solver.addWorkList(succPointer, taint));
        }

        return taint;
    }

    /**
     * Handles taint transfer operations at method calls
     *
     * @param csCallSite The context-sensitive call site
     * @param jMethod The method containing the transfer
     * @param baseP The base pointer (for instance method calls)
     */
    public void dealTaintTransfer(CSCallSite csCallSite, JMethod jMethod, CSVar baseP) {
        Context c = csCallSite.getContext();

        // Check for configured taint transfers
        for (TaintTransfer taintTransfer : config.getTransfers()) {
            if (taintTransfer.method().getSignature().equals(jMethod.getSignature())) {

                // Transfer from base to result (e.g., getter method)
                if (taintTransfer.from() == TaintTransfer.BASE &&
                        taintTransfer.to() == TaintTransfer.RESULT) {

                    Var lValue = csCallSite.getCallSite().getLValue();
                    addTFGEdge(baseP, csManager.getCSVar(c, lValue), jMethod.getReturnType());

                }
                // Transfer from argument to base (e.g., setter method)
                else if (taintTransfer.from() >= 0 &&
                        taintTransfer.to() == TaintTransfer.BASE) {

                    List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
                    CSVar argP = csManager.getCSVar(c, args.get(taintTransfer.from()));
                    addTFGEdge(argP, baseP, jMethod.getReturnType());

                }
                // Transfer from argument to result (e.g., transformation method)
                else if (taintTransfer.from() >= 0 &&
                        taintTransfer.to() == TaintTransfer.RESULT) {

                    List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
                    CSVar argP = csManager.getCSVar(c, args.get(taintTransfer.from()));
                    Var lValue = csCallSite.getCallSite().getLValue();
                    addTFGEdge(argP, csManager.getCSVar(c, lValue), jMethod.getReturnType());
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        // Check each recorded sink call site for taint flows
        sinkCallSites.forEach(entry -> {
            CSCallSite csCallSite = entry.getKey();
            Sink sink = entry.getValue();

            List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();

            // Get the points-to set for the sink argument
            CSVar sinkArgVar = csManager.getCSVar(csCallSite.getContext(), args.get(sink.index()));

            // Check each object in the points-to set
            for (CSObj obj : result.getPointsToSet(sinkArgVar)) {
                // If the object is tainted, record the taint flow
                if (manager.isTaint(obj.getObject())) {
                    taintFlows.add(new TaintFlow(
                            manager.getSourceCall(obj.getObject()),
                            csCallSite.getCallSite(),
                            sink.index()));
                }
            }
        });

        return taintFlows;
    }
}
