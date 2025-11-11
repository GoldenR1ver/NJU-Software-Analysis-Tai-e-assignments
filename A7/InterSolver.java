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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        this.workList = new ArrayDeque<>();
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        // 直接照搬A4
        List<Node> entry = icfg.entryMethods().map(icfg::getEntryOf).toList();
        for (Node node : icfg) {
            if(entry.contains(node)) {
                result.setOutFact(node, analysis.newBoundaryFact(node));
            } else {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        // TODO - finish me
        workList.addAll(icfg.getNodes());
        List<Node> entry = icfg.entryMethods().map(icfg::getEntryOf).toList();
        while(!workList.isEmpty()) {
            Node node = workList.poll();
            if (!entry.contains(node)){
                // 迭代函数状态转移公式
                Fact infact = result.getInFact(node), outfact = result.getOutFact(node);
                Set<ICFGEdge<Node>> inEdges = icfg.getInEdgesOf(node);
                for (ICFGEdge<Node> edge : inEdges) {
                    Fact ofact = result.getOutFact(edge.getSource());
                    Fact gfact = analysis.transferEdge(edge, ofact);
                    analysis.meetInto(gfact, infact);
                }
                result.setInFact(node, infact);

                // 是否有变化，有变化添加所有OUT边
                boolean tmp  = analysis.transferNode(node, infact, outfact);
                result.setOutFact(node, outfact);
                if(tmp){
                    for (ICFGEdge<Node> outEdge : icfg.getOutEdgesOf(node)) {
                        Node target = outEdge.getTarget();
                        if (!workList.contains(target)) {
                            workList.add(target);
                        }
                    }
                }
            }
        }
    }

    //添加的函数
    private boolean isEntryMethodEntry(Node node) {
        for (Method method : icfg.entryMethods().toList()) {
            if (icfg.getEntryOf(method).equals(node)) {
                return true;
            }
        }
        return false;
    }

    public DataflowResult<Node, Fact> getResult() {
        return this.result;
    }
    public void addWorkList(Node node){
        workList.add(node);
    }
}
