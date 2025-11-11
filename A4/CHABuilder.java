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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);

        while(!worklist.isEmpty()){
            JMethod method = worklist.poll();
            if(!callGraph.reachableMethods.contains(method)){
                callGraph.addReachableMethod(method);

                List<Stmt> stmts = method.getIR().getStmts();
                for(Stmt stmt : stmts){
                    if(stmt instanceof Invoke){
                        Invoke callsite = (Invoke)stmt;
                        for(JMethod calledmethod : resolve(callsite)){
                            Edge call = new Edge(CallGraphs.getCallKind(callsite),callsite,calledmethod);
                            callGraph.addEdge(call);
                            if(!callGraph.reachableMethods.contains(calledmethod))worklist.add(calledmethod);
                        }
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> calledmethods = new HashSet<>();
        MethodRef methodref = callSite.getMethodRef();
        JClass declaringClass = methodref.getDeclaringClass();
        Subsignature subsignature = methodref.getSubsignature();
        CallKind callkind = CallGraphs.getCallKind(callSite);

        switch (callkind){
            case STATIC :
                calledmethods.add(declaringClass.getDeclaredMethod(subsignature));
                return calledmethods;
            case SPECIAL:
                JMethod dispatch = dispatch(declaringClass, subsignature);
                if(dispatch != null)calledmethods.add(dispatch);
                return calledmethods;
            case VIRTUAL:
            case INTERFACE:
                Set<JClass> subifaces = new HashSet<>();
                subifaces.add(declaringClass);
                Deque<JClass> stack = new ArrayDeque<>();
                stack.push(declaringClass);
                while(!stack.isEmpty()){
                    JClass currentiface = stack.pop();
                    Collection<JClass> direct = hierarchy.getDirectSubinterfacesOf(currentiface);
                    for(JClass subiface : direct){
                        if(subifaces.add(subiface)){
                            stack.push(subiface);
                        }
                    }
                }

                Set<JClass> impls = new HashSet<>(subifaces);
                Deque<JClass> stackImplementors = new ArrayDeque<>(subifaces);
                while (!stackImplementors.isEmpty()) {
                    JClass currentInterface = stackImplementors.pop();
                    Collection<JClass> directImplementors = hierarchy.getDirectImplementorsOf(currentInterface);
                    for (JClass implementor : directImplementors) {
                        if (impls.add(implementor)) {
                            stackImplementors.push(implementor);
                        }
                    }
                }

                Set<JClass> subclasses = new HashSet<>(impls);
                Deque<JClass> stackSubclasses = new ArrayDeque<>(impls);
                while (!stackSubclasses.isEmpty()) {
                    JClass currentClass = stackSubclasses.pop();
                    Collection<JClass> directSubclasses = hierarchy.getDirectSubclassesOf(currentClass);
                    for (JClass subclass : directSubclasses) {
                        if (subclasses.add(subclass)) {
                            stackSubclasses.push(subclass);
                        }
                    }
                }

                for (JClass subclass : subclasses) {
                    JMethod tmp = dispatch(subclass, subsignature);
                    if (tmp != null) {
                        calledmethods.add(tmp);
                    }
                }



        }
        return calledmethods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if(declaredMethod != null && !declaredMethod.isAbstract()) {
            return declaredMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if(superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}
