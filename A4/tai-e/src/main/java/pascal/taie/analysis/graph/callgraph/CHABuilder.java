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
import pascal.taie.ir.stmt.Invoke;
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
        // TODO - finish me
        LinkedList<JMethod> workList = new LinkedList<>();
        workList.addLast(entry);
        while (!workList.isEmpty()) {
            JMethod curr = workList.pollFirst();
            if (!callGraph.contains(curr)) {
                callGraph.addReachableMethod(curr);
                for (Invoke callSite : callGraph.getCallSitesIn(curr)) {
                    for (JMethod target : resolve(callSite)) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                                callSite, target));
                        workList.addLast(target);
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
        // TODO - finish me
        Set<JMethod> jMethodSet = new HashSet<>();
        if (callSite.isStatic()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            jMethodSet.add(jClass.getDeclaredMethod(subsignature));
        } else if (callSite.isSpecial()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            jMethodSet.add(dispatch(jClass, subsignature));
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
             LinkedList<JClass> workList = new LinkedList<>();
            workList.addLast(jClass);
            while (!workList.isEmpty()) {
                JClass curr = workList.pollFirst();
                JMethod method = dispatch(curr, subsignature);
                if (method != null) {
                    jMethodSet.add(method);
                }
                if (curr.isInterface()) { // interface
                    for (JClass sub : hierarchy.getDirectSubinterfacesOf(curr)) {
                        workList.addLast(sub);
                    }
                    for (JClass sub : hierarchy.getDirectImplementorsOf(curr)) {
                        workList.addLast(sub);
                    }
                } else { // class
                    for (JClass sub : hierarchy.getDirectSubclassesOf(curr)) {
                        workList.addLast(sub);
                    }
                }
            }
        }
        return jMethodSet;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        }

        JClass superClass = jclass.getSuperClass();
        if (superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}
