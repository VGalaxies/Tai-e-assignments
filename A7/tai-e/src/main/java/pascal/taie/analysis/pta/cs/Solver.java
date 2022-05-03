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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(new StmtProcessor(csMethod));
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

        @Override
        public Void visit(New stmt) {
            Context objContext = contextSelector.selectHeapContext(csMethod, null); // note
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(
                            csManager.getCSObj(objContext, heapModel.getObj(stmt)))
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
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(field)
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(
                        csManager.getStaticField(field),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                InvokeExp invokeExp = stmt.getInvokeExp(); // arg
                JMethod method = stmt.getMethodRef().resolve();
                IR ir = method.getIR(); // param
                assert invokeExp.getArgCount() == method.getParamCount();

                CSCallSite callSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(callSite, null);

                if (callGraph.addEdge(new Edge<>(
                        CallGraphs.getCallKind(stmt), callSite,
                        csManager.getCSMethod(calleeContext, method)))) {
                    addReachable(csManager.getCSMethod(calleeContext, method)); // note

                    for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                        addPFGEdge(
                                csManager.getCSVar(context, invokeExp.getArg(i)),
                                csManager.getCSVar(calleeContext, ir.getParam(i))
                        );
                    }

                    if (stmt.getLValue() != null) {
                        for (Var ret : ir.getReturnVars()) {
                            addPFGEdge(
                                    csManager.getCSVar(calleeContext, ret),
                                    csManager.getCSVar(context, stmt.getLValue())
                            );
                        }
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
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof CSVar csVar) {
                for (CSObj obj : delta) {
                    Var var = csVar.getVar();

                    for (StoreField storeField : var.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), storeField.getRValue()),
                                csManager.getInstanceField(obj, field)
                        );
                    }

                    for (LoadField loadField : var.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        addPFGEdge(
                                csManager.getInstanceField(obj, field),
                                csManager.getCSVar(csVar.getContext(), loadField.getLValue())
                        );
                    }

                    for (StoreArray storeArray : var.getStoreArrays()) {
                        // storeArray unused
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }

                    for (LoadArray loadArray : var.getLoadArrays()) {
                        // loadArray unused
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(csVar.getContext(), loadArray.getLValue())
                        );
                    }

                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet.getObjects()) {
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }

        if (!delta.isEmpty()) {
            for (CSObj obj : delta) {
                pointer.getPointsToSet().addObject(obj);
            }
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
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
        for (Invoke invoke : recv.getVar().getInvokes()) {
            JMethod method = resolveCallee(recvObj, invoke);
            CSCallSite callSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context calleeContext = contextSelector.selectContext(callSite, recvObj, null);

            workList.addEntry(
                    csManager.getCSVar(calleeContext, method.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            if (callGraph.addEdge(new Edge<>(
                    CallGraphs.getCallKind(invoke), callSite,
                    csManager.getCSMethod(calleeContext, method)))) {
                addReachable(csManager.getCSMethod(calleeContext, method));

                InvokeExp invokeExp = invoke.getInvokeExp(); // arg
                IR ir = method.getIR(); // param
                assert invokeExp.getArgCount() == method.getParamCount();

                for (int i = 0 ; i < invokeExp.getArgCount(); ++i) {
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), invokeExp.getArg(i)),
                            csManager.getCSVar(calleeContext, ir.getParam(i))
                    );
                }

                if (invoke.getLValue() != null) {
                    for (Var ret : ir.getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, ret),
                                csManager.getCSVar(recv.getContext(), invoke.getLValue())
                        );
                    }
                }
            }
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

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
