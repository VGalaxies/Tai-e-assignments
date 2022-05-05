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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

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
    }

    // TODO - finish me

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public void processSource(JMethod method, Type type, Invoke invoke, Context context) {
        for (Source source : config.getSources()) {
            if (source.method() == method && source.type() == type) {
                CSObj csObj = csManager.getCSObj(
                        emptyContext,
                        manager.makeTaint(invoke, type)
                );
                CSVar csVar = csManager.getCSVar(context, invoke.getLValue());
                if (!solver.getResult().getPointsToSet(csVar).contains(csObj)) {
                    solver.addEntry(csVar, PointsToSetFactory.make(csObj));
                }
            }
        }
    }

    public void processBaseToResult(JMethod method, Type type, CSVar base, Invoke invoke) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method() == method &&
                transfer.from() == TaintTransfer.BASE &&
                transfer.to() == TaintTransfer.RESULT &&
                transfer.type() == type) {
                for (CSObj csObj : solver.getResult().getPointsToSet(base)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)
//                            && obj.getType() == base.getType()
                    ) {
                        CSObj taintObj = csManager.getCSObj(
                                emptyContext,
                                manager.makeTaint(
                                        manager.getSourceCall(obj), // not invoke
                                        type
                                )
                        );
                        CSVar csVar = csManager.getCSVar(base.getContext(), invoke.getLValue());
                        if (!solver.getResult().getPointsToSet(csVar).contains(taintObj)) {
                            solver.addEntry(csVar, PointsToSetFactory.make(taintObj));
                        }
                    }
                }
            }
        }
    }

    public void processArgToBase(JMethod method, Type type, CSVar base, CSVar arg, int index) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method() == method &&
                transfer.from() == index &&
                transfer.to() == TaintTransfer.BASE &&
                transfer.type() == type) {
                for (CSObj csObj : solver.getResult().getPointsToSet(arg)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)
//                            && obj.getType() == arg.getType()
                    ) {
                        CSObj taintObj = csManager.getCSObj(
                                emptyContext,
                                manager.makeTaint(
                                        manager.getSourceCall(obj), // same
                                        type
                                )
                        );
                        if (!solver.getResult().getPointsToSet(base).contains(taintObj)) {
                            solver.addEntry(base, PointsToSetFactory.make(taintObj));
                        }
                    }
                }
            }
        }
    }

    public void processArgToResult(JMethod method, Type type, Invoke invoke, CSVar arg, int index, Context context) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method() == method &&
                transfer.from() == index &&
                transfer.to() == TaintTransfer.RESULT &&
                transfer.type() == type) {
                for (CSObj csObj : solver.getResult().getPointsToSet(arg)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)
//                            && obj.getType() == arg.getType()
                    ) {
                        CSObj taintObj = csManager.getCSObj(
                                emptyContext,
                                manager.makeTaint(
                                        manager.getSourceCall(obj), // same
                                        type
                                )
                        );
                        CSVar csVar = csManager.getCSVar(context, invoke.getLValue());
                        if (!solver.getResult().getPointsToSet(csVar).contains(taintObj)) {
                            solver.addEntry(csVar, PointsToSetFactory.make(taintObj));
                        }
                    }
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
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        for (Edge<?, ?> edge : result.getCSCallGraph().edges().toList()) {
            CSCallSite callSite = (CSCallSite) edge.getCallSite();
            InvokeExp invoke = callSite.getCallSite().getInvokeExp();
            CSMethod method = (CSMethod) edge.getCallee();
            for (Sink sink : config.getSinks()) {
                if (sink.method() == method.getMethod()) {
                    assert sink.index() < invoke.getArgCount();
                    Var targetArg = invoke.getArg(sink.index());
                    for (CSObj csObj : result.getPointsToSet(
                            csManager.getCSVar(callSite.getContext(), targetArg))) {
                        Obj obj = csObj.getObject();;
                        if (manager.isTaint(obj)
//                                && obj.getType() == targetArg.getType()
                        ) {
                            TaintFlow taintFlow = new TaintFlow(
                                    manager.getSourceCall(obj),
                                    callSite.getCallSite(),
                                    sink.index());
                            taintFlows.add(taintFlow);
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
}
