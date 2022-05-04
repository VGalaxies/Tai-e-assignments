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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    private boolean isIntersectBase(Var lhs, Var rhs) {
        Set<Obj> set = new HashSet<>(pta.getPointsToSet(lhs));
        set.retainAll(pta.getPointsToSet(rhs));
        return !set.isEmpty();
    }

    private boolean isIntersectIndex(Value lhs, Value rhs) {
        if (lhs.isUndef() || rhs.isUndef()) {
            return false;
        }
        if (lhs.isConstant() && rhs.isConstant()) {
            return lhs.getConstant() == rhs.getConstant();
        }
        return true;
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        // e.g. a[i] = x
        if (stmt instanceof StoreArray storeArray) {
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            Var base = arrayAccess.getBase();
            Var indexStore = arrayAccess.getIndex();
            CPFact factStore = this.solver.getResult().getOutFact(storeArray);

            for (Var var : pta.getVars()) {
                if (isIntersectBase(base, var)) {
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        Var indexLoad = loadArray.getArrayAccess().getIndex();
                        CPFact factLoad = this.solver.getResult().getOutFact(loadArray);
                        if (isIntersectIndex(factStore.get(indexStore), factLoad.get(indexLoad)) ||
                            isIntersectIndex(in.get(indexStore), factLoad.get(indexLoad))) { // note
                            this.solver.addWorkList(loadArray);
                        }
                    }
                }
            }
        }

        // e.g. x = a[i]
        if (stmt instanceof LoadArray loadArray) {
            ArrayAccess arrayAccess = loadArray.getArrayAccess();
            Var base = arrayAccess.getBase();
            Var indexLoad = arrayAccess.getIndex();
            CPFact factLoad = this.solver.getResult().getOutFact(loadArray);

            Value value = Value.getUndef();
            for (Var var : pta.getVars()) {
                if (isIntersectBase(base, var)) {
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        Var indexStore = storeArray.getArrayAccess().getIndex();
                        CPFact factStore = this.solver.getResult().getOutFact(storeArray);
                        if (isIntersectIndex(factStore.get(indexStore), factLoad.get(indexLoad)) ||
                            isIntersectIndex(factStore.get(indexStore), in.get(indexLoad))) { // note
                            value = cp.meetValue(value, factStore.get(storeArray.getRValue()));
                        }
                    }
                }
            }

            // do not call intra-transferNode
            CPFact prev_out = out.copy();
            out.copyFrom(in);
            out.update(loadArray.getLValue(), value);
            CPFact curr_out = out.copy();
            return !curr_out.equals(prev_out);
        }

        // e.g. T.f = x
        if (stmt instanceof StoreField storeField && storeField.isStatic()) {
            FieldAccess fieldAccess = storeField.getFieldAccess();
            assert fieldAccess instanceof StaticFieldAccess;

            JField field = fieldAccess.getFieldRef().resolve();
            JClass jClass = fieldAccess.getFieldRef().getDeclaringClass();

            for (Stmt load : icfg) {
                if (load instanceof LoadField loadField &&
                    loadField.isStatic() &&
                    loadField.getFieldRef().resolve() == field &&
                    loadField.getFieldRef().getDeclaringClass() == jClass) {
                    this.solver.addWorkList(loadField);
                }
            }
        }

        // e.g. x = T.f
        if (stmt instanceof LoadField loadField && loadField.isStatic()) {
            FieldAccess fieldAccess = loadField.getFieldAccess();
            assert fieldAccess instanceof StaticFieldAccess;

            JField field = fieldAccess.getFieldRef().resolve();
            JClass jClass = fieldAccess.getFieldRef().getDeclaringClass();

            Value value = Value.getUndef();
            for (Stmt store : icfg) {
                if (store instanceof StoreField storeField &&
                    storeField.isStatic() &&
                    storeField.getFieldRef().resolve() == field &&
                    storeField.getFieldRef().getDeclaringClass() == jClass) {
                    CPFact fact = this.solver.getResult().getOutFact(storeField);
                    value = cp.meetValue(value, fact.get(storeField.getRValue()));
                }
            }

            // do not call intra-transferNode
            CPFact prev_out = out.copy();
            out.copyFrom(in);
            out.update(loadField.getLValue(), value);
            CPFact curr_out = out.copy();
            return !curr_out.equals(prev_out);
        }

        // e.g. o.f = x
        if (stmt instanceof StoreField storeField && !storeField.isStatic()) {
            FieldAccess fieldAccess = storeField.getFieldAccess();
            assert fieldAccess instanceof InstanceFieldAccess;

            Var base = ((InstanceFieldAccess) fieldAccess).getBase();
            JField field = fieldAccess.getFieldRef().resolve();

            for (Var var : pta.getVars()) {
                if (isIntersectBase(base, var)) {
                    for (LoadField loadField : var.getLoadFields()) {
                        if (!loadField.isStatic() &&
                             loadField.getFieldRef().resolve() == field) {
                            this.solver.addWorkList(loadField);
                        }
                    }
                }
            }
        }

        // e.g. x = o.f
        if (stmt instanceof LoadField loadField && !loadField.isStatic()) {
            FieldAccess fieldAccess = loadField.getFieldAccess();
            assert fieldAccess instanceof InstanceFieldAccess;

            Var base = ((InstanceFieldAccess) fieldAccess).getBase();
            JField field = fieldAccess.getFieldRef().resolve();

            Value value = Value.getUndef();
            for (Var var : pta.getVars()) {
                if (isIntersectBase(base, var)) {
                    for (StoreField storeField : var.getStoreFields()) {
                        if (!storeField.isStatic() &&
                             storeField.getFieldRef().resolve() == field) {
                            CPFact fact = this.solver.getResult().getOutFact(storeField);
                            value = cp.meetValue(value, fact.get(storeField.getRValue()));
                        }
                    }
                }
            }

            // do not call intra-transferNode
            CPFact prev_out = out.copy();
            out.copyFrom(in);
            out.update(loadField.getLValue(), value);
            CPFact curr_out = out.copy();
            return !curr_out.equals(prev_out);
        }

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact res = out.copy();

        Stmt src = edge.getSource();
        assert src instanceof Invoke;

        Optional<LValue> _def = src.getDef();
        if (_def.isPresent()) {
            LValue def = _def.get();
            if (def instanceof Var) {
                res.update((Var) def, Value.getUndef()); // kill
            }
        }

        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact res = new CPFact();

        assert edge.getSource() instanceof Invoke;
        Invoke srcStmt = (Invoke) edge.getSource();
        InvokeExp srcExp = srcStmt.getInvokeExp();

        JMethod callee = edge.getCallee();
        List<Var> params = callee.getIR().getParams();
        assert params.size() == srcExp.getArgCount();

        for (int i = 0 ; i < params.size(); ++i) {
            Var param = params.get(i);
            Var arg = srcExp.getArg(i);
            res.update(param, callSiteOut.get(arg));
        }

        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact res = new CPFact();

        Stmt callStmt = edge.getCallSite();
        assert callStmt instanceof Invoke;

        Optional<LValue> _def = callStmt.getDef();
        if (_def.isPresent()) {
            LValue def = _def.get();
            if (def instanceof Var) {
                Value value = Value.getUndef();
                for (Var var : edge.getReturnVars()) {
                    value = cp.meetValue(value, returnOut.get(var));
                }
                res.update((Var) def, value);
            }
        }

        return res;
    }
}
