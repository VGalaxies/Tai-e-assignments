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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        unreachable(deadCode, cfg, constants);
        deadAssignment(deadCode, cfg, liveVars);
        return deadCode;
    }

    private static void unreachable(Set<Stmt> res, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set<Stmt> dead = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg) {
            if (stmt != cfg.getEntry() && stmt != cfg.getExit()) {
                dead.add(stmt); // init all
            }
        }

        LinkedList<Stmt> list = new LinkedList<>();
        Stmt entry = cfg.getEntry();
        list.addLast(entry);
        dead.remove(entry);

        while (!list.isEmpty()) {
            Stmt stmt = list.pollFirst();

            if (stmt instanceof If) {
                If ifStmt = (If) stmt;
                CPFact inFact = constants.getInFact(ifStmt);
                Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), inFact);

                boolean cond;
                if (value.isConstant()) {
                    if (value.getConstant() == 1) {
                        cond = true;
                    } else {
                        cond = false;
                    }

                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt)) {
                        if ((cond && edge.getKind() == Edge.Kind.IF_TRUE)
                                || (!cond && edge.getKind() == Edge.Kind.IF_FALSE)) {
                            Stmt succ = edge.getTarget();
                            if (dead.contains(succ)) {
                                list.addLast(succ);
                                dead.remove(succ);
                            }
                        }
                    }
                    continue;
                } else {
                    // fall through
                }
            }

            if (stmt instanceof SwitchStmt) {
                SwitchStmt switchStmt = (SwitchStmt) stmt;
                CPFact inFact = constants.getInFact(switchStmt);
                Value value = ConstantPropagation.evaluate(switchStmt.getVar(), inFact);

                if (value.isConstant()) {
                    int val = value.getConstant();
                    boolean hit = false;
                    for (Pair<Integer, Stmt> caseTarget : switchStmt.getCaseTargets()) {
                        if (val == caseTarget.first()) {
                            hit = true;
                            Stmt target = caseTarget.second();

                            // no need to consider fall through
                            if (dead.contains(target)) {
                                list.addLast(target);
                                dead.remove(target);
                            }

                        }
                    }

                    if (!hit) {
                        Stmt target = switchStmt.getDefaultTarget();
                        if (dead.contains(target)) {
                            list.addLast(target);
                            dead.remove(target);
                        }
                    }

                    continue;
                } else {
                    // fall through
                }
            }

            for (Stmt succ : cfg.getSuccsOf(stmt)) {
                if (dead.contains(succ)) {
                    list.addLast(succ);
                    dead.remove(succ);
                }
            }
        }

        res.addAll(dead);
    }

    private static void deadAssignment(Set<Stmt> res, CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set<Stmt> dead = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg) {
            if (stmt != cfg.getEntry() && stmt != cfg.getExit() && !res.contains(stmt)) {
                dead.add(stmt); // init all without unreachable
            }
        }

        Set<Stmt> list = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        for (Stmt stmt : dead) {
            if (stmt instanceof AssignStmt) {
                AssignStmt assignStmt = (AssignStmt) stmt;
                SetFact<Var> outFact = liveVars.getOutFact(stmt);

                Optional<LValue> _def = stmt.getDef();
                if (_def.isPresent()) {
                    if (_def.get() instanceof Var) {
                        Var def = (Var) _def.get();
                        if (!outFact.contains(def) && hasNoSideEffect(assignStmt.getRValue())) {
                            list.add(stmt);
                        }
                    }
                }
            }
        }

        res.addAll(list);
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}