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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        LinkedList<Node> list = new LinkedList<>();
        for (Node node : cfg) {
            list.addLast(node);
        }

        while (!list.isEmpty()) {
            Node node = list.pollFirst();

            Fact node_in_fact = result.getInFact(node);
            for (Node pred : cfg.getPredsOf(node)) {
                Fact pred_fact = result.getOutFact(pred);
                analysis.meetInto(pred_fact, node_in_fact);
            }
            result.setInFact(node, node_in_fact);

            Fact node_out_fact = result.getOutFact(node);
            boolean changed = analysis.transferNode(node, node_in_fact, node_out_fact);
            result.setOutFact(node, node_out_fact);

            if (changed) {
                for (Node succ : cfg.getSuccsOf(node)) {
                    if (!list.contains(succ)) {
                        list.addLast(succ);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        LinkedList<Node> list = new LinkedList<>();
        for (Node node : cfg) {
            list.addLast(node);
        }

        while (!list.isEmpty()) {
            Node node = list.pollFirst();

            Fact node_out_fact = result.getOutFact(node);
            for (Node succ : cfg.getSuccsOf(node)) {
                Fact succ_fact = result.getInFact(succ);
                analysis.meetInto(succ_fact, node_out_fact);
            }
            result.setOutFact(node, node_out_fact);

            Fact node_in_fact = result.getInFact(node);
            boolean changed = analysis.transferNode(node, node_in_fact, node_out_fact);
            result.setInFact(node, node_in_fact);

            if (changed) {
                for (Node pred : cfg.getPredsOf(node)) {
                    if (!list.contains(pred)) {
                        list.addLast(pred);
                    }
                }
            }
        }
    }
}
