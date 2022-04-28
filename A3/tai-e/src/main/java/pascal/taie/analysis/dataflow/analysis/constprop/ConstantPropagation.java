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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact(); // use absence to represent UNDEF
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        Optional<LValue> _def = stmt.getDef();
        if (_def.isPresent()) {
            LValue def = _def.get();
            if (def instanceof Var && stmt instanceof DefinitionStmt) {
                CPFact prev_out = out.copy();
                out.copyFrom(in);
                DefinitionStmt<?, ?> definitionStmt = (DefinitionStmt<?, ?>) stmt;
                out.update((Var) def, evaluate(definitionStmt.getRValue(), in));
                CPFact curr_out = out.copy();
                return !curr_out.equals(prev_out);
            } else {
                return out.copyFrom(in); // identity function
            }
        } else {
            return out.copyFrom(in); // identity function
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            IntLiteral intLiteral = (IntLiteral) exp;
            // CPFact unused
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof Var) {
            Var var = (Var) exp;
            // e.g. y = 1; x = y;
            return in.get(var);
        } else if (exp instanceof BinaryExp) {
            BinaryExp binaryExp = (BinaryExp) exp;
            // recursive
            Value op1 = evaluate(binaryExp.getOperand1(), in);
            Value op2 = evaluate(binaryExp.getOperand2(), in);
            if (op1.isNAC() || op2.isNAC()) {
                return Value.getNAC();
            }
            if (op1.isConstant() && op2.isConstant()) {
                int op1Literal = op1.getConstant();
                int op2Literal = op2.getConstant();
                BinaryExp.Op op = binaryExp.getOperator();
                switch (op.toString()) {
                    case "+":
                        return Value.makeConstant(op1Literal + op2Literal);
                    case "-":
                        return Value.makeConstant(op1Literal - op2Literal);
                    case "*":
                        return Value.makeConstant(op1Literal * op2Literal);
                    case "/":
                        if (op2Literal == 0) {
                            return Value.getUndef();
                        }
                        return Value.makeConstant(op1Literal / op2Literal);
                    case "%":
                        if (op2Literal == 0) {
                            return Value.getUndef();
                        }
                        return Value.makeConstant(op1Literal % op2Literal);

                    case "|":
                        return Value.makeConstant(op1Literal | op2Literal);
                    case "&":
                        return Value.makeConstant(op1Literal & op2Literal);
                    case "^":
                        return Value.makeConstant(op1Literal ^ op2Literal);

                    case "==":
                        if (op1Literal == op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);
                    case "!=":
                        if (op1Literal != op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);
                    case "<":
                        if (op1Literal < op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);
                    case ">":
                        if (op1Literal > op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);
                    case "<=":
                        if (op1Literal <= op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);
                    case ">=":
                        if (op1Literal >= op2Literal)
                            return Value.makeConstant(1);
                        else
                            return Value.makeConstant(0);

                    case "<<":
                        return Value.makeConstant(op1Literal << op2Literal);
                    case ">>":
                        return Value.makeConstant(op1Literal >> op2Literal);
                    case ">>>":
                        return Value.makeConstant(op1Literal >>> op2Literal);

                }
            }
            return Value.getUndef(); // note
        }
        return Value.getNAC(); // note
    }
}

