/*
 * Copyright (C) 2014 falk.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
 */

package de.learnlib.ralib.theory.equality;

import de.learnlib.ralib.automata.guards.DataExpression;
import de.learnlib.ralib.automata.guards.IfGuard;
import de.learnlib.ralib.data.SymbolicDataValue;
import de.learnlib.ralib.data.SymbolicDataValue.SuffixValue;
import de.learnlib.ralib.data.SymbolicDataValue.Register;
import de.learnlib.ralib.theory.Relation;
import de.learnlib.ralib.theory.SDTIfGuard;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Map;

/**
 *
 * @author falk
 */
public class EqualityGuard extends SDTIfGuard {
    
    public EqualityGuard(SuffixValue param, Register reg) {
        super(param, reg, Relation.EQUALS);
    }
    
//    @Override
//    public Equality createCopy(VarMapping renaming) {
//        return new Equality(this.getParameter(), renaming.get(this.getRegister()));
//    }
    
   
    @Override
    public String toString() {
//        String ret = "";
//        for (Register reg : this.getRegisters()) {
//            ret = ret + " " + this.getParameter() + "=" + reg;
//        }
//        return ret;
//        //}
        return "(" + this.getParameter().toString() + "=" + this.getRegister().toString() + ")";
        
    }
    
//    private List<Expression<Boolean>> toExprList() {
//        List<Expression<Boolean>> eqs = new ArrayList<>();
//        Variable p = new Variable(BuiltinTypes.SINT32, "p");
//        for (Register reg : this.getRegisters()) {
//            String xname = "x" + reg.getId();
//            Variable x = new Variable(BuiltinTypes.SINT32, xname);
//            Expression<Boolean> expression = new 
//        NumericBooleanExpression(x, NumericComparator.EQ, p);
//            eqs.add(expression);
//        }
//        return eqs;
//    }
//    
//    private Expression<Boolean> toExpr(List<Expression<Boolean>> eqList, int i) {
//        if (eqList.size() == i+1) {
//            return eqList.get(i);
//        }
//        else {
//            return new PropositionalCompound(eqList.get(i), LogicalOperator.AND, toExpr(eqList,i+1));
//        }
//    }
    
    @Override
    public Expression<Boolean> toExpr() {
        String xname = "x" + this.getRegister().getId();
        String pname = "p" + this.getParameter().getId();
        Variable p = new Variable(BuiltinTypes.SINT32, pname);
        Variable x = new Variable(BuiltinTypes.SINT32,xname);
        return new NumericBooleanExpression(x, NumericComparator.EQ, p);
    }
    
    @Override
    public IfGuard toTG(Map<SymbolicDataValue, Variable> variables) {
        Expression<Boolean> expr = this.toExpr();
        DataExpression<Boolean> cond = new DataExpression<>(expr, variables);
        return new IfGuard(cond);
                
                }
    
}