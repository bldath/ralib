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
import de.learnlib.ralib.data.SymbolicDataValue.Register;
import de.learnlib.ralib.data.SymbolicDataValue.SuffixValue;
import de.learnlib.ralib.theory.Relation;
import de.learnlib.ralib.theory.SDTElseGuard;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
/**
 *
 * @author falk
 */
public class DisequalityGuard extends SDTElseGuard {
    
    public DisequalityGuard(SuffixValue param, Set<Register> regs) {
        super(param, regs, Relation.ELSE);     
    }
    
        private List<Expression<Boolean>> toExprList() {
        List<Expression<Boolean>> deqs = new ArrayList<>();
        String pname = "p" + this.getParameter().getId();
        Variable p = new Variable(BuiltinTypes.SINT32, pname);
        for (Register reg : this.getRegisters()) {
            String xname = "x" + reg.getId();
            Variable x = new Variable(BuiltinTypes.SINT32, xname);
            Expression<Boolean> expression = new 
        NumericBooleanExpression(x, NumericComparator.NE, p);
            deqs.add(expression);
        }
        return deqs;
    }
//    
    private Expression<Boolean> toExpr(List<Expression<Boolean>> deqList, int i) {
        if (deqList.size() == i+1) {
            return deqList.get(i);
        }
        else {
            return new PropositionalCompound(deqList.get(i), LogicalOperator.AND, toExpr(deqList,i+1));
        }
    }
    
    @Override
    public Expression<Boolean> toExpr() {
        return this.toExpr(this.toExprList(),0);
    }
    
    private List<IfGuard> toIfs(Set<Expression<Boolean>> ifExprs, Map<SymbolicDataValue, Variable> variables) {
        List<IfGuard> ifGuards = new ArrayList<>();
        for (Expression<Boolean> ifExpr : ifExprs) {
            DataExpression<Boolean> cond = new DataExpression<>(ifExpr, variables);
            ifGuards.add(new IfGuard(cond));
        }
        return ifGuards;
    }
        
    @Override
    public IfGuard toTG(Map<SymbolicDataValue, Variable> variables) {
        Expression<Boolean> expr = this.toExpr();
        DataExpression<Boolean> cond = new DataExpression<>(expr, variables);
        return new IfGuard(cond);
                
                }
    
    
    @Override
    public String toString() {
        return "ELSE[" + this.getParameter().toString() + "]";
    }
    
    public DisequalityGuard join(EqualityGuard e) {
        //System.out.println("e.param = " + e.getParameter().toString() + ", this.param = " + this.getParameter().toString());
        assert e.getParameter().equals(this.getParameter());
        return this;
    }
}