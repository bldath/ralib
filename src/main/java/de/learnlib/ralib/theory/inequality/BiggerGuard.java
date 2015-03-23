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

package de.learnlib.ralib.theory.inequality;

import de.learnlib.ralib.automata.guards.DataExpression;
import de.learnlib.ralib.automata.guards.IfGuard;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.DataValue;
import de.learnlib.ralib.data.SymbolicDataValue;
import de.learnlib.ralib.data.SymbolicDataValue.SuffixValue;
import de.learnlib.ralib.data.VarMapping;
import de.learnlib.ralib.theory.Relation;
import de.learnlib.ralib.theory.SDTIfGuard;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Map;
import java.util.Objects;

/**
 *
 * @author falk
 */
public class BiggerGuard extends SDTIfGuard {
    
    public BiggerGuard(SuffixValue param, SymbolicDataValue reg) {
        super(param,reg,Relation.BIGGER);
    }
    
    @Override
    public SmallerGuard toDeqGuard() {
        return new SmallerGuard(parameter,register);
    }
   
    @Override
    public String toString() {
        return "(" + this.getParameter().toString() + ">" + this.getRegister().toString() + ")";
        //
        //return super.toString();
    }
    
    @Override
    public Expression<Boolean> toExpr(Constants consts) {
        SymbolicDataValue r = this.getRegister();
       //  String pname = "y" + this.getParameter().getId();
        Variable p = this.getParameter().toVariable(); //new Variable(BuiltinTypes.SINT32, pname);
        
        if (r.isConstant()) {
            DataValue<Integer> dv = (DataValue<Integer>) consts.get((SymbolicDataValue.Constant)r);
            Integer dv_i = dv.getId();
            gov.nasa.jpf.constraints.expressions.Constant c = new gov.nasa.jpf.constraints.expressions.Constant(BuiltinTypes.SINT32,dv_i);
            return new NumericBooleanExpression(c, NumericComparator.LT, p);
        }
        else {
//            String xname = "";
//            if (r instanceof SymbolicDataValue.Register) {
//            xname = "x" + r.getId();
//            }
//            else if (r instanceof SymbolicDataValue.SuffixValue) {
//            xname = "y" + r.getId();
    //        }
        //Variable x = new Variable(BuiltinTypes.SINT32,xname);
        Variable x = r.toVariable();
            return new NumericBooleanExpression(x, NumericComparator.LT, p);
        }
    } 
//    
//    
//
//    @Override
//    public Expression<Boolean> toExpr(Constants consts) {
//        String xname = "x" + this.getRegister().getId();
//        Variable p = new Variable(BuiltinTypes.SINT32, "y");
//        Variable x = new Variable(BuiltinTypes.SINT32,xname);
//        return new NumericBooleanExpression(x, NumericComparator.LT, p);
//    }    
    
    @Override
    public IfGuard toTG(Map<SymbolicDataValue, Variable> variables, Constants consts) {
        Expression<Boolean> expr = this.toExpr(consts);
        DataExpression<Boolean> cond = new DataExpression<>(expr, variables);
        return new IfGuard(cond);
    }
    
    public boolean contradicts(SDTIfGuard other) {
        boolean samePR = (this.getParameter().getId() == other.getParameter().getId() && 
                this.getRegister().getId() == other.getRegister().getId());
        return samePR && (other instanceof SmallerGuard);
    }

     @Override
    public SDTIfGuard relabel(VarMapping relabelling) {
        SymbolicDataValue.SuffixValue sv = (SymbolicDataValue.SuffixValue) relabelling.get(parameter);
        SymbolicDataValue r = null;
        sv = (sv == null) ? parameter : sv;
        
        if (register.isConstant()) {
            return new BiggerGuard(sv,register);
        }
        else {
            if (register.isSuffixValue()) {
            r = (SymbolicDataValue) relabelling.get(register);
            }
            else if (register.isRegister()) {
            r = (SymbolicDataValue.Register) relabelling.get(register);
            }
        r = (r == null) ? parameter : r;
        return new BiggerGuard(sv, r);
        }
    }
    
    @Override
    public SDTIfGuard relabelLoosely(VarMapping relabelling) {
        SymbolicDataValue.SuffixValue sv = (SymbolicDataValue.SuffixValue) relabelling.get(parameter);
        SymbolicDataValue r = null;
        sv = (sv == null) ? parameter : sv;
        
        if (register.isConstant()) {
            return new BiggerGuard(sv,register);
        }
        else {
            r = (SymbolicDataValue)relabelling.get(register);
            }
            
        r = (r == null) ? parameter : r;
        return new BiggerGuard(sv, r);
    }
    
    
    

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 59 * hash + Objects.hashCode(parameter);
        hash = 59 * hash + Objects.hashCode(register);
        hash = 59 * hash + Objects.hashCode(relation);
        hash = 59 * hash + Objects.hashCode(getClass());
        
        return hash;
    }
    
    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final BiggerGuard other = (BiggerGuard) obj;
        if (!Objects.equals(this.register, other.register)) {
            return false;
        }
        if (!Objects.equals(this.relation, other.relation)) {
            return false;
        }
        return Objects.equals(this.parameter, other.parameter);
    }

    
    
}
