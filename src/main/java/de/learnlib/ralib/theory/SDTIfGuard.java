/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package de.learnlib.ralib.theory;

import de.learnlib.ralib.automata.TransitionGuard;
import de.learnlib.ralib.data.SymbolicDataValue;
import de.learnlib.ralib.data.SymbolicDataValue.*;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import java.util.Map;


public abstract class SDTIfGuard extends SDTGuard {
    
    private final Register register;
    private final Relation relation;
    
    
    public Register getRegister() {
        return this.register;
    }
    
    public Relation getRelation() {
    //    return regrels.get(reg);
        return this.relation;
    }
    
    public boolean equals(SDTIfGuard other) {
        return (this.getParameter() == other.getParameter() &&
                this.register == other.getRegister() &&
                this.relation == other.getRelation());
//                this.regrels == other.getRegsAndRels());
    }
    
    public SDTIfGuard(SuffixValue param, Register reg, Relation rel) {
        super(param);
        this.relation = rel;
        this.register = reg;
    }   
    
    @Override
    public abstract TransitionGuard toTG(Map<SymbolicDataValue, Variable> variables);
    
    @Override
    public abstract Expression<Boolean> toExpr();
            
}