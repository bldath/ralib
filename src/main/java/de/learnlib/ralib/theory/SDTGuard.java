/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package de.learnlib.ralib.theory;

import de.learnlib.ralib.automata.TransitionGuard;
import de.learnlib.ralib.automata.guards.GuardExpression;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.SymbolicDataValue;
import de.learnlib.ralib.data.SymbolicDataValue.SuffixValue;
import de.learnlib.ralib.data.VarMapping;
import gov.nasa.jpf.constraints.api.Variable;
import java.util.Map;

/**
 *
 * @author falk
 */
public abstract class SDTGuard {
    
    //TODO: this should probably be a special sdtparameter
    protected final SuffixValue parameter;
    
    //TODO: this should be either a register or a special sdtregister
    //private final Register register;
    
//    private final Register register;
//    private final Relation relation;
//    
    
    public SuffixValue getParameter() {
        return this.parameter;
    }

//    public Register getRegister() {
//        return this.register;
//    }
    
    
    //public Map<Register, Relation> getRegsAndRels() {
    //    return this.regrels;
    //}
    
//    public Register getRegister() {
//        return this.register;        
//    }
    
//    public Relation getRelation() {
//        return this.relation;
//    }
    
    public SDTGuard(SuffixValue param) {
        
        this.parameter = param;
    
//        this.regrels = new LinkedHashMap<>();
//        this.parameter = param;
//        this.regrels.put(reg,rel);
    }
    
//    public Guard createCopy(VarMapping renaming) {
//        return this;
//    }
    
    
    
    
    
    //TODO: this method should not be in this class unless it applies to every kind of guard...
    // Fix this method for inequality
    

    
    /**
     * 
     * @param variables
     * @param consts
     * @return 
     */
    //public abstract Expression<Boolean> getGuardExpression(
    //        Map<SymbolicDataValue, Variable> variables);
    
    public TransitionGuard toTG() {
        return new TransitionGuard(this.toExpr());
    }
    
    public abstract GuardExpression toExpr();
    
    public abstract SDTGuard relabel(VarMapping relabelling);

    public abstract SDTGuard relabelLoosely(VarMapping relabelling);

}
