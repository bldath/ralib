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

package de.learnlib.ralib.learning;

import de.learnlib.logging.LearnLogger;
import de.learnlib.ralib.automata.Assignment;
import de.learnlib.ralib.automata.RALocation;
import de.learnlib.ralib.automata.Transition;
import de.learnlib.ralib.automata.TransitionGuard;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.PIV;
import de.learnlib.ralib.data.SymbolicDataValue.Parameter;
import de.learnlib.ralib.data.SymbolicDataValue.Register;
import de.learnlib.ralib.data.VarMapping;
import de.learnlib.ralib.oracles.Branching;
import de.learnlib.ralib.words.DataWords;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Level;
import net.automatalib.words.Word;

/**
 * Constructs Register Automata from observation tables
 * 
 * @author falk
 */
class AutomatonBuilder {
    
    private final Map<Word<PSymbolInstance>, Component> components;

    private final Map<Word<PSymbolInstance>, RALocation> locations = new LinkedHashMap<>();
    
    private final Hypothesis automaton;
    
    protected final Constants consts;
    
    private static LearnLogger log = LearnLogger.getLogger(AutomatonBuilder.class);
    
    AutomatonBuilder(Map<Word<PSymbolInstance>, Component> components, Constants consts) {
        this.consts = consts;
        this.components = components;
        this.automaton = new Hypothesis(consts);
    }

    Hypothesis toRegisterAutomaton() {
        log.fine("computing hypothesis");
        computeLocations();
        computeTransitions();
        return this.automaton;
    }
    
    private void computeLocations() {
        Component c = components.get(RaStar.EMPTY_PREFIX);      
        log.log(Level.FINER, "{0}", c);
        RALocation loc = this.automaton.addInitialState(c.isAccepting());
        this.locations.put(RaStar.EMPTY_PREFIX, loc);
        this.automaton.setAccessSequence(loc, RaStar.EMPTY_PREFIX);
                
        for (Entry<Word<PSymbolInstance>, Component> e : this.components.entrySet()) {
            if (!e.getKey().equals(RaStar.EMPTY_PREFIX)) {
                log.log(Level.FINER, "{0}", e.getValue());
                loc = this.automaton.addState(e.getValue().isAccepting());
                this.locations.put(e.getKey(), loc);
                this.automaton.setAccessSequence(loc, e.getKey());
            }
        }
    }
    
    private void computeTransitions() {
        for (Component c : components.values()) {
            computeTransition(c, c.getPrimeRow());
            for (Row r : c.getOtherRows()) {
                computeTransition(c, r);
            }
        }
    }

    
    private void computeTransition(Component dest_c, Row r) {        
        if (r.getPrefix().length() < 1) {
            return;
        }
        
        log.log(Level.FINER, "computing transition: {1} to {0}", new Object[]{dest_c, r});

        Word<PSymbolInstance> dest_id = dest_c.getAccessSequence();
        Word<PSymbolInstance> src_id = r.getPrefix().prefix(r.getPrefix().length() -1);        
        Component src_c = this.components.get(src_id);
        
        // locations
        RALocation src_loc = this.locations.get(src_id);
        RALocation dest_loc = this.locations.get(dest_id);
        
        // action
        ParameterizedSymbol action = r.getPrefix().lastSymbol().getBaseSymbol();
        
        // guard
        Branching b = src_c.getBranching(action);
        TransitionGuard guard = b.getBranches().get(r.getPrefix());
        
        // assignment
        VarMapping assignments = new VarMapping();
        int max = DataWords.paramLength(DataWords.actsOf(src_id));
        PIV parsInVars_Src = src_c.getPrimeRow().getParsInVars();
        PIV parsInVars_Row = r.getParsInVars();        
        VarMapping remapping = dest_c.getRemapping(r);
        
//        log.log(Level.FINEST,"PIV ROW:" + parsInVars_Row);
//        log.log(Level.FINEST,"PIV SRC:" + parsInVars_Src);
//        log.log(Level.FINEST,"REMAP: " + remapping);
        
        for (Entry<Parameter, Register> e : parsInVars_Row) {
            // param or register
            Parameter p = e.getKey();
            // remapping is null for prime rows ...
            Register rNew = (remapping == null) ? e.getValue() : (Register) remapping.get(e.getValue());
            if (p.getId() > max) {                
                Parameter pNew = new Parameter(p.getType(), p.getId() - max);
                assignments.put(rNew, pNew);
            } else {
                Register rOld = parsInVars_Src.get(p);
                assignments.put(rNew, rOld);
            }
        }
        Assignment assign = new Assignment(assignments);
                
        // create transition
        Transition  t = createTransition(action, guard, src_loc, dest_loc, assign);
        if (t != null) {
            log.log(Level.FINER, "computed transition {0}", t);
            this.automaton.addTransition(src_loc, action, t);
            this.automaton.setTransitionSequence(t, r.getPrefix());
        }
    }

    protected Transition createTransition(ParameterizedSymbol action, TransitionGuard guard, 
            RALocation src_loc, RALocation dest_loc, Assignment assign) {
        return new Transition(action, guard, src_loc, dest_loc, assign);
    }
    
    
}
