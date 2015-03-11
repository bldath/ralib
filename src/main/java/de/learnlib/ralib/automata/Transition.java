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

package de.learnlib.ralib.automata;

import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.ParValuation;
import de.learnlib.ralib.data.VarValuation;
import de.learnlib.ralib.words.ParameterizedSymbol;

/**
 * Register Automaton transitions have input symbols, and assignments.
 * 
 * @author falk
 */
public abstract class Transition {
       
    protected final ParameterizedSymbol label;

    protected final TransitionGuard guard;
     
    protected final RALocation source;
    
    protected final RALocation destination;

    protected final Assignment assignment;

    public Transition(ParameterizedSymbol label, TransitionGuard guard, 
            RALocation source, RALocation destination, Assignment assignment) {
        this.label = label;
        this.guard = guard;
        this.source = source;
        this.destination = destination;
        this.assignment = assignment;
    }
    
    public abstract boolean isEnabled(VarValuation registers, ParValuation parameters, Constants consts);
    
    public VarValuation execute(VarValuation registers, ParValuation parameters, Constants consts) {        
        return this.getAssignment().compute(registers, parameters, consts);
    }
    
    /**
     * @return the label
     */
    public ParameterizedSymbol getLabel() {
        return label;
    }

    /**
     * @return the source
     */
    public RALocation getSource() {
        return source;
    }

    /**
     * @return the destination
     */
    public RALocation getDestination() {
        return destination;
    }

    /**
     * @return the assignment
     */
    public Assignment getAssignment() {
        return assignment;
    }

    /**
     * @return the guard
     */
    public TransitionGuard getGuard() {
        return guard;
    }
    
    
    
}
