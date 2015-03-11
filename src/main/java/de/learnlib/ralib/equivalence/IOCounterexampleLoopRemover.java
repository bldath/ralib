package de.learnlib.ralib.equivalence;

/*
 * Copyright (C) 2015 falk.
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



import de.learnlib.ralib.automata.RALocation;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.oracles.io.IOOracle;
import de.learnlib.ralib.sul.SimulatorSUL;
import de.learnlib.ralib.theory.Theory;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import net.automatalib.commons.util.Pair;
import net.automatalib.words.Word;

/**
 *
 * @author falk
 */
public class IOCounterexampleLoopRemover {
    
    private static class Loop {
        private final int min;
        private final int max;
        public Loop(int min, int max) {
            this.min = min;
            this.max = max;
        }        
    }
    
    private final ParameterizedSymbol[] inputs;
    private final Constants consts;
    private final Map<DataType, Theory> teachers;       
    private final IOOracle sulOracle;
    private RegisterAutomaton hypothesis;

    public IOCounterexampleLoopRemover(ParameterizedSymbol[] inputs, Constants consts, Map<DataType, Theory> teachers, IOOracle sulOracle) {
        this.inputs = inputs;
        this.consts = consts;
        this.teachers = teachers;
        this.sulOracle = sulOracle;
    }

    public Word<PSymbolInstance> removeLoops(
            Word<PSymbolInstance> ce, RegisterAutomaton hyp) {
        
        this.hypothesis = hyp;
        
        Map<Integer, List<Loop>> loops = new HashMap<>();
        List<Integer> sizes = new ArrayList<>();
        RALocation[] trace = execute(ce);
        for (int i=0; i<trace.length; i++) {
            for (int j=i+1; j<trace.length; j++) {
                if (!trace[i].equals(trace[j])) {
                    continue;
                }
                int length = j-i;
                System.out.println("Found loop of length " + length);
                List<Loop> list = loops.get(length);
                if (list == null) {
                    list = new LinkedList<>();
                    loops.put(length, list);
                    sizes.add(length);
                }
                list.add(new Loop(i,j));
            }
        }
        
        Collections.sort(sizes);
        Collections.reverse(sizes);
        for (Integer i : sizes) {
            System.out.println("Checking length " + i);            
            List<Loop> list = loops.get(i);
            for (Loop loop : list) {
                Word<PSymbolInstance> shorter = shorten(ce, loop);
                Word<PSymbolInstance> candidate = sulOracle.trace(shorter);
                System.out.println(candidate);
                if (!hypothesis.accepts(candidate)) {
                    System.out.println("Reduced CE length by " + i + 
                            " to " + candidate.length());
                    return shorter;
                }
            }            
        }
        return ce;
    }
    
    private Word<PSymbolInstance> shorten(Word<PSymbolInstance> ce, Loop loop) {
        
        Word<PSymbolInstance> prefix = ce.prefix(loop.min * 2);
        Word<PSymbolInstance> suffix = ce.subWord(loop.max * 2, ce.length());
        return prefix.concat(suffix);
    }    
    
    private RALocation[] execute(Word<PSymbolInstance> ce) {
        List<RALocation> trace = new ArrayList<>();
        for (int i=0; i<ce.length(); i+=2) {
            Word<PSymbolInstance> prefix = ce.prefix(i);
            trace.add(hypothesis.getLocation(prefix));
        }

        return trace.toArray(new RALocation[] {}); 
    }
    
}