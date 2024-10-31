package de.learnlib.ralib.automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.learnlib.ralib.automata.guards.AtomicGuardExpression;
import de.learnlib.ralib.automata.guards.Conjunction;
import de.learnlib.ralib.automata.guards.Disjunction;
import de.learnlib.ralib.automata.guards.GuardExpression;
import de.learnlib.ralib.automata.guards.Negation;
import de.learnlib.ralib.automata.guards.Relation;
import de.learnlib.ralib.automata.guards.TrueGuardExpression;
import de.learnlib.ralib.automata.output.OutputTransition;
import de.learnlib.ralib.words.OutputSymbol;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.transducer.FastMealy;
import net.automatalib.automaton.transducer.FastMealyState;

public class MyRAtoMealyTransformer {

    private MutableRegisterAutomaton ra;
    private RALocation startLoc;
    private FastMealy mealyMachine;
    private Map<RALocation, FastMealyState> lookupStates = new HashMap<>();
    private Alphabet<ParameterizedSymbol> alphabet;
    private Collection<RALocation> outputStates;

    public MyRAtoMealyTransformer(MutableRegisterAutomaton ra, Alphabet<ParameterizedSymbol> alphabet) {
        this.ra = ra;
        this.startLoc = ra.getInitialState();
        this.lookupStates = new HashMap<>();
        this.alphabet = alphabet;
        this.outputStates = getOutputStates();
        depthFirstSearch();
    }

    public FastMealy getMealy() {
        return this.mealyMachine;
    }

    public Map<RALocation, FastMealyState> getLookupStates() {
        return this.lookupStates;
    }

    public List<Transition> getOutputTransitions() {
        List<Transition> tList = new ArrayList<>();
        for (RALocation loc : ra.getStates()) {
            for (Transition t : loc.getOut()) {
                if (t instanceof OutputTransition) {
                    tList.add(t);
                }
            }
        }
        return tList;
    }

    public Collection<RALocation> getOutputStates() {
        Set<RALocation> ret = new HashSet<>();
        for (Transition t : getOutputTransitions()) {
            ret.add(t.getSource());
        }
        return ret;
    }

    private void printTransitionsAndStatesByType() {
        for (Transition it : ra.getInputTransitions()) {
            System.out.println("INPUTTRANSITION " + it.toString());
        }
        for (Transition ot : getOutputTransitions()) {
            System.out.println("OUTPUTTRANSITION " + ot.toString());
        }
        for (RALocation il : ra.getInputStates()) {
            System.out.println("INPUTSTATE " + il.toString());
        }
        for (RALocation ol : getOutputStates()) {
            System.out.println("OUTPUTSTATE " + ol.toString());
        }
    }

    private void depthFirstSearch() {
        printTransitionsAndStatesByType();
        Collection<Transition> startTrs = this.startLoc.getOut();
        System.out.println("STARTLOCATION IS: " + startLoc.toString());
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> mealy = new FastMealy<>(this.alphabet);
        FastMealyState<ParameterizedSymbol> mStartState = mealy.addInitialState();
        lookupStates.put(this.startLoc, mStartState);
        System.out.println("LOOKUP " + startLoc.toString() + " " + mStartState.toString());
        for (Transition t : startTrs) {
            if (keepTransition(t).equals(true)) {
                ParameterizedSymbol symb = t.getLabel();
                RALocation destLoc = t.getDestination();
                if (outputStates.contains(destLoc)) {
                    Collection<Transition> fromDestTrs = destLoc.getOut();
                    Integer count = 0;
                    for (Transition fdt : fromDestTrs) {
                        RALocation destLoc2 = fdt.getDestination();
                        ParameterizedSymbol os = fdt.getLabel();
                        if (keepTransition(fdt).equals(true)) {
                            count++;
                            if (!this.lookupStates.containsKey(destLoc2)) {
                                FastMealyState<ParameterizedSymbol> mState2 = mealy.addState();
                                this.lookupStates.put(destLoc2, mState2);
                                System.out.println("LOOKUP " + destLoc2.toString() + " " + mState2.toString());
                                mealy.addTransition(this.lookupStates.get(this.startLoc), symb, mState2, os);
                                System.out.print("FROM_1 " + mealy.getState(this.lookupStates.get(this.startLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getOutput() + "\n");
                                visit(destLoc2, mealy);
                            } else {
                                mealy.addTransition(this.lookupStates.get(this.startLoc), symb, this.lookupStates.get(destLoc2), os);
                                System.out.print("FROM_2 " + mealy.getState(this.lookupStates.get(this.startLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getOutput() + "\n");
                            }
                        }
                    }
                    if (count > 1) {
                        throw new IllegalStateException("TOO MANY OUTPUT TRANSITIONS IN LOC " + destLoc.toString());
                    }
                } else {
                    OutputSymbol output;
                    if (destLoc.isAccepting()) {
                    output = new OutputSymbol("+") {};
                    } else {
                        output = new OutputSymbol("-") {};
                    }
                    if (!this.lookupStates.containsKey(destLoc)) {
                        FastMealyState<ParameterizedSymbol> mState = mealy.addState();
                        this.lookupStates.put(destLoc, mState);
                        mealy.addTransition(this.lookupStates.get(this.startLoc), symb, mState, output);
                        System.out.print("FROM_A " + mealy.getState(this.lookupStates.get(this.startLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getOutput() + "\n");
                        visit(destLoc, mealy);
                    } else {
                        mealy.addTransition(this.lookupStates.get(this.startLoc), symb, this.lookupStates.get(destLoc), output);
                        System.out.print("FROM_B " + mealy.getState(this.lookupStates.get(this.startLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(this.startLoc), symb).getOutput() + "\n");
                    }
                }
            }
        }
        this.mealyMachine = mealy;
    }

    private Boolean readGuards(GuardExpression g, Boolean negate) {
        Boolean res = true;
        if (g instanceof TrueGuardExpression) {
            System.out.println("TRUE");
            if (negate) {
                res = false;
            } else {
                res = true;
            }
        } else if (g instanceof AtomicGuardExpression) {
            AtomicGuardExpression tmp = (AtomicGuardExpression) g;
            Relation rTmp = tmp.getRelation();
            switch(rTmp) {
                case NOT_EQUALS:
                    System.out.println("CASE NOT EQUALS");
                    if (negate) {
                        res = false;
                    } else {
                        res = true;
                    }
                    break;
                case EQUALS:
                    System.out.println("CASE EQUALS");
                    if (negate) {
                        res = true;
                    } else {
                        res = false;
                    }
                    break;
                default:
                    System.out.println("CASE OTHER ATOMICGUARDEXPRESSION");
                    res = false;
                    break;
            }
        } else if (g instanceof Conjunction)  { // In some RA it is always Conjunction first
            Conjunction tmp = (Conjunction) g;
            GuardExpression[] conjuncts = tmp.getConjuncts();
            for (GuardExpression c: conjuncts) {
                System.out.println("CONJUNCT");
                Boolean tmpRes = readGuards(c, negate);
                if (tmpRes.equals(false)) {
                    res = false;
                }
            }
        } else if (g instanceof Disjunction) {
            Disjunction tmp = (Disjunction) g;
            GuardExpression[] disjuncts = tmp.getDisjuncts();
            for (GuardExpression d: disjuncts) {
                System.out.println("DISJUNCT");
                Boolean tmpRes = readGuards(d, negate);
                if (tmpRes.equals(false)) {
                    res = false;
                }
            }
        } else if (g instanceof Negation) {
            System.out.println("NEGATION");
            Negation tmp = (Negation) g;
            GuardExpression negated = tmp.getNegated();
            negate = !negate;
            res = readGuards(negated, negate);
        } else {
            res = false;
            throw new IllegalStateException("GUARDEXPRESSION ERROR: WHY ARE YOU HERE? " + g.toString());
            //System.out.println("UNSUPPORTED GUARDEXPRESSION " + g.toString());
        }
        return res;
    }

    private Boolean keepTransition(Transition t){
        Boolean negate = false;
        TransitionGuard tg = t.getGuard();
        GuardExpression ge = tg.getCondition();
        return readGuards(ge, negate);
    }

    private void visit(
        RALocation loc,
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> mealy
        ) {
        Collection<RALocation> outputStates = getOutputStates();
        Collection<Transition> trs = loc.getOut();
        if (trs != null) {
            for (Transition t : trs) {
                if (keepTransition(t).equals(true)) {
                    RALocation sourceLoc = t.getSource();
                    RALocation destLoc = t.getDestination();
                    ParameterizedSymbol symb = t.getLabel();
                    if (outputStates.contains(destLoc)) {
                        Integer count = 0;
                        Collection<Transition> fromDestTrs = destLoc.getOut();
                        for (Transition fdt : fromDestTrs) {
                            RALocation destLoc2 = fdt.getDestination();
                            ParameterizedSymbol os = fdt.getLabel();
                            if (keepTransition(fdt).equals(true)) {
                                count++;
                                if (!this.lookupStates.containsKey(destLoc2)) {
                                    FastMealyState<ParameterizedSymbol> mState2 = mealy.addState();
                                    this.lookupStates.put(destLoc2, mState2);
                                    System.out.println("LOOKUP " + destLoc2.toString() + " " + mState2.toString());
                                    mealy.addTransition(this.lookupStates.get(sourceLoc), symb, mState2, os);
                                    System.out.print("FROM_3 " + mealy.getState(this.lookupStates.get(sourceLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getOutput() + "\n");
                                    visit(destLoc2, mealy);
                                } else {
                                    mealy.addTransition(this.lookupStates.get(sourceLoc), symb, this.lookupStates.get(destLoc2), os);
                                    System.out.print("FROM_4 " + mealy.getState(this.lookupStates.get(sourceLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getOutput() + "\n");
                                }
                            }
                        }
                        if (count > 1) {
                            throw new IllegalStateException("TOO MANY OUTPUT TRANSITIONS IN LOC " + destLoc.toString());
                        }
                    } else {
                        ParameterizedSymbol output;
                            if (destLoc.isAccepting()) {
                                output = new OutputSymbol("+") {};
                            } else {
                                output = new OutputSymbol("-") {};
                            }
                        if (!this.lookupStates.containsKey(destLoc)) {
                            FastMealyState<ParameterizedSymbol> mState = mealy.addState();
                            this.lookupStates.put(destLoc, mState);
                            mealy.addTransition(this.lookupStates.get(sourceLoc), symb, this.lookupStates.get(destLoc), output);
                            System.out.print("FROM_C " + mealy.getState(this.lookupStates.get(sourceLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getOutput() + "\n");
                            visit(destLoc, mealy);
                        } else {
                            mealy.addTransition(this.lookupStates.get(sourceLoc), symb, this.lookupStates.get(destLoc), output);
                            System.out.print("FROM_D " + mealy.getState(this.lookupStates.get(sourceLoc).getId()) + " TO " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getSuccessor() + " " + symb.toString() + " WITH OUTPUT " + mealy.getTransition(this.lookupStates.get(sourceLoc), symb).getOutput() + "\n");
                        }
                    }
                }
            }
        }
    }
}
