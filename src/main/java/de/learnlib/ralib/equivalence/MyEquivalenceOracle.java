package de.learnlib.ralib.equivalence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.equivalence.RandomWpMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.query.DefaultQuery;
import de.learnlib.ralib.automata.MutableRegisterAutomaton;
import de.learnlib.ralib.automata.MyRAtoMealyTransformer;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.sul.MySUL;
import de.learnlib.ralib.words.OutputSymbol;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.transducer.FastMealy;
import net.automatalib.word.Word;


public class MyEquivalenceOracle implements IOEquivalenceOracle {
    private MutableRegisterAutomaton ra;
    private FastMealy mealyMachine;
    private Alphabet<ParameterizedSymbol> alphabet;
    private Word<PSymbolInstance> counterexample;
    private MySUL mySUL;
    private Collection<ParameterizedSymbol> inputAlph;
    private Word<PSymbolInstance> inputPrefix = null;
    private Word<PSymbolInstance> outputPrefix = null;
    private Integer ceCount = 0;

    private final int minimalSize;
    private final int rndLength;
    private final int bound;

    public MyEquivalenceOracle(Alphabet<ParameterizedSymbol> alphabet,
    		MySUL mySUL,
    		int minimalSize,
    		int rndLength,
    		int bound) {
        this.inputAlph = new ArrayList<>();
        this.alphabet = alphabet;
        makeInputAlphabet(alphabet);
        this.counterexample = Word.epsilon();
        this.mySUL = mySUL;
        this.inputPrefix = Word.epsilon();
        this.outputPrefix = Word.epsilon();
        this.minimalSize = minimalSize;
        this.rndLength = rndLength;
        this.bound = bound;
    }

    public MyEquivalenceOracle(Alphabet<ParameterizedSymbol> alphabet, MySUL mySUL) {
    	this(alphabet, mySUL, 1, 10, 1000);
    }

    public void setHypothesis(MutableRegisterAutomaton ra) {
        this.ra = ra;
    }

    public void setAlphabet(Alphabet<ParameterizedSymbol> alphabet) {
        this.alphabet = alphabet;
    }

    public void makeInputAlphabet(Alphabet<ParameterizedSymbol> alphabet) {
        for (ParameterizedSymbol ps : alphabet) {
            if (!(ps instanceof OutputSymbol)) {
                this.inputAlph.add(ps);
            }
        }
    }

    public void setMealy(FastMealy mealyMachine) {
        this.mealyMachine = mealyMachine;
    }

    public void setSUL(MySUL mySUL) {
        this.mySUL = mySUL;
    }

    public void setEpsilonCounterExample() {
        this.counterexample = Word.epsilon();
    }

    private DefaultQuery<PSymbolInstance, Boolean> formatCounterExample() {
        counterexample = Word.epsilon();
        Boolean b = false;
        this.inputPrefix = mySUL.getInputPrefix();
        this.outputPrefix = mySUL.getOutputPrefix();

        List<PSymbolInstance> oWList = new ArrayList<>();
        for (PSymbolInstance pso: outputPrefix) {
            oWList.add(pso);
        }
        PSymbolInstance last = oWList.get(oWList.size() - 1);
        if (last.getBaseSymbol().getName().equals("+[]") || last.getBaseSymbol().getName().equals("-[]")) {
            DefaultQuery<PSymbolInstance, Boolean> qRA = new DefaultQuery<>(this.inputPrefix, !ra.accepts(counterexample));
            return qRA;
        } else {
            Iterator oWIt = oWList.iterator();
            for (PSymbolInstance psi: inputPrefix) {
                counterexample = counterexample.append(psi);
                PSymbolInstance pso = (PSymbolInstance) oWIt.next();
                counterexample = counterexample.append(pso);
            }
            DefaultQuery<PSymbolInstance, Boolean> qRAo = new DefaultQuery<>(this.counterexample, !ra.accepts(counterexample));
            return qRAo;
        }
    }

    @Override
    public DefaultQuery<PSymbolInstance, Boolean> findCounterExample(
            RegisterAutomaton ra, Collection<? extends PSymbolInstance> clctn) {
                this.ra = (MutableRegisterAutomaton) ra;
                MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(this.ra, this.alphabet);
                this.mealyMachine = raToM.getMealy();
                System.out.println("Made mealy");
                MembershipOracle mSul = new SULOracle(mySUL);
                RandomWpMethodEQOracle rwpO = new RandomWpMethodEQOracle<>(mSul, minimalSize, rndLength, bound); //FIX INTS
                System.out.println("Made RWPEQOracle");
                //System.out.println("Inputalphabet is: " + inputAlph.toString());
                DefaultQuery<ParameterizedSymbol, Object> qM = rwpO.findCounterExample(mealyMachine, inputAlph);
                if (qM == null) {
                    if (ceCount != 0) {
                        System.out.println("RWP_CE " + ceCount);
                        System.out.println("No more mealy counterexample");
                        ceCount = 0;
                    }
                    return null;
                }
                ceCount++;
                //System.out.println("Generated LearnLib mealy counterexample: " + qM.toString());
                DefaultQuery<PSymbolInstance, Boolean> qRA = formatCounterExample();
                System.out.println("Formated counterexample: " + qRA.toString());
                return qRA;
            }
    
    public long getResets() {
    	return mySUL.getResets();
    }
    
    public long getInputs() {
    	return mySUL.getInputs();
    }
}
