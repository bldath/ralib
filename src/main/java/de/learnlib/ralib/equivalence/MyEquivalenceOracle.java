package de.learnlib.ralib.equivalence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.equivalence.RandomWpMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.query.DefaultQuery;
import de.learnlib.ralib.automata.MutableRegisterAutomaton;
import de.learnlib.ralib.automata.MyRAtoMealyTransformer;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.data.DataValue;
import de.learnlib.ralib.data.ParValuation;
import de.learnlib.ralib.data.SymbolicDataValue.Parameter;
import de.learnlib.ralib.data.util.SymbolicDataValueGenerator;
import de.learnlib.ralib.sul.MySUL;
import de.learnlib.ralib.theory.Theory;
import de.learnlib.ralib.words.DataWords;
import de.learnlib.ralib.words.OutputSymbol;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.ListAlphabet;
import net.automatalib.automaton.transducer.FastMealy;
import net.automatalib.word.Word;


public class MyEquivalenceOracle implements IOEquivalenceOracle {
    private MutableRegisterAutomaton ra;
    private FastMealy mealyMachine;
    private Alphabet<ParameterizedSymbol> alphabet;
    private Map<DataType, Theory> teachers;
    private Word<PSymbolInstance> counterexample;
    private final MySUL mySUL;

    public MyEquivalenceOracle(MutableRegisterAutomaton ra, Alphabet<ParameterizedSymbol> alphabet, Map<DataType, Theory> teachers, MySUL mySUL) {
        this.ra = ra;
        this.alphabet = alphabet;
        this.teachers = teachers;
        this.counterexample = Word.epsilon();
        this.mySUL = mySUL;
    }

    public void setHypothesis(MutableRegisterAutomaton ra) {
    	this.ra = ra;
    }

    public PSymbolInstance PsToPsi(ParameterizedSymbol ps) {
        DataValue[] vals = new DataValue[ps.getArity()];
        SymbolicDataValueGenerator.ParameterGenerator pgen = new SymbolicDataValueGenerator.ParameterGenerator();
        ParValuation pval = new ParValuation();
        int i = 0;
        for (DataType t : ps.getPtypes()) {
            Parameter p = pgen.next(t);
            List<DataValue> old = computeOld(t, pval);
            DataValue dv = teachers.get(t).getFreshValue(old);
            vals[i] = dv;
            pval.put(p, vals[i]);
            i++;
        }
        PSymbolInstance psi = new PSymbolInstance(ps, vals);
        counterexample = counterexample.append(psi);
        //System.out.println("CE: " + counterexample.toString());
        return psi;
    }

    private List<DataValue> computeOld(DataType t, ParValuation pval) {
    java.util.Set<DataValue> set = new java.util.LinkedHashSet<>();
    set.addAll(DataWords.valSet(counterexample, t));
    for (DataValue d : pval.values()){
        if (d.getType().equals(t)) {
            set.add(d);
            }
        }
    return new  ArrayList<>(set);
    }

    public DefaultQuery<PSymbolInstance, Boolean> translateCounterExample(DefaultQuery<ParameterizedSymbol, Object> q) {
        Boolean b = false;
        if (!(q.getOutput() instanceof Word)) {
            throw new IllegalStateException("MEALY QUERY OUTPUT ERROR: " + q.getOutput());
        }
        Word<ParameterizedSymbol> iWord = q.getInput();
        Word<OutputSymbol> oWord = (Word<OutputSymbol>) q.getOutput();
        List<OutputSymbol> oWList = new ArrayList<>();
        for (OutputSymbol pso: oWord) {
            oWList.add(pso);
        }
        OutputSymbol last = oWList.get(oWList.size() - 1);
        if (last.getName().equals("+[]") || last.getName().equals("-[]")) {
            if (last.getName().equals("+[]")) {
                b = true;
            }
            for (ParameterizedSymbol ps: iWord) {
                PSymbolInstance psi = PsToPsi(ps);
            }
            DefaultQuery<PSymbolInstance, Boolean> qRA = new DefaultQuery<>(this.counterexample, b);
            return qRA;
        } else {
            Iterator oWIt = oWList.iterator();
            for (ParameterizedSymbol ps: iWord) {
                PSymbolInstance psi = PsToPsi(ps);
                OutputSymbol pso = (OutputSymbol) oWIt.next();
                PSymbolInstance psio = PsToPsi(pso);
            }
            DefaultQuery<PSymbolInstance, Boolean> qRAo = new DefaultQuery<>(this.counterexample, b);
            return qRAo;
        }
    }

    @Override
    public DefaultQuery<PSymbolInstance, Boolean> findCounterExample(
            RegisterAutomaton a, Collection<? extends PSymbolInstance> clctn) {
                MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(ra, alphabet);
                this.mealyMachine = raToM.getMealy();
                System.out.println("Made mealy");
                MembershipOracle mSul = new SULOracle(mySUL);
                RandomWpMethodEQOracle rwpO = new RandomWpMethodEQOracle<>(mSul, 0, 2); //FIX INTS
                System.out.println("Made RWPEQOracle");
                Collection<ParameterizedSymbol> inputAlph = alphabetTranslator((Collection<PSymbolInstance>) clctn);
                System.out.println("Made inputalphabet: " + inputAlph.toString());
                DefaultQuery<ParameterizedSymbol, Object> qM = rwpO.findCounterExample(mealyMachine, inputAlph);
                if (qM == null) {
                    System.out.println("No more mealy counterexample");
                    return null;
                }
                System.out.println("Generated mealy counterexample: " + qM.toString());
                DefaultQuery<PSymbolInstance, Boolean> qRA = translateCounterExample(qM);
                System.out.println("Translated counterexample: " + qRA.toString());
                return qRA;
            }

    private Collection<ParameterizedSymbol> alphabetTranslator (Collection<PSymbolInstance> psiAlph) {
        List<ParameterizedSymbol> tmpList = new LinkedList<>();
        for (PSymbolInstance psi : psiAlph) {
            ParameterizedSymbol ps = psi.getBaseSymbol();
            tmpList.add(ps);
        }
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(tmpList);
        return alphabet;
    }

}
