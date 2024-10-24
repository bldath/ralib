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
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.ListAlphabet;
import net.automatalib.automaton.transducer.FastMealy;
import net.automatalib.word.Word;


public class MyEquivalenceOracle implements IOEquivalenceOracle {
    private MutableRegisterAutomaton RA;
    private FastMealy MM;
    private Alphabet<ParameterizedSymbol> alphabet;
    private Map<DataType, Theory> teachers;
    private Word<PSymbolInstance> counterexample;
    private final MySUL mySUL;

    public MyEquivalenceOracle(MutableRegisterAutomaton RA, Alphabet<ParameterizedSymbol> alphabet, Map<DataType, Theory> teachers, MySUL mySUL) {
        this.RA = RA;
        this.alphabet = alphabet;
        this.teachers = teachers;
        this.counterexample = Word.epsilon();
        this.mySUL = mySUL;
    }

    public PSymbolInstance PsToPsi(ParameterizedSymbol ps) {
        DataValue[] vals = new DataValue[ps.getArity()];
        SymbolicDataValueGenerator.ParameterGenerator pgen = new SymbolicDataValueGenerator.ParameterGenerator();
        ParValuation pval = new ParValuation();
        int i = 0;
        for (DataType t : ps.getPtypes()) {
            Parameter p = pgen.next(t);
            System.out.println("Datatype: " + p.getType().toString() + " ID: " + p.getId());
            List<DataValue> old = computeOld(t, pval);
            DataValue dv = teachers.get(t).getFreshValue(old);
            vals[i] = dv;
            pval.put(p, vals[i]);
            i++;
        }
        PSymbolInstance psi = new PSymbolInstance(ps, vals);
        counterexample = counterexample.append(psi);
        System.out.println("CE: " + counterexample.toString());
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
        Word<ParameterizedSymbol> iWord = q.getInput();
        if (!(q.getOutput() instanceof Word)) {
            throw new IllegalStateException("MEALY QUERY OUTPUT ERROR: " + q.getOutput());
        }
        Word<ParameterizedSymbol> oWord = (Word<ParameterizedSymbol>) q.getOutput();
        List<ParameterizedSymbol> oWList = new ArrayList<>();
        for (ParameterizedSymbol pso: oWord) {
            oWList.add(pso);
        }
        ParameterizedSymbol last = oWList.get(oWList.size() - 1);
        if (last.getName().equals("+[]") || last.getName().equals("-[]")) {
            if (last.getName().equals("+[]")) {
                b = true;
            }
            for (ParameterizedSymbol ps: iWord) {
                System.out.println("PS " + ps);
                PSymbolInstance psi = PsToPsi(ps);
                System.out.println("PSI " + psi);
                counterexample = counterexample.append(psi);
            }
            DefaultQuery<PSymbolInstance, Boolean> qRA = new DefaultQuery<>(this.counterexample, b);
            return qRA;
        } else {
            Iterator oWIt = oWList.iterator();
            for (ParameterizedSymbol ps: iWord) {
                System.out.println("PS " + ps);
                PSymbolInstance psi = PsToPsi(ps);
                System.out.println("PSI " + psi);
                counterexample = counterexample.append(psi);
                ParameterizedSymbol pso = (ParameterizedSymbol) oWIt.next();
                System.out.println("PSo " + pso);
                PSymbolInstance psio = PsToPsi(pso);
                System.out.println("PSIo " + psi);
                counterexample = counterexample.append(psio);
            }
            DefaultQuery<PSymbolInstance, Boolean> qRAo = new DefaultQuery<>(this.counterexample, b);
            return qRAo;
        }
    }

    public DefaultQuery<PSymbolInstance, Object> translateCounterExampleOld(DefaultQuery<ParameterizedSymbol, Object> q) {
        Word<PSymbolInstance> ce = Word.epsilon();
        for (ParameterizedSymbol ps: q.getInput()) {
            System.out.println("PS " + ps);
            PSymbolInstance psi = PsToPsi(ps);
            System.out.println("PSI " + psi);
            ce = ce.append(psi);
        }
        if (q.getOutput() instanceof Word) {
            System.out.println("OUTPUT IS " + q.getOutput());
            Word<ParameterizedSymbol> qo = (Word<ParameterizedSymbol>) q.getOutput();
            Word<PSymbolInstance> ceo = Word.epsilon();
            for (ParameterizedSymbol ps: qo) {
                System.out.println("PSo " + ps);
                PSymbolInstance psi = PsToPsi(ps);
                System.out.println("PSIo " + psi);
                ceo = ceo.append(psi);
            }
            DefaultQuery<PSymbolInstance, Object> qRAo = new DefaultQuery<>(ce, ceo);
            return qRAo;
        }
        DefaultQuery<PSymbolInstance, Object> qRA = new DefaultQuery<>(ce, q.getOutput());
        return qRA;
    }

    @Override //TODO: When no counterexample
    public DefaultQuery<PSymbolInstance, Boolean> findCounterExample(
            RegisterAutomaton a, Collection<? extends PSymbolInstance> clctn) {
                MyRAtoMealyTransformer RAtoM = new MyRAtoMealyTransformer(RA, alphabet);
                this.MM = RAtoM.getMealy();
                System.out.println("Made mealy");
                MembershipOracle mSul = new SULOracle(mySUL);
                RandomWpMethodEQOracle rwpO = new RandomWpMethodEQOracle<>(mSul, 0, 2); //FIX INTS
                System.out.println("Made RWPEQOracle");
                Collection<ParameterizedSymbol> inputAlph = alphabetTranslator((Collection<PSymbolInstance>) clctn);
                System.out.println("Made inputalphabet: " + inputAlph.toString());
                DefaultQuery<ParameterizedSymbol, Object> qM = rwpO.findCounterExample(MM, inputAlph);
                if (qM.getOutput() instanceof Word) {
                    Word<ParameterizedSymbol> tmpW = (Word<ParameterizedSymbol>) qM.getOutput();
                    System.out.println("Mealy counterexample input: " + qM.getInput() + " and output word: " + tmpW);
                } else {
                    Boolean tmpB = (Boolean) qM.getOutput();
                    System.out.println("Mealy counterexample input: " + qM.getInput() + " and output boolean: " + tmpB);
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
