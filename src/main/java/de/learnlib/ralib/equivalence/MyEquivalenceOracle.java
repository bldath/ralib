package de.learnlib.ralib.equivalence;

import java.util.ArrayList;
import java.util.Collection;
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
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.data.DataValue;
import de.learnlib.ralib.data.ParValuation;
import de.learnlib.ralib.data.SymbolicDataValue.Parameter;
import de.learnlib.ralib.data.util.SymbolicDataValueGenerator;
import de.learnlib.ralib.sul.DataWordSUL;
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
    private final DataWordSUL dwSUL;
    private MutableRegisterAutomaton RA;
    private FastMealy MM;
    private Alphabet<ParameterizedSymbol> alphabet;
    private Map<DataType, Theory> teachers;
    private Constants consts;
    private Word<PSymbolInstance> pref;
    private final MySUL mySUL;

    public MyEquivalenceOracle(DataWordSUL dwSUL, MutableRegisterAutomaton RA, Alphabet<ParameterizedSymbol> alphabet, Map<DataType, Theory> teachers, Constants consts, MySUL mySUL) {
        this.dwSUL = dwSUL;
        this.RA = RA;
        this.alphabet = alphabet;
        this.teachers = teachers;
        this.consts = consts;
        this.pref = Word.epsilon();
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
        pref = pref.append(psi);
        System.out.println("Prefix: " + pref.toString());
        return psi;
    }

    private List<DataValue> computeOld(DataType t, ParValuation pval) {
    java.util.Set<DataValue> set = new java.util.LinkedHashSet<>();
    set.addAll(DataWords.valSet(pref, t));
    for (DataValue d : pval.values()){
        if (d.getType().equals(t)) {
            set.add(d);
            }
        }
    return new  ArrayList<>(set);
    }

    public DefaultQuery<PSymbolInstance, Boolean> translateCounterExample(DefaultQuery<ParameterizedSymbol, Boolean> q) {
        Boolean b = false;
        // if (q.getOutput().equals(true)) {
        //     b = true;
        // }
        System.out.println("HERE");
        Word<PSymbolInstance> ce = Word.epsilon();
        Word<ParameterizedSymbol> qw = q.getInput();
        //System.out.println(q.getOutput().getClass()); //FIX THIS: WRONG TYPE.
        for (ParameterizedSymbol ps: q.getInput()) {
            System.out.println("PS " + ps);
            PSymbolInstance psi = PsToPsi(ps);
            System.out.println("PSI " + psi);
            ce = ce.append(psi);
        }
        DefaultQuery<PSymbolInstance, Boolean> qRA = new DefaultQuery<>(ce, b);
        return qRA;
    }

    @Override
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
                //TODO FIX BUGS WHEN FINDING MEALY COUNTEREXAMPLE
                DefaultQuery<ParameterizedSymbol, Boolean> qM = rwpO.findCounterExample(MM, inputAlph);
                System.out.println("Generated mealy counterexample: " + qM.toString());
                DefaultQuery<PSymbolInstance, Boolean> qRA = translateCounterExample(qM);//CHECK THIS
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
