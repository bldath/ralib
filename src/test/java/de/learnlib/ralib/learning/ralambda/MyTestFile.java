package de.learnlib.ralib.learning.ralambda;

//import static de.learnlib.ralib.example.keygen.MapAutomatonExample.AUTOMATON;
//import static de.learnlib.ralib.example.llambda.LLambdaAutomatonExample.AUTOMATON;
//import static de.learnlib.ralib.example.login.LoginAutomatonExample.AUTOMATON;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.I_GET;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.I_PUT;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.O_GET;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.O_NULL;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.O_PUT;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.T_KEY;
import static de.learnlib.ralib.example.keygen.MapAutomatonExample.T_VAL;
import static de.learnlib.ralib.example.llambda.LLambdaAutomatonExample.A;
import static de.learnlib.ralib.example.llambda.LLambdaAutomatonExample.B;
import static de.learnlib.ralib.example.login.LoginAutomatonExample.I_LOGIN;
import static de.learnlib.ralib.example.login.LoginAutomatonExample.I_LOGOUT;
import static de.learnlib.ralib.example.login.LoginAutomatonExample.I_REGISTER;
import static de.learnlib.ralib.example.login.LoginAutomatonExample.T_PWD;
import static de.learnlib.ralib.example.login.LoginAutomatonExample.T_UID;
import static de.learnlib.ralib.example.stack.StackAutomatonExample.AUTOMATON;
import static de.learnlib.ralib.example.stack.StackAutomatonExample.I_POP;
import static de.learnlib.ralib.example.stack.StackAutomatonExample.I_PUSH;
import static de.learnlib.ralib.example.stack.StackAutomatonExample.T_INT;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.logging.Level;

import org.testng.Assert;
import org.testng.annotations.Test;

import de.learnlib.query.DefaultQuery;
import de.learnlib.ralib.RaLibTestSuite;
import de.learnlib.ralib.TestUtil;
import de.learnlib.ralib.automata.MutableRegisterAutomaton;
import de.learnlib.ralib.automata.MyRAtoMealyTransformer;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.automata.xml.RegisterAutomatonImporter;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.data.DataValue;
import de.learnlib.ralib.dt.DTLeaf;
import de.learnlib.ralib.equivalence.IOCounterExamplePrefixFinder;
import de.learnlib.ralib.equivalence.IOCounterExamplePrefixReplacer;
import de.learnlib.ralib.equivalence.IOCounterexampleLoopRemover;
import de.learnlib.ralib.equivalence.IOEquivalenceTest;
import de.learnlib.ralib.equivalence.MyEquivalenceOracle;
import de.learnlib.ralib.learning.Measurements;
import de.learnlib.ralib.learning.MeasuringOracle;
import de.learnlib.ralib.learning.SymbolicSuffix;
import de.learnlib.ralib.oracles.DataWordOracle;
import de.learnlib.ralib.oracles.SDTLogicOracle;
import de.learnlib.ralib.oracles.SimulatorOracle;
import de.learnlib.ralib.oracles.TreeOracleFactory;
import de.learnlib.ralib.oracles.io.IOCache;
import de.learnlib.ralib.oracles.io.IOFilter;
import de.learnlib.ralib.oracles.io.IOOracle;
import de.learnlib.ralib.oracles.mto.MultiTheorySDTLogicOracle;
import de.learnlib.ralib.oracles.mto.MultiTheoryTreeOracle;
import de.learnlib.ralib.solver.ConstraintSolver;
import de.learnlib.ralib.solver.simple.SimpleConstraintSolver;
import de.learnlib.ralib.sul.DataWordSUL;
import de.learnlib.ralib.sul.MySUL;
import de.learnlib.ralib.sul.SULOracle;
import de.learnlib.ralib.sul.SimulatorSUL;
import de.learnlib.ralib.theory.Theory;
import de.learnlib.ralib.theory.equality.EqualityTheory;
import de.learnlib.ralib.tools.theories.IntegerEqualityTheory;
import de.learnlib.ralib.words.InputSymbol;
import de.learnlib.ralib.words.OutputSymbol;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.ListAlphabet;
import net.automatalib.automaton.transducer.FastMealy;
import net.automatalib.automaton.transducer.FastMealyState;
import net.automatalib.automaton.transducer.MealyTransition;
import net.automatalib.word.Word;

public class MyTestFile extends RaLibTestSuite {
    @Test
    public void myTest1() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_PUSH, I_POP));
        Constants consts = new Constants();
        RegisterAutomaton sul = AUTOMATON;
        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(T_INT, new IntegerEqualityTheory(T_INT));
        ConstraintSolver solver = new SimpleConstraintSolver();
        Measurements mes = new Measurements();
        MeasuringOracle mto = new MeasuringOracle(new MultiTheoryTreeOracle(
            dwOracle, teachers, new Constants(), solver), mes);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, I_PUSH, I_POP);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        expMealy.addTransition(exp0, I_PUSH, exp0, new OutputSymbol("+") {});
        expMealy.addTransition(exp0, I_POP, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_PUSH, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_POP, exp1, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest2() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_PUSH, I_POP));
	    Constants consts = new Constants();
        RegisterAutomaton sul = AUTOMATON;
        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(T_INT, new IntegerEqualityTheory(T_INT));
        ConstraintSolver solver = new SimpleConstraintSolver();
        Measurements mes = new Measurements();
        MeasuringOracle mto = new MeasuringOracle(new MultiTheoryTreeOracle(
              dwOracle, teachers, new Constants(), solver), mes);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, I_PUSH, I_POP);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        Word<PSymbolInstance> ce = Word.fromSymbols(
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 0)),
        		new PSymbolInstance(I_POP, new DataValue(T_INT, 0)));
        ralambda.addCounterexample(new DefaultQuery<>(ce, sul.accepts(ce)));
        ralambda.learn();
        hyp = ralambda.getHypothesis();
        ce = Word.fromSymbols(
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 0)),
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 1)),
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 2)));
        ralambda.addCounterexample(new DefaultQuery<>(ce, sul.accepts(ce)));
        ralambda.learn();
        hyp = ralambda.getHypothesis();
        Assert.assertEquals(hyp.getStates().size(), 4);
        Assert.assertEquals(hyp.getTransitions().size(), 10);

        //Uses depth first search and does not keep all transitions
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp2 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp3 = expMealy.addState();
        expMealy.addTransition(exp0, I_PUSH, exp1, new OutputSymbol("+") {});
        expMealy.addTransition(exp1, I_POP, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp2, I_PUSH, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp2, I_POP, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_PUSH, exp3, new OutputSymbol("+") {});
        expMealy.addTransition(exp3, I_POP, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp3, I_PUSH, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, I_POP, exp2, new OutputSymbol("-") {});

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest3() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_PUSH, I_POP));
        Constants consts = new Constants();
        RegisterAutomaton sul = AUTOMATON;
        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(T_INT, new IntegerEqualityTheory(T_INT));
        ConstraintSolver solver = new SimpleConstraintSolver();
        MultiTheoryTreeOracle mto = new MultiTheoryTreeOracle(
              dwOracle, teachers, new Constants(), solver);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, I_PUSH, I_POP);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        Word<PSymbolInstance> ce = Word.fromSymbols(
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 0)),
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 1)),
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 2)));
        ralambda.addCounterexample(new DefaultQuery<>(ce, sul.accepts(ce)));
        ralambda.learn();
        hyp = ralambda.getHypothesis();
        ce = Word.fromSymbols(
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 0)),
        		new PSymbolInstance(I_POP, new DataValue(T_INT, 0)));
        ralambda.addCounterexample(new DefaultQuery<>(ce, sul.accepts(ce)));
        ralambda.learn();
        hyp = ralambda.getHypothesis();
        ce = Word.fromSymbols(
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 0)),
        		new PSymbolInstance(I_PUSH, new DataValue(T_INT, 1)),
        		new PSymbolInstance(I_POP, new DataValue(T_INT, 1)));
        ralambda.addCounterexample(new DefaultQuery<>(ce, sul.accepts(ce)));
        ralambda.learn();
        hyp = ralambda.getHypothesis();

        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp2 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp3 = expMealy.addState();
        expMealy.addTransition(exp0, I_PUSH, exp1, new OutputSymbol("+") {});
        expMealy.addTransition(exp1, I_PUSH, exp2, new OutputSymbol("+") {});
        expMealy.addTransition(exp2, I_POP, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp3, I_PUSH, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp3, I_POP, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp2, I_PUSH, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_POP, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, I_POP, exp3, new OutputSymbol("-") {});

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest4() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_PUT, I_GET, O_PUT, O_GET, O_NULL));
        Constants consts = new Constants();
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.keygen.MapAutomatonExample.AUTOMATON;
        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(de.learnlib.ralib.example.keygen.MapAutomatonExample.T_KEY, new IntegerEqualityTheory(de.learnlib.ralib.example.keygen.MapAutomatonExample.T_KEY));
        teachers.put(de.learnlib.ralib.example.keygen.MapAutomatonExample.T_VAL, new IntegerEqualityTheory(de.learnlib.ralib.example.keygen.MapAutomatonExample.T_VAL));
        ConstraintSolver solver = new SimpleConstraintSolver();
        Measurements mes = new Measurements();
        MeasuringOracle mto = new MeasuringOracle(new MultiTheoryTreeOracle(
              dwOracle, teachers, new Constants(), solver), mes);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, I_PUT, I_GET, O_PUT, O_GET, O_NULL);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        expMealy.addTransition(exp0, I_PUT, exp0, new OutputSymbol("+") {});
        expMealy.addTransition(exp1, I_PUT, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_GET, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, O_PUT, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, O_GET, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, O_NULL, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, I_GET, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, O_PUT, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, O_GET, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, O_NULL, exp1, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest5() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_PUT, I_GET));
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.keygen.MapAutomatonExample.AUTOMATON;

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(sul, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        //System.out.println("RA IS: " + sul.toString());

        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp2 = expMealy.addState();

        // When using old version of depth first search, get 6 states instead of 3

        // FastMealyState<ParameterizedSymbol> exp3 = expMealy.addState();
        // FastMealyState<ParameterizedSymbol> exp4 = expMealy.addState();
        // FastMealyState<ParameterizedSymbol> exp5 = expMealy.addState();

        expMealy.addTransition(exp0, I_PUT, exp1, O_PUT);
        expMealy.addTransition(exp1, I_PUT, exp2, O_PUT);
        expMealy.addTransition(exp1, I_GET, exp1, O_NULL);

        // When using old version of depth first search, get 6 transitions instead of 3

        // expMealy.addTransition(exp0, I_PUT, exp1, new ParameterizedSymbol("+") {});
        // expMealy.addTransition(exp1, O_PUT, exp2, new ParameterizedSymbol("+") {});

        // expMealy.addTransition(exp2, I_PUT, exp3, new ParameterizedSymbol("+") {});
        // expMealy.addTransition(exp3, O_PUT, exp4, new ParameterizedSymbol("+") {});

        // expMealy.addTransition(exp2, I_GET, exp5, new ParameterizedSymbol("+") {});
        // expMealy.addTransition(exp5, O_NULL, exp2, new ParameterizedSymbol("+") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }

        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(T_KEY, new IntegerEqualityTheory(T_KEY));
        teachers.put(T_VAL, new IntegerEqualityTheory(T_VAL));
        Constants consts = new Constants();
        SimulatorSUL dwSUL = new SimulatorSUL(sul, teachers, consts);
        MySUL msu = new MySUL(teachers, dwSUL);
        MyEquivalenceOracle mO = new MyEquivalenceOracle(alphabet, msu);
        Collection<PSymbolInstance> clctn = new ArrayList<>();
        PSymbolInstance psi_put = new PSymbolInstance(I_PUT, new DataValue(T_VAL, 0));
        PSymbolInstance psi_get = new PSymbolInstance(I_GET, new DataValue(T_KEY, 0));
        clctn.add(psi_put);
        clctn.add(psi_get);
        //CRASHES WHEN FINDING MEALY COUNTER EXAMPLE, EXCEPT ONCE IN A WHILE, BUT RA EXAMPLE IS INCOMPLETE
        //DefaultQuery<PSymbolInstance, Boolean> res = mO.findCounterExample(sul, clctn);
    }

    @Test
    public void myTest5b() {
        RegisterAutomatonImporter loader = TestUtil.getLoader(
                "/de/learnlib/ralib/automata/xml/sip.xml");
        RegisterAutomaton model = loader.getRegisterAutomaton();
        //System.out.println("RA IS: " + model.toString());

        Alphabet<InputSymbol> inputs = loader.getInputs();
        List<ParameterizedSymbol> tmp = new ArrayList<>();
        for (ParameterizedSymbol p : inputs) {
            tmp.add(p);
        }
        Alphabet<ParameterizedSymbol> alphabet =  new ListAlphabet<>(tmp);
        final Constants consts = loader.getConstants();
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        loader.getDataTypes().stream().forEach((t) -> {
            IntegerEqualityTheory theory = new IntegerEqualityTheory(t);
            theory.setUseSuffixOpt(false);
            teachers.put(t, theory);
        });

        SimulatorSUL dwSUL = new SimulatorSUL(model, teachers, consts);
        MySUL msu = new MySUL(teachers, dwSUL);
        MyEquivalenceOracle mO = new MyEquivalenceOracle(alphabet, msu);
        //DefaultQuery<PSymbolInstance, Boolean> res = mO.findCounterExample(model, null);
    }

    @Test
    public void myTest5c() {
        RegisterAutomatonImporter loader = TestUtil.getLoader(
                "/de/learnlib/ralib/automata/xml/sip.xml");
        RegisterAutomaton model = loader.getRegisterAutomaton();
        //System.out.println("RA IS: " + model.toString());
        Alphabet<InputSymbol> inputs = loader.getInputs();

        List<ParameterizedSymbol> tmp = new ArrayList<>();
        for (ParameterizedSymbol p : inputs) {
            tmp.add(p);
        }
        Alphabet<ParameterizedSymbol> alphabet =  new ListAlphabet<>(tmp);
        final Constants consts = loader.getConstants();
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        loader.getDataTypes().stream().forEach((t) -> {
            IntegerEqualityTheory theory = new IntegerEqualityTheory(t);
            theory.setUseSuffixOpt(false);
            teachers.put(t, theory);
        });

        SimulatorSUL dwSUL = new SimulatorSUL(model, teachers, consts);
        MySUL msu = new MySUL(teachers, dwSUL);
        MyEquivalenceOracle mO = new MyEquivalenceOracle(alphabet, msu);
        //WORKS WHEN BOUNDED
        //DefaultQuery<PSymbolInstance, Boolean> res = mO.findCounterExample(model, null);
    }

    @Test
    public void myTest5d() {
        long seed = -1386796323025681754L;
        logger.log(Level.FINE, "SEED={0}", seed);
        final Random unused = new Random(seed);
        RegisterAutomatonImporter loader = TestUtil.getLoader(
                "/de/learnlib/ralib/automata/xml/sip.xml");
        RegisterAutomaton model = loader.getRegisterAutomaton();
        ParameterizedSymbol[] inputs = loader.getInputs().toArray(
                new ParameterizedSymbol[]{});
        ParameterizedSymbol[] actions = loader.getActions().toArray(
                new ParameterizedSymbol[]{});
        final Constants consts = loader.getConstants();
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        loader.getDataTypes().stream().forEach((t) -> {
            IntegerEqualityTheory theory = new IntegerEqualityTheory(t);
            theory.setUseSuffixOpt(false);
            teachers.put(t, theory);
        });
        DataWordSUL sul = new SimulatorSUL(model, teachers, consts);
        IOOracle ioOracle = new SULOracle(sul, ERROR);
        IOCache ioCache = new IOCache(ioOracle);
        IOFilter ioFilter = new IOFilter(ioCache, inputs);
        teachers.values().stream().forEach((t) -> {
            ((EqualityTheory)t).setFreshValues(true, ioCache);
        });
        ConstraintSolver solver = new SimpleConstraintSolver();
        MultiTheoryTreeOracle mto = new MultiTheoryTreeOracle(
                ioFilter, teachers, consts, solver);
        MultiTheorySDTLogicOracle mlo =
                new MultiTheorySDTLogicOracle(consts, solver);
        for (ParameterizedSymbol ps : actions) {
        	if (!DTLeaf.isInput(ps) && ps.getArity() > 0) {
        		mto.treeQuery(Word.epsilon(), new SymbolicSuffix(ps));
        		break;
        	}
        }

        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers, consts, solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, mlo, consts, true, actions);
        ralambda.setSolver(solver);
            IOEquivalenceTest ioEquiv = new IOEquivalenceTest(
                    model, teachers, consts, true, actions);
        IOCounterexampleLoopRemover loops = new IOCounterexampleLoopRemover(ioOracle);
        IOCounterExamplePrefixReplacer asrep = new IOCounterExamplePrefixReplacer(ioOracle);
        IOCounterExamplePrefixFinder pref = new IOCounterExamplePrefixFinder(ioOracle);

        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        System.out.println("RA IS: " + model.toString());
        System.out.println("HYP IS: " + hyp.toString());
        List<ParameterizedSymbol> tmp = new ArrayList<>();
        for (ParameterizedSymbol p : inputs) {
            tmp.add(p);
        }
        Alphabet<ParameterizedSymbol> alphabet =  new ListAlphabet<>(tmp);

        SimulatorSUL dwSUL = new SimulatorSUL(model, teachers, consts);
        MySUL msu = new MySUL(teachers, dwSUL);
        MyEquivalenceOracle mO = new MyEquivalenceOracle(alphabet, msu);
        //WORKS WHEN BOUNDED BUT SOMETIMES CRASHES DUE TO BUG IN RALIB RALAMBDA HYPOTHESIS CREATION
        //RUN MyNewTestFile instead with RaStar, until bug is fixed in RaLambda library
        DefaultQuery<PSymbolInstance, Boolean> res = mO.findCounterExample(hyp, null);

        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            ralambda.addCounterexample(res);
            ralambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }

        hyp = ralambda.getHypothesis();
        System.out.println("HYP2 IS: " + hyp.toString());
        res = null;
        res = mO.findCounterExample(hyp, null);
        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            ralambda.addCounterexample(res);
            ralambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }

        hyp = ralambda.getHypothesis();
        System.out.println("HYP3 IS: " + hyp.toString());
        res = null;
        res = mO.findCounterExample(hyp, null);
        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            ralambda.addCounterexample(res);
            ralambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }
    }

    @Test
    public void myTest6() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(A, B));
        Constants consts = new Constants();
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.llambda.LLambdaAutomatonExample.AUTOMATON;

        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        ConstraintSolver solver = new SimpleConstraintSolver();
        Measurements mes = new Measurements();
        MeasuringOracle mto = new MeasuringOracle(new MultiTheoryTreeOracle(
              dwOracle, teachers, new Constants(), solver), mes);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, A, B);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        expMealy.addTransition(exp0, A, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, A, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, B, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, B, exp1, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest7() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(A, B));
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.llambda.LLambdaAutomatonExample.AUTOMATON;

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(sul, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        //System.out.println("RA IS: " + sul.toString());

        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp2 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp3 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp4 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp5 = expMealy.addState();
        FastMealyState<ParameterizedSymbol> exp6 = expMealy.addState();
        expMealy.addTransition(exp0, A, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, B, exp6, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, A, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, B, exp6, new OutputSymbol("-") {});
        expMealy.addTransition(exp2, A, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp2, B, exp5, new OutputSymbol("-") {});
        expMealy.addTransition(exp3, A, exp4, new OutputSymbol("+") {});
        expMealy.addTransition(exp3, B, exp3, new OutputSymbol("-") {});
        expMealy.addTransition(exp4, A, exp4, new OutputSymbol("+") {});
        expMealy.addTransition(exp4, B, exp4, new OutputSymbol("+") {});
        expMealy.addTransition(exp5, A, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp5, B, exp0, new OutputSymbol("+") {});
        expMealy.addTransition(exp6, A, exp2, new OutputSymbol("-") {});
        expMealy.addTransition(exp6, B, exp5, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest8() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_REGISTER, I_LOGIN, I_LOGOUT));
        Constants consts = new Constants();
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.login.LoginAutomatonExample.AUTOMATON;
        DataWordOracle dwOracle = new SimulatorOracle(sul);
        final Map<DataType, Theory> teachers = new LinkedHashMap<>();
        teachers.put(T_UID, new IntegerEqualityTheory(T_UID));
        teachers.put(T_PWD, new IntegerEqualityTheory(T_PWD));
        ConstraintSolver solver = new SimpleConstraintSolver();
        Measurements mes = new Measurements();
        MeasuringOracle mto = new MeasuringOracle(new MultiTheoryTreeOracle(
              dwOracle, teachers, new Constants(), solver), mes);
        SDTLogicOracle slo = new MultiTheorySDTLogicOracle(consts, solver);
        TreeOracleFactory hypFactory = (RegisterAutomaton hyp) ->
                new MultiTheoryTreeOracle(new SimulatorOracle(hyp), teachers,
                        new Constants(), solver);
        RaLambda ralambda = new RaLambda(mto, hypFactory, slo, consts, false, false, I_REGISTER, I_LOGIN, I_LOGOUT);
        ralambda.setSolver(solver);
        ralambda.learn();
        MutableRegisterAutomaton hyp = ralambda.getHypothesis();
        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(hyp, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        //System.out.println("RA IS: " + hyp.toString());

        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        expMealy.addTransition(exp0, I_REGISTER, exp0, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, I_LOGIN, exp0, new OutputSymbol("-") {});
        expMealy.addTransition(exp0, I_LOGOUT, exp0, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }

    @Test
    public void myTest9() {
        Alphabet<ParameterizedSymbol> alphabet = new ListAlphabet<>(Arrays.asList(I_REGISTER, I_LOGIN, I_LOGOUT));
        MutableRegisterAutomaton sul = (MutableRegisterAutomaton) de.learnlib.ralib.example.login.LoginAutomatonExample.AUTOMATON;

        MyRAtoMealyTransformer raToM = new MyRAtoMealyTransformer(sul, alphabet);
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> actMealy = raToM.getMealy();
        FastMealy<ParameterizedSymbol, ParameterizedSymbol> expMealy = new FastMealy<>(alphabet);
        FastMealyState<ParameterizedSymbol> exp0 = expMealy.addInitialState();
        FastMealyState<ParameterizedSymbol> exp1 = expMealy.addState();
        expMealy.addTransition(exp0, I_REGISTER, exp1, new OutputSymbol("-") {});
        expMealy.addTransition(exp1, I_LOGIN, exp1, new OutputSymbol("-") {});

        Collection<FastMealyState<ParameterizedSymbol>> expStates = expMealy.getStates();
        Collection<FastMealyState<ParameterizedSymbol>> actStates = actMealy.getStates();
        Iterator esIt = expStates.iterator();
        for (FastMealyState as: actStates) {
            FastMealyState es = (FastMealyState) esIt.next();
            Assert.assertEquals(as.toString(), es.toString());
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> actTrs = actMealy.getTransitions(as);
            Collection<MealyTransition<FastMealyState<ParameterizedSymbol>, FastMealyState<ParameterizedSymbol>>> expTrs = expMealy.getTransitions(es);
            Iterator etIt = expTrs.iterator();
            for (MealyTransition at: actTrs){
                MealyTransition et = (MealyTransition) etIt.next();
                Assert.assertEquals(at.getSuccessor().toString(), et.getSuccessor().toString());
                Assert.assertEquals(at.getOutput().toString(), et.getOutput().toString());
            }
        }
    }
}
