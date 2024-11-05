package de.learnlib.ralib.learning;

import java.util.ArrayList;
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
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.automata.xml.RegisterAutomatonImporter;
import de.learnlib.ralib.data.Constants;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.dt.DTLeaf;
import de.learnlib.ralib.equivalence.IOCounterExamplePrefixFinder;
import de.learnlib.ralib.equivalence.IOCounterExamplePrefixReplacer;
import de.learnlib.ralib.equivalence.IOCounterexampleLoopRemover;
import de.learnlib.ralib.equivalence.IOEquivalenceTest;
import de.learnlib.ralib.equivalence.MyEquivalenceOracle;
import de.learnlib.ralib.learning.rastar.RaStar;
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
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.ListAlphabet;
import net.automatalib.word.Word;

public class MyNewTestFile extends RaLibTestSuite {

  @Test
  public void myTest() {
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
        RaStar lambda = new RaStar(mto, hypFactory, mlo, consts, true, actions);
            IOEquivalenceTest ioEquiv = new IOEquivalenceTest(
                    model, teachers, consts, true, actions);
        IOCounterexampleLoopRemover loops = new IOCounterexampleLoopRemover(ioOracle);
        IOCounterExamplePrefixReplacer asrep = new IOCounterExamplePrefixReplacer(ioOracle);
        IOCounterExamplePrefixFinder pref = new IOCounterExamplePrefixFinder(ioOracle);

        lambda.learn();
        MutableRegisterAutomaton hyp = lambda.getHypothesis();
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
        //WORKS. USE RALIB RASTAR OVER RALAMBDA UNTIL BUG IS FIXED IN RALAMBDA
        DefaultQuery<PSymbolInstance, Boolean> res = mO.findCounterExample(hyp, null);

        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            lambda.addCounterexample(res);
            lambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }

        hyp = lambda.getHypothesis();
        System.out.println("HYP2 IS: " + hyp.toString());
        res = null;
        res = mO.findCounterExample(hyp, null);
        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            lambda.addCounterexample(res);
            lambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }

        hyp = lambda.getHypothesis();
        System.out.println("HYP3 IS: " + hyp.toString());
        res = null;
        res = mO.findCounterExample(hyp, null);
        if (res!=null) {
            Assert.assertNotEquals(model.accepts(res.getInput()), hyp.accepts(res.getInput()));
            lambda.addCounterexample(res);
            lambda.learn();
        } else {
            System.out.println("CE IS NULL");
        }
  }
}
