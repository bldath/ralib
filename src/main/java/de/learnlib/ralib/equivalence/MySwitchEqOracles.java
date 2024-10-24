package de.learnlib.ralib.equivalence;

import java.util.Collection;

import de.learnlib.query.DefaultQuery;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.words.PSymbolInstance;


public class MySwitchEqOracles implements IOEquivalenceOracle{
    private IOEquivalenceOracle raOracle;
    private IOEquivalenceOracle raMealyOracle;


    public MySwitchEqOracles(IOEquivalenceOracle raOracle, IOEquivalenceOracle raMealyOracle) {
        this.raOracle = raOracle;
        this.raMealyOracle = raMealyOracle;
    }

    @Override
    public DefaultQuery<PSymbolInstance, Boolean> findCounterExample(RegisterAutomaton ra, Collection<? extends PSymbolInstance> clctn) {
        DefaultQuery<PSymbolInstance, Boolean> counterexample = raMealyOracle.findCounterExample(ra, clctn);
        if (counterexample == null) {
            counterexample = raOracle.findCounterExample(ra, clctn);
        }
        return counterexample;
    }
}
