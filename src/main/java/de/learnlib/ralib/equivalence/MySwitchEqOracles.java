package de.learnlib.ralib.equivalence;

import java.util.Collection;

import de.learnlib.query.DefaultQuery;
import de.learnlib.ralib.automata.RegisterAutomaton;
import de.learnlib.ralib.words.PSymbolInstance;


public class MySwitchEqOracles implements IOEquivalenceOracle{
    private IOEquivalenceOracle raOracle;
    private IOEquivalenceOracle raMealyOracle;
    private Boolean useRAEqOracle = false;
    DefaultQuery<PSymbolInstance, Boolean> counterexample = null;


    public MySwitchEqOracles(IOEquivalenceOracle raOracle, IOEquivalenceOracle raMealyOracle) {
        this.raOracle = raOracle;
        this.raMealyOracle = raMealyOracle;
    }

    @Override
    public DefaultQuery<PSymbolInstance, Boolean> findCounterExample(RegisterAutomaton ra, Collection<? extends PSymbolInstance> clctn) {
        if (!useRAEqOracle) {
            counterexample = raMealyOracle.findCounterExample(ra, clctn);
            if (counterexample==null) {
                useRAEqOracle = true;
                counterexample = raOracle.findCounterExample(ra, clctn);
            }
        } else {
            counterexample = raMealyOracle.findCounterExample(ra, clctn);
            if (counterexample == null) {
                //useRAEqOracle = false;
            }
        }
        return counterexample;
    }

    public void useRAEqOracleOrNot(Boolean b) {
        this.useRAEqOracle = b;
    }

}
