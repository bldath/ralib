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
    private long abstractionResets = 0L;
    private long randomWalkResets = 0L;
    private long abstractionInputs = 0L;
    private long randomWalkInputs = 0L;
    private long totalAbsResets = 0L;
    private long totalAbsInputs = 0L;

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
                totalAbsResets = ((MyEquivalenceOracle) raMealyOracle).getResets();
                totalAbsInputs = ((MyEquivalenceOracle) raMealyOracle).getInputs();
                counterexample = raOracle.findCounterExample(ra, clctn);
                if (counterexample == null) {
                	System.out.println("");
                }
            } else {
                abstractionResets = ((MyEquivalenceOracle) raMealyOracle).getResets();
                abstractionInputs = ((MyEquivalenceOracle) raMealyOracle).getInputs();
            }
        } else {
            if (counterexample == null) {
                //useRAEqOracle = false;
            	System.out.println("");
            } else {
            	randomWalkResets = ((IORandomWalk) raOracle).getResets() - totalAbsResets;
            	randomWalkInputs = ((IORandomWalk) raOracle).getInputs() - totalAbsInputs;
                counterexample = raMealyOracle.findCounterExample(ra, clctn);
            }
        }
        return counterexample;
    }

    public void useRAEqOracleOrNot(Boolean b) {
        this.useRAEqOracle = b;
    }
    
    public void printResults() {
    	System.out.println("Abstraction Resets: " + abstractionResets);
    	System.out.println("Abstraction Inputs: " + abstractionInputs);
    	System.out.println("Random Walk Resets: " + randomWalkResets);
    	System.out.println("Random Walk Inputs: " + randomWalkInputs);
    	System.out.println("Abstraction Resets (incl. final): " + totalAbsResets);
    	System.out.println("Abstraction Inputs (incl. final): " + totalAbsInputs);
    	System.out.println("Random Walk Resets (incl. final): " + (((IORandomWalk) raOracle).getResets() - totalAbsResets));
    	System.out.println("Random Walk Inputs (incl. final): " + (((IORandomWalk) raOracle).getInputs() - totalAbsInputs));
    }

}
