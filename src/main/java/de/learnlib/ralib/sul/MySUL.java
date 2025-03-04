package de.learnlib.ralib.sul;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.learnlib.exception.SULException;
import de.learnlib.ralib.data.DataType;
import de.learnlib.ralib.data.DataValue;
import de.learnlib.ralib.data.ParValuation;
import de.learnlib.ralib.data.SymbolicDataValue.Parameter;
import de.learnlib.ralib.data.util.SymbolicDataValueGenerator;
import de.learnlib.ralib.theory.Theory;
import de.learnlib.ralib.words.DataWords;
import de.learnlib.ralib.words.PSymbolInstance;
import de.learnlib.ralib.words.ParameterizedSymbol;
import de.learnlib.sul.SUL;
import net.automatalib.word.Word;


public class MySUL implements SUL<ParameterizedSymbol, ParameterizedSymbol> {
    private final DataWordSUL dwSUL;
    private Word<PSymbolInstance> inputPref = null;
    private Word<PSymbolInstance> outputPref = null;
    private final Map<DataType, Theory> teach;

    public MySUL(Map<DataType, Theory> teachers,
            DataWordSUL dwSUL) {
        this.teach = teachers;
        this.dwSUL = dwSUL;
    }

    public Word<PSymbolInstance> getInputPrefix() {
        return this.inputPref;
    }

    public Word<PSymbolInstance> getOutputPrefix() {
        return this.outputPref;
    }

    public void
     pre() {
        inputPref = Word.epsilon();
        outputPref = Word.epsilon();
        dwSUL.pre();
    }

    public void post() {
        dwSUL.post();
    }

    private PSymbolInstance psToPsi(ParameterizedSymbol ps) {
        DataValue[] vals = new DataValue[ps.getArity()];
        SymbolicDataValueGenerator.ParameterGenerator pgen = new SymbolicDataValueGenerator.ParameterGenerator();
        ParValuation pval = new ParValuation();
        int i = 0;
        for (DataType t : ps.getPtypes()) {
            Parameter p = pgen.next(t);
            List<DataValue> old = computeOld(t, pval);
            DataValue dv = teach.get(t).getFreshValue(old);
            vals[i] = dv;
            pval.put(p, vals[i]);
            i++;
        }
        PSymbolInstance psi = new PSymbolInstance(ps, vals);
        inputPref = inputPref.append(psi);
        //System.out.println("Outputprefix: " + outputPref.toString());
        //System.out.println("Inputprefix: " + inputPref.toString());
        return psi;
    }

    public ParameterizedSymbol step(ParameterizedSymbol pi) throws SULException {
        PSymbolInstance psi = psToPsi(pi);
        PSymbolInstance pso = dwSUL.step(psi);
        //System.out.println("PSI " + psi.toString() + " PSO " + pso.toString());
        outputPref = outputPref.append(pso);
        ParameterizedSymbol po = pso.getBaseSymbol();
        return po;
    }

    private List<DataValue> computeOld(DataType t, ParValuation pval) {
    java.util.Set<DataValue> set = new java.util.LinkedHashSet<>();
    set.addAll(DataWords.valSet(inputPref, t));
    for (DataValue d : pval.values()){
        if (d.getType().equals(t)) {
            set.add(d);
            }
        }
    return new  ArrayList<>(set);
    }

    public Map<DataType, Theory> getTeachers() {
        return this.teach;
    }
    
    public long getResets() {
    	return dwSUL.getResets();
    }
    
    public long getInputs() {
    	return dwSUL.getInputs();
    }
}
