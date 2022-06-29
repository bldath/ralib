package de.learnlib.ralib.learning.rattt;

import java.util.Map;

import de.learnlib.ralib.dt.DTLeaf;
import de.learnlib.ralib.learning.LocationComponent;
import de.learnlib.ralib.learning.SymbolicSuffix;
import de.learnlib.ralib.oracles.TreeOracle;
import de.learnlib.ralib.words.PSymbolInstance;
import net.automatalib.words.Word;

/**
 * This interface describes the methods needed in a discrimination tree during learning.
 * 
 * @author fredrik
 */
public interface DiscriminationTree {

	/**
	 * Sift a prefix into the DT to find the corresponding leaf. If add is true, also adds the prefix to the set of non-short prefixes of the corresponding leaf.
	 * 
	 * @param prefix
	 * @param oracle
	 * @param add
	 * @return the leaf corresponding to prefix
	 */
	public DTLeaf sift(Word<PSymbolInstance> prefix, boolean add);

	/**
	 * Split a prefix from a leaf node into a new leaf. Adds a new inner node using the suffix as a discriminator.
	 * 
	 * @param prefix
	 * @param suffix
	 * @param leaf
	 * @param oracle
	 */
	public void split(Word<PSymbolInstance> prefx, SymbolicSuffix suffix, DTLeaf leaf);
	
	public Map<Word<PSymbolInstance>, LocationComponent> getComponents();
}