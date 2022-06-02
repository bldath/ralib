package de.learnlib.ralib.dt;

import de.learnlib.ralib.data.PIV;
import de.learnlib.ralib.learning.SymbolicDecisionTree;
import de.learnlib.ralib.oracles.TreeQueryResult;

public class DTBranch {

		private SymbolicDecisionTree sdt;
		
		private DTNode child;
		
		public DTBranch(SymbolicDecisionTree sdt, DTNode child) {
			this.sdt = sdt;
			this.child = child;
		}
		
		public DTNode getChild() {
			return child;
		}
		
		public boolean matches(SymbolicDecisionTree other, PIV renaming) {
			return sdt.isEquivalent(other, renaming);
		}
		
		public boolean matches(TreeQueryResult tqr) {
			return sdt.isEquivalent(tqr.getSdt(), tqr.getPiv());
		}
}