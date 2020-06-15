package com.fr2501.virage.analyzer;

import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.AnnotatedDecompositionTree;

public class SearchResult {
	private QueryState state;
	private AnnotatedDecompositionTree tree;
	
	public SearchResult(QueryState state) {
		if(state != QueryState.TIMEOUT && state != QueryState.FAILED) {
			throw new IllegalArgumentException();
		}
		
		this.state = state;
		this.tree = null;
	}
	
	public SearchResult(QueryState state, AnnotatedDecompositionTree tree) {
		this.state = state;
		this.tree = tree;
	}

	public QueryState getState() {
		return state;
	}

	public AnnotatedDecompositionTree getTree() throws Exception {
		if(this.tree == null) {
			// TODO: Better type
			throw new Exception();
		}
		
		return tree;
	}
}
