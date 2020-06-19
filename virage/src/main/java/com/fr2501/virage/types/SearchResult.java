package com.fr2501.virage.types;

import com.fr2501.virage.prolog.QueryState;

//TODO: Document
public class SearchResult<T> {
	private QueryState state;
	private T value;
	
	public SearchResult(QueryState state, T value) {
		this.state = state;
		this.value = value;
	}
	
	public QueryState getState() {
		return this.state;
	}
	
	public T getValue() throws Exception {
		if(!this.hasValue()) {
			throw new ValueNotPresentException();
		}
		return this.value;
	}
	
	public boolean hasValue() {
		return (this.value != null);
	}
}
