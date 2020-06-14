package com.fr2501.virage.prolog;

// TODO: Documentation
public class QueryResult {
	private int queryHandle;
	private QueryState state;
	private String term;
	
	public QueryResult(int queryHandle) {
		this.queryHandle = queryHandle;
		this.state = QueryState.PENDING;
	}
	
	public QueryState getState() {
		return this.state;
	}
	
	public void setState(QueryState state) {
		this.state = state;
	}
	
	public String getTerm() {
		return this.term;
	}
	
	public void setTerm(String term) {
		this.term = term;
	}
}
