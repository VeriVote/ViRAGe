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
	
	protected void setState(QueryState state) {
		this.state = state;
	}
	
	public String getTerm() {
		return this.term;
	}
	
	protected void setTerm(String term) {
		this.term = term;
	}
	
	@Override
	public String toString() {
		String res = "(" + queryHandle + ") " + state.toString() + " " + term;
		return res;
	}
}
