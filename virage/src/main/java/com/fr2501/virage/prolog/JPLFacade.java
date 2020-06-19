package com.fr2501.virage.prolog;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.Atom;
import org.jpl7.PrologException;
import org.jpl7.Query;
import org.jpl7.Term;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.SearchResult;

// TODO: Document
public class JPLFacade {
	private static final Logger logger = LogManager.getLogger(JPLFacade.class);
	private long timeout;
	
	public JPLFacade(long timeout) {
		this.timeout = timeout;
	}
	
	public void setTimeout(long timeout) {
		this.timeout = timeout;
	}
	
	public void consultFile(String path) {
		Query q = new Query("consult", new Term[] {new Atom(path)});
		q.hasSolution();
	}
	
	public Map<String, String> simpleQueryWithTimeout(String queryString, long timeout) {
		float timeoutInSeconds = ((float) timeout) / 1000.0f;
		
		String actualQuery = "call_with_time_limit(" + timeoutInSeconds + ",(" + queryString + "))";
		
		Query query = new Query(actualQuery);
		
		try {
			if(query.hasMoreSolutions()) {
				Map<String, Term> solution = query.nextSolution();
				Map<String, String> result = new HashMap<String, String>();
				
				for(String key: solution.keySet()) {
					String termString = solution.get(key).toString();
					
					result.put(key, termString);
					
				}

				return result;
			} else {
				return null;
			}
		} catch(PrologException e) {
			return new HashMap<String, String>();
		}
	}
	 
	public SearchResult<Boolean> factQuery(String queryString) {
		return this.factQuery(queryString, this.timeout);
	}
	
	public SearchResult<Boolean> factQuery(String queryString, long timeout) {
		long endTime = System.currentTimeMillis() + timeout;
		
		String unusedVariable = this.findUnusedVariable(queryString);
		
		int maxDepth=0;
		while(System.currentTimeMillis() < endTime) {
			logger.debug("Current maxDepth: " + maxDepth);
			long remainingTime = endTime -System.currentTimeMillis();
			String actualQuery = "call_with_depth_limit((" + queryString + ")," + maxDepth + "," + unusedVariable + ")";
			
			Map<String, String> result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
			
			if(result == null) {
				// No solution, query failed.
				return new SearchResult<Boolean>(QueryState.FAILED, false);
			}
			
			if(!result.containsKey(unusedVariable)) {
				// Empty Map was received, malformed query or timeout.
				// Distinction is impossible, so timeout is assumed.
				return new SearchResult<Boolean>(QueryState.TIMEOUT, null);
			}

			if(result.get(unusedVariable).equals("depth_limit_exceeded")) {
				// Depth limit exceeded, increase and try again.
				maxDepth++;
				continue;
			}

			if(StringUtils.isNumeric(result.get(unusedVariable))) {
				// Query succeeded.
				result.remove(unusedVariable);
				return new SearchResult<Boolean>(QueryState.SUCCESS, true);
			}
			
			maxDepth++;
		}
		
		return new SearchResult<Boolean>(QueryState.TIMEOUT, null);
	}
	
	public SearchResult<Map<String,String>> iterativeDeepeningQuery(String queryString) {
		return this.iterativeDeepeningQuery(queryString, this.timeout);
	}
	
	public SearchResult<Map<String, String>> iterativeDeepeningQuery(String queryString, long timeout) {
		long endTime = System.currentTimeMillis() + timeout;
		
		String unusedVariable = this.findUnusedVariable(queryString);
		
		int maxDepth=0;
		while(System.currentTimeMillis() < endTime) {
			logger.debug("Current maxDepth: " + maxDepth);
			long remainingTime = endTime -System.currentTimeMillis();
			String actualQuery = "call_with_depth_limit((" + queryString + ")," + maxDepth + "," + unusedVariable + ")";

			Map<String, String> result = new HashMap<String, String>();
			
			result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
			
			if(result == null) {
				// No solution, query failed.
				return new SearchResult<Map<String, String>>(QueryState.FAILED, null);
			}
			
			if(!result.containsKey(unusedVariable)) {
				// Empty Map was received, malformed query or timeout.
				// Distinction is impossible, so timeout is assumed.
				return new SearchResult<Map<String, String>>(QueryState.TIMEOUT, null);
			}

			if(result.get(unusedVariable).equals("depth_limit_exceeded")) {
				// Depth limit exceeded, increase and try again.
				maxDepth++;
				continue;
			}

			if(StringUtils.isNumeric(result.get(unusedVariable))) {
				// Query succeeded.
				result.remove(unusedVariable);
				return new SearchResult<Map<String, String>>(QueryState.SUCCESS, result);
			}
			
			maxDepth++;
		}
		
		return new SearchResult<Map<String, String>>(QueryState.TIMEOUT, null);
	}
	
	private String findUnusedVariable(String queryString) {
		// Feels a bit hacky, but it works.
		String unusedVariable = "X";
		while(queryString.contains(unusedVariable)) {
			unusedVariable += unusedVariable;
		}
		
		return unusedVariable;
	}
}
