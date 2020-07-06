package com.fr2501.virage.prolog;

import java.util.HashMap;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.Atom;
import org.jpl7.JPL;
import org.jpl7.PrologException;
import org.jpl7.Query;
import org.jpl7.Term;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.SearchResult;

/**
 * 
 * A class used to interface with JPL7.
 *
 */
public class JPLFacade {
	private static final Logger logger = LogManager.getLogger(JPLFacade.class);
	private static final long DEFAULT_TIMEOUT = 10000;
	private long timeout;
	
	public JPLFacade() {
		this(JPLFacade.DEFAULT_TIMEOUT);
	}
	
	public JPLFacade(long timeout) {
		this.timeout = timeout;
		JPL.init();
	}
	
	public void setTimeout(long timeout) {
		this.timeout = timeout;
	}
	
	/**
	 * Consult a file so it becomes available within the JPL engine.
	 * @param path path to the file
	 */
	public void consultFile(String path) {
		Query q = new Query("consult", new Term[] {new Atom(path)});
		q.hasSolution();
	}
	
	/**
	 * Simple Prolog query, returns only the first result due to Prolog limitations.
	 * 
	 * @param queryString the query
	 * @param timeout the timeout
	 * @return a {@link Map} containing the result. If no solution
	 * is found within timeout, an empty Map is returned.
	 * @throws PrologException if query is malformed.
	 */
	public Map<String, String> simpleQueryWithTimeout(String queryString, long timeout) throws PrologException {
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
			if(!e.getMessage().equals("PrologException: time_limit_exceeded")) {
				logger.error("A Prolog error occured.");
				logger.error(e);
				throw e;
			}
			
			return new HashMap<String, String>();
		}
	}
	
	/**
	 * A query not containing variables, only asking for true or false, using default timeout.
	 * @param queryString the query
	 * @return a SearchResult representing the result of the query
	 */
	public SearchResult<Boolean> factQuery(String queryString) {
		return this.factQuery(queryString, this.timeout);
	}
	
	/**
	 * A query not containing variables, only asking for true or false, using default timeout.
	 * @param queryString the query
	 * @param timeout the timeout
	 * @return a SearchResult representing the result of the query
	 */
	public SearchResult<Boolean> factQuery(String queryString, long timeout) {
		long endTime = System.currentTimeMillis() + timeout;
		
		String unusedVariable = this.findUnusedVariable(queryString);
		
		int maxDepth=0;
		while(System.currentTimeMillis() < endTime) {
			logger.debug("Current maxDepth: " + maxDepth);
			long remainingTime = endTime -System.currentTimeMillis();
			String actualQuery = "call_with_depth_limit((" + queryString + ")," + maxDepth + "," + unusedVariable + ")";
			
			Map<String, String> result = new HashMap<String, String>();
			
			try {
				result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
			} catch(PrologException e) {
				return new SearchResult<Boolean>(QueryState.ERROR, null);
			}
			
			if(result == null) {
				// No solution, query failed.
				return new SearchResult<Boolean>(QueryState.FAILED, false);
			}
			
			if(!result.containsKey(unusedVariable)) {
				// Empty Map was received, timeout.
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
	
	/**
	 * A query containing variables, using default timeout.
	 * @par)am queryString the query
	 * @return a SearchResult representing the result of the query
	 */
	public SearchResult<Map<String,String>> iterativeDeepeningQuery(String queryString) {
		return this.iterativeDeepeningQuery(queryString, this.timeout);
	}
	
	/**
	 * A query containing variables.
	 * @param queryString the query
	 * @param timeout the timeout
	 * @return a SearchResult representing the result of the query
	 */
	public SearchResult<Map<String, String>> iterativeDeepeningQuery(String queryString, long timeout) {
		long endTime = System.currentTimeMillis() + timeout;
		
		String unusedVariable = this.findUnusedVariable(queryString);
		
		int maxDepth=0;
		while(System.currentTimeMillis() < endTime) {
			logger.debug("Current maxDepth: " + maxDepth);
			long remainingTime = endTime -System.currentTimeMillis();
			String actualQuery = "call_with_depth_limit((" + queryString + ")," + maxDepth + "," + unusedVariable + ")";

			Map<String, String> result = new HashMap<String, String>();
			
			try {
				result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
			} catch(PrologException e) {
				return new SearchResult<Map<String, String>>(QueryState.ERROR, null);
			}
			
			if(result == null) {
				// No solution, query failed.
				return new SearchResult<Map<String, String>>(QueryState.FAILED, null);
			}
			
			if(!result.containsKey(unusedVariable)) {
				// Empty Map was received, timeout.
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
