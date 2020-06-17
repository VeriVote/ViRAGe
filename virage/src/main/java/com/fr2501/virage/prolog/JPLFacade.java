package com.fr2501.virage.prolog;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jpl7.Atom;
import org.jpl7.Query;
import org.jpl7.Term;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class JPLFacade {
	private FrameworkRepresentation framework;
	private long timeout;
	
	public JPLFacade(FrameworkRepresentation framework, long timeout) {
		this.timeout = timeout;
		
		this.framework = framework;
		this.consultFile(this.framework.getAbsolutePath());
	}
	
	public void setTimeout(long timeout) {
		this.timeout = timeout;
	}
	
	public void consultFile(String path) {
		Query q = new Query("consult", new Term[] {new Atom(path)});
		q.hasSolution();
	}
	
	public Set<Map<String, String>> simpleQuery(String queryString) {
		return this.simpleQuery(queryString, this.timeout);
	}
	
	public Set<Map<String, String>> simpleQuery(String queryString, long timeout) {
		Set<Map<String, String>> results = new HashSet<Map<String, String>>();
		long endTime = System.currentTimeMillis() + timeout;
		
		Query query = new Query(queryString);
		
		while(query.hasMoreSolutions()) {
			if(endTime < System.currentTimeMillis()) {
				query.close();
				break;
			}
			
			Map<String, Term> solution = query.nextSolution();
			Map<String, String> result = new HashMap<String, String>();
			
			for(String key: solution.keySet()) {
				String termString = solution.get(key).toString();
				
				result.put(key, termString);
				results.add(result);
			}
		}
		
		return results;
	}
	
	public Set<Map<String, String>> iterativeDeepeningQuery(String queryString) {
		return this.iterativeDeepeningQuery(queryString, this.timeout);
	}
	
	public Set<Map<String, String>> iterativeDeepeningQuery(String queryString, long timeout) {
		Set<Map<String, String>> results = new HashSet<Map<String, String>>();
		long startTime = System.currentTimeMillis();
		long endTime = System.currentTimeMillis() + timeout;
		
		// TODO
		String unusedVariable = "R";
		
		int maxDepth=0;
		while(System.currentTimeMillis() < endTime) {
			long elapsedTime = System.currentTimeMillis() - startTime;
			
			String actualQuery = "call_with_depth_limit((" + queryString + ")," + maxDepth + "," + unusedVariable + ")";
			
			Set<Map<String, String>> result = this.simpleQuery(actualQuery, timeout-elapsedTime);
			
			boolean anyExceeded = false;
			for(Map<String, String> map: result) {
				if(!map.containsKey(unusedVariable)) {
					// TODO: What does this mean?
					continue;
				}
				
				if(map.get(unusedVariable).equals("depth_limit_exceeded")) {
					anyExceeded = true;
				}
				
				if(StringUtils.isNumeric(map.get(unusedVariable))) {
					map.remove(unusedVariable);
					results.add(map);
					continue;
				}
				
				maxDepth++;
			}
			
			if(!anyExceeded && result.isEmpty()) {
				// No branch went over limit and no branch succeeded, query is unsolvable.
				return results;
			}
		}
		
		return results;
	}
}
