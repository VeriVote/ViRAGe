package com.fr2501.virage.analyzer;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class SimplePrologCompositionAnalyzer implements CompositionAnalyzer {
	private static final Logger logger = LogManager.getLogger();
	private JPLFacade facade;
	private FrameworkRepresentation framework;
	
	public SimplePrologCompositionAnalyzer(FrameworkRepresentation framework) {
		logger.info("Initialising SimplePrologCompositionAnalyzer.");
		this.framework = framework;
		
		this.facade = new JPLFacade(DEFAULT_TIMEOUT);
		this.facade.consultFile(this.framework.getAbsolutePath());
	}
	
	@Override
	public void setTimeout(long millis) {
		this.facade.setTimeout(millis);
	}
	
	@Override
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, Set<Property> properties) {
		for(Property property: properties) {
			if(property.getArity() != 1) {
				throw new IllegalArgumentException();
			}
		}
		
		String votingRule = composition.toString();
		
		List<String> propertyStrings = new LinkedList<String>();
		for(Property property: properties) {
			propertyStrings.add(property.getInstantiatedString(votingRule));
		}
		String query = StringUtils.printCollection(propertyStrings);
		
		return this.facade.factQuery(query);
	}

	@Override
	public SearchResult<Set<DecompositionTree>> generateComposition(Set<Property> properties) throws Exception {
		Set<DecompositionTree> res = new HashSet<DecompositionTree>();
		
		for(Property property: properties) {
			if(property.getArity() != 1) {
				throw new IllegalArgumentException();
			}
		}
		
		// Safety measure to ensure all properties talking about the same element.
		List<String> propertyStrings = new LinkedList<String>();
		for(Property property: properties) {
			propertyStrings.add(property.getInstantiatedString("X"));
		}
		
		String query = StringUtils.printCollection(propertyStrings);
		
		SearchResult<Set<Map<String, String>>> resultSets = this.facade.query(query);
		
		if(resultSets.hasValue()) {
			for(Map<String, String> map: resultSets.getValue()) {
				if(!map.containsKey("X")) {
					// This should never happen.
					throw new Exception();
				}
				
				String solution = map.get("X");
				DecompositionTree solutionTree = new DecompositionTree(solution);
				res.add(solutionTree);
			}
				
			return new SearchResult<Set<DecompositionTree>>(resultSets.getState(), res);
		} else {
			return new SearchResult<Set<DecompositionTree>>(QueryState.FAILED, new HashSet<DecompositionTree>());
		}
	}

}
