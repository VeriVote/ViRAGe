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
	public SearchResult<DecompositionTree> generateComposition(Set<Property> properties) throws Exception {
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
		
		SearchResult<Map<String, String>> result = this.facade.iterativeDeepeningQuery(query);
		
		if(result.hasValue()) {
			Map<String, String> resultMap = result.getValue();
			
			if(!resultMap.containsKey("X")) {
				// This should never happen.
				throw new Exception();
			}
				
			String solution = resultMap.get("X");
			DecompositionTree solutionTree = new DecompositionTree(solution);
				
			return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
		} else {
			return new SearchResult<DecompositionTree>(result.getState(), null);
		}
	}

}
