package com.fr2501.virage.analyzer;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.JPL;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

/**
 * 
 * Simple implementation of the {@link CompositionAnalyzer}, using Prolog with iterative deepening.
 *
 */
public class AdmissionCheckPrologCompositionAnalyzer extends SimplePrologCompositionAnalyzer {
	private static final Logger logger = LogManager.getLogger();
	
	/**
	 * Initializes a SimplePrologCompositionAnalyzer and consults the specified framework.
	 * @param framework the framework
	 */
	public AdmissionCheckPrologCompositionAnalyzer(FrameworkRepresentation framework) {
		super(framework);
	}
	
	@Override
	protected void consultKnowledgeBase() {
		AdmissionGuardGenerator generator = new AdmissionGuardGenerator(this.framework);
		String path = "src/main/resources/framework_with_admit_guards.pl";
		
		generator.createAdmissionGuardFile(path);
		this.facade.consultFile(path);
	}

	@Override
	public SearchResult<DecompositionTree> generateComposition(Set<Property> properties) {
		for(Property property: properties) {
			if(property.getArity() != 1) {
				throw new IllegalArgumentException();
			}
		}
		
		// Safety measure to ensure all properties talking about the same element.
		List<String> admitStrings = new LinkedList<String>();
		List<String> propertyStrings = new LinkedList<String>();
		for(Property property: properties) {
			admitStrings.add(AdmissionGuardStrings.ADMITS + property.getInstantiatedString("X"));
			propertyStrings.add(property.getName() + AdmissionGuardStrings.SUFFIX + property.getInstantiatedStringWithoutName("X"));
		}
		admitStrings.addAll(propertyStrings);
		
		String query = StringUtils.printCollection(admitStrings);
		
		SearchResult<Map<String, String>> result = this.facade.iterativeDeepeningQuery(query);
		
		Map<String, String> resultMap = null;
		if(result.hasValue()) {
			try {
				resultMap = result.getValue();
			} catch(ValueNotPresentException e) {
				// This should never happen.
				logger.warn(e);
			}
				
			String solution = resultMap.get("X");
			DecompositionTree solutionTree = new DecompositionTree(solution);
				
			return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
		} else {
			return new SearchResult<DecompositionTree>(result.getState(), null);
		}
	}

}
