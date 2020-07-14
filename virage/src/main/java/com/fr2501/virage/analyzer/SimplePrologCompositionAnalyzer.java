package com.fr2501.virage.analyzer;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.PrologProof;
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
public class SimplePrologCompositionAnalyzer implements CompositionAnalyzer {
	private static final Logger logger = LogManager.getLogger();
	
	protected static final long DEFAULT_TIMEOUT = 10000;
	protected JPLFacade facade;
	protected FrameworkRepresentation framework;
	
	/**
	 * Initializes a SimplePrologCompositionAnalyzer and consults the specified framework.
	 * @param framework the framework
	 * @throws IOException but should actually not
	 */
	public SimplePrologCompositionAnalyzer(FrameworkRepresentation framework) throws IOException {
		logger.info("Initialising SimplePrologCompositionAnalyzer.");
		this.framework = framework;
		
		this.facade = new JPLFacade(DEFAULT_TIMEOUT);
		this.consultKnowledgeBase();
	}
	
	protected void consultKnowledgeBase() throws IOException {
		this.facade.consultFile(this.framework.getAbsolutePath());
		this.facade.consultFile(this.getClass().getClassLoader().getResource("meta_interpreter.pl"));
	}
	
	@Override
	public void setTimeout(long millis) {
		this.facade.setTimeout(millis);
	}
	
	@Override
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, List<Property> properties) {		
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
	public SearchResult<DecompositionTree> generateComposition(List<Property> properties) {
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
		
		Map<String, String> resultMap = null;
		if(result.hasValue()) {
			try {
				resultMap = result.getValue();
			} catch(ValueNotPresentException e) {
				// This should never happen.
				logger.warn("This should not have happened.");
				logger.warn(e);
			}
				
			String solution = resultMap.get("X");
			DecompositionTree solutionTree = new DecompositionTree(solution);
				
			return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
		} else {
			return new SearchResult<DecompositionTree>(result.getState(), null);
		}
	}
	
	@Override
	public List<PrologProof> proveClaims(DecompositionTree composition, List<Property> properties) {
		List<PrologProof> res = new LinkedList<PrologProof>();
		
		for(Property property: properties) {
			if(property.getArity() != 1) {
				throw new IllegalArgumentException();
			}
		}
		
		String votingRule = composition.toString();
		
		for(Property property: properties) {
			// This is fine as it's the only variable.
			String proofVariable = "P";
			String query = "prove((" + property.getInstantiatedString(votingRule) + ")," + proofVariable + ")";
			
			logger.debug(query);
			
			// Disabling timeout as these queries are typically fast
			long oldTimeout = this.facade.getTimeout();
			this.facade.setTimeout(Long.MAX_VALUE/2);
			SearchResult<Map<String,String>> result = this.facade.iterativeDeepeningQuery(query);
			this.facade.setTimeout(oldTimeout);
			
			if(result.hasValue()) {
				try {
					Map<String,String> map = result.getValue();
					
					if(map.containsKey(proofVariable)) {
						logger.debug(map.get(proofVariable));
						
						res.add(PrologProof.createProofFromString(map.get(proofVariable)));
					} else {
						throw new IllegalArgumentException();
					}
				} catch (ValueNotPresentException e) {
					throw new IllegalArgumentException();
				}
			} else {
				throw new IllegalArgumentException();
			}
		}
		
		return res;
	}
}
