package com.fr2501.virage.analyzer;

import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.prolog.JIPFacade;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

public class SimplePrologCompositionAnalyzer implements CompositionAnalyzer {
	private static final Logger logger = LogManager.getLogger();
	private JIPFacade facade;
	
	public SimplePrologCompositionAnalyzer(FrameworkRepresentation framework) {
		logger.debug("Initialising SimplePrologCompositionAnalyzer.");
		
		this.facade = new JIPFacade(framework);
	}
	
	@Override
	public void setTimeout(long millis) {
		this.facade.setTimeout(millis);
	}
	
	@Override
	public SearchResult analyzeComposition(DecompositionTree composition, Set<Property> properties) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SearchResult generateComposition(Set<Property> properties) {
		// TODO Auto-generated method stub
		return null;
	}

}
