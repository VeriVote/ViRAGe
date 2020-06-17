package com.fr2501.virage.analyzer;

import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

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
