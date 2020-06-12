package com.fr2501.virage.prolog;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Enumeration;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.ugos.jiprolog.engine.JIPEngine;
import com.ugos.jiprolog.engine.JIPTerm;

//TODO: Documentation
public class JIPFacade {
	private Logger logger = LogManager.getLogger(JIPFacade.class);
	private JIPEngine engine;
	
	public JIPFacade() {
		this.engine = new JIPEngine();
		this.engine.addEventListener(new SimpleJIPEventListener());
	}
	
	public void consultFrameworkRepresentation(FrameworkRepresentation framework) throws InterruptedException {
		String clauseString = "";
		
		for(CompositionRule cr: framework.getCompositionRules()) {
			clauseString += cr.getClause().toString() + "\n";
		}
		
		logger.debug(clauseString);
		
		InputStream is = new ByteArrayInputStream(clauseString.getBytes());
		
		this.engine.consultStream(is, "is");
		this.engine.openQuery("?- non_blocking(X),non_electing(X).");
		Thread.sleep(2);
		
		System.out.println(this.engine.getSearchPath());
		this.engine.closeAllQueries();
	}
}
