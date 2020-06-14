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
	private JIPQueryManager manager;
	
	public JIPFacade(FrameworkRepresentation framework) {
		this.manager = JIPQueryManagerFactory.getJIPQueryManager(framework);
		this.manager.setTimeout(1000);
	}
}
