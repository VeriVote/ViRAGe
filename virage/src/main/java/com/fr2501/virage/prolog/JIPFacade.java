package com.fr2501.virage.prolog;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.FrameworkRepresentation;

//TODO: Documentation
public class JIPFacade {
	private Logger logger = LogManager.getLogger(JIPFacade.class);
	private JIPQueryManager manager;
	
	private FrameworkRepresentation framework;
	private InputStream frameworkStream;
	
	public JIPFacade(FrameworkRepresentation framework) {
		logger.debug("Initialising JIPFacade");
		
		this.frameworkStream = this.convertFrameworkToInputStream();
		this.manager.consult(this.frameworkStream, "framework");
		this.manager.consultFile("src/main/resources/meta_interpreter.pl");
		
		this.manager = JIPQueryManagerFactory.getJIPQueryManager(framework);
	}
	
	public void setTimeout(long millis) {
		this.manager.setTimeout(millis);
	}
	
	public QueryResult iterativeDeepeningQuery(List<String> parts) {
		String query = "?- mi_id(g(";
		
		for(String part: parts) {
			query += part + ",";
		}
		
		// Remove last ','.
		query = query.substring(0, query.length()-1);
		
		query += ")).";
		
		int queryHandle = this.manager.openQuery(query);
		
		QueryResult result = this.manager.getResult(queryHandle);
		while(this.manager.getResult(queryHandle).getState() == QueryState.PENDING) {
			result = this.manager.getResult(queryHandle);
		}
		
		return result;
	}
	
	public QueryResult treeQuery(List<String> parts) {
		String query = "?- mi_tree(g(";
		
		for(String part: parts) {
			query += part + ",";
		}
		
		// Remove last ','.
		query = query.substring(0, query.length()-1);
		
		query += "), T).";
		
		int queryHandle = this.manager.openQuery(query);
		
		QueryResult result = this.manager.getResult(queryHandle);
		while(this.manager.getResult(queryHandle).getState() == QueryState.PENDING) {
			result = this.manager.getResult(queryHandle);
		}
		
		return result;
	}
	
	private InputStream convertFrameworkToInputStream() {
		String clauseString = "";
		
		for(CompositionRule cr: this.framework.getCompositionRules()) {
			clauseString += cr.getClause().toString() + "\n";
		}
		
		InputStream is = new ByteArrayInputStream(clauseString.getBytes());
		
		return is;
	}
}
