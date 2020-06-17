package com.fr2501.virage.prolog;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.FrameworkRepresentation;

//TODO: Documentation
public class JIPFacade {
	private Logger logger = LogManager.getLogger(JIPFacade.class);
	private JIPQueryManager manager;
	
	private FrameworkRepresentation framework;
	private InputStream frameworkStream;
	
	public JIPFacade(FrameworkRepresentation framework) {
		logger.info("Initialising JIPFacade.");
		
		this.framework = framework;
		this.frameworkStream = this.convertFrameworkToInputStream();
		
		this.manager = JIPQueryManager.getInstance();
		
		this.manager.consult(this.frameworkStream, "framework");
		this.manager.consultFile("src/main/resources/meta_interpreter.pl");
	}
	
	public void setTimeout(long millis) {
		this.manager.setTimeout(millis);
	}
	
	public QueryResult simpleQuery(List<String> parts) {
		String query = "?- ";
		
		query += StringUtils.printCollection(parts);
		
		query += ".";
		
		return this.sendQuery(query);
	}
	
	public QueryResult limitedQuery(List<String> parts) {
		String query = "?- breadth_first_search((";
		
		query += StringUtils.printCollection(parts);
		
		query += ")," + "R";
		
		query += ").";
		
		return this.sendQuery(query);
	}
	
	private QueryResult sendQuery(String query) {
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
