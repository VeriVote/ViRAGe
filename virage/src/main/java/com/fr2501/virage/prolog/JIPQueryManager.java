package com.fr2501.virage.prolog;

import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.ugos.jiprolog.engine.JIPEngine;
import com.ugos.jiprolog.engine.JIPErrorEvent;
import com.ugos.jiprolog.engine.JIPEvent;
import com.ugos.jiprolog.engine.JIPEventListener;

// TODO: Documentation
public class JIPQueryManager implements Runnable, JIPEventListener {
	private static final Logger logger = LogManager.getLogger(JIPQueryManager.class);
	private static JIPQueryManager instance = null;
	
	private static final long DEFAULT_TIMEOUT = 10000;
	private long timeoutMillis;
	
	// Sorted List/Priority Queue might make more sense, but for now this will do.
	private Map<Integer, Long> timeouts;
	private Map<Integer, QueryResult> results;
	
	private JIPEngine engine;
	
	public void run() {
		while(true) {
			this.checkForTimeouts();
			try {
				// TODO: Think about a better solution.
				Thread.sleep(this.timeoutMillis/100);
			} catch (InterruptedException e) {
				logger.warn("Thread.sleep() was impossible.");
				e.printStackTrace();
			}
		}
	}
	
	private JIPQueryManager() {
		logger.info("Initialising JIPQueryManager.");
		
		this.timeoutMillis = JIPQueryManager.DEFAULT_TIMEOUT;
		this.timeouts = new HashMap<Integer, Long>();
		this.results = new HashMap<Integer, QueryResult>();
		this.engine = new JIPEngine();

		this.engine.addEventListener(this);
		
		Thread thread = new Thread(this, "JIPQueryManager");
		thread.start();
	}
	
	public static JIPQueryManager getInstance() {
		if(instance == null) {
			instance = new JIPQueryManager();
		}
		
		return instance;
	}
	
	public void setTimeout(long timeoutMillis) {
		this.timeoutMillis = timeoutMillis;
	}
	
	public int openQuery(String query) {
		logger.debug("Trying to open query \"" + query + "\".");
		
		int queryHandle = this.engine.openQuery(query);
		
		logger.debug("Handle: " + queryHandle + ".");
		
		long startingTime = System.currentTimeMillis();
		
		this.timeouts.put(queryHandle, startingTime + this.timeoutMillis);
		this.results.put(queryHandle, new QueryResult(queryHandle));
		
		return queryHandle;
	}
	
	public QueryResult openBlockingQuery(String query) {
		int queryHandle = this.openQuery(query);
		
		while(this.results.get(queryHandle).getState() == QueryState.PENDING);
		
		return this.results.get(queryHandle);
	}
	
	public QueryResult getResult(int queryHandle) {
		return results.get(queryHandle);
	}
	
	public void consult(InputStream is, String name) {
		this.engine.consultStream(is, name);
	}
	
	public void consultFile(String path) {
		this.engine.consultFile(path);
	}
	
	@Override
	public void closeNotified(JIPEvent arg0) {
		logger.trace("close: " + arg0.getQueryHandle());
		if((this.results.get(arg0.getQueryHandle()).getState() == QueryState.PENDING)) {
			this.updateResultState(arg0.getQueryHandle(), QueryState.FAILED);
		}
	}

	@Override
	public void endNotified(JIPEvent arg0) {
		logger.trace("end: " + arg0.getQueryHandle() + "; " + arg0.getTerm());
		if((this.results.get(arg0.getQueryHandle()).getState() == QueryState.PENDING)) {
			this.updateResultState(arg0.getQueryHandle(), QueryState.FAILED);
		}
	}

	@Override
	public void errorNotified(JIPErrorEvent arg0) {
		logger.error("error: " + arg0.getQueryHandle());
		logger.error(arg0.getError());
		
		this.updateResultState(arg0.getQueryHandle(), QueryState.ERROR);
		this.engine.closeQuery(arg0.getQueryHandle());
	}

	@Override
	public void moreNotified(JIPEvent arg0) {
		logger.trace("more: " + arg0.getQueryHandle());
		
	}

	@Override
	public void openNotified(JIPEvent arg0) {
		logger.trace("open: " + arg0.getQueryHandle());
		
	}

	@Override
	public void solutionNotified(JIPEvent arg0) {
		logger.trace("solution: " + arg0.getQueryHandle());
		logger.debug(arg0.getTerm());
		
		this.results.get(arg0.getQueryHandle()).setTerm(arg0.getTerm().toString());
		
		if(arg0.getSource().hasMoreChoicePoints(arg0.getQueryHandle())) {
			this.updateResultState(arg0.getQueryHandle(), QueryState.HAS_MORE_CHOICES);
		} else {
			this.updateResultState(arg0.getQueryHandle(), QueryState.SUCCESS);
		}
	}

	@Override
	public void termNotified(JIPEvent arg0) {
		logger.trace("term: " + arg0.getQueryHandle() + "; " + arg0.getTerm());	
	}
	
	private void checkForTimeouts() {
		long currentTime = System.currentTimeMillis();
		
		for(int queryHandle: this.timeouts.keySet()) {
			if(this.results.get(queryHandle).getState() != QueryState.PENDING) {
				continue;
			}
			
			long endTime = this.timeouts.get(queryHandle);
			
			if(endTime < currentTime) {
				logger.info("Query " + queryHandle + " timed out.");
				this.engine.closeQuery(queryHandle);
				this.updateResultState(queryHandle, QueryState.TIMEOUT);
			}
		}
	}
	
	private void updateResultState(int queryHandle, QueryState state) {
		this.results.get(queryHandle).setState(state);
	}
}
