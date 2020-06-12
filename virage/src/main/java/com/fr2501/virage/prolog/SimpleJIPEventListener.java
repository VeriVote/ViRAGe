package com.fr2501.virage.prolog;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.ugos.jiprolog.engine.JIPErrorEvent;
import com.ugos.jiprolog.engine.JIPEvent;
import com.ugos.jiprolog.engine.JIPEventListener;
import com.ugos.jiprolog.engine.JIPTerm;

// TODO: Documentation
public class SimpleJIPEventListener implements JIPEventListener {
	private Logger logger = LogManager.getLogger(SimpleJIPEventListener.class);

	@Override
	public void closeNotified(JIPEvent arg0) {
		logger.trace("close: " + arg0.getQueryHandle());
	}

	@Override
	public void endNotified(JIPEvent arg0) {
		logger.trace("end: " + arg0.getQueryHandle());
		arg0.getSource().closeQuery(arg0.getQueryHandle());
	}

	@Override
	public void errorNotified(JIPErrorEvent arg0) {
		logger.trace("error: " + arg0.getQueryHandle());
		
		arg0.getSource().closeQuery(arg0.getQueryHandle());
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
		
		if(arg0.getSource().hasMoreChoicePoints(arg0.getQueryHandle())) {
			arg0.getSource().nextSolution(arg0.getQueryHandle());
		}
	}

	@Override
	public void termNotified(JIPEvent arg0) {
		logger.trace("term: " + arg0.getQueryHandle());
		
	}
}
