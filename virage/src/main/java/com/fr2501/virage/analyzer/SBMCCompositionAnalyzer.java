package com.fr2501.virage.analyzer;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Semaphore;
import java.util.logging.Level;
import java.util.logging.Logger;

import com.fr2501.util.ThreadSignal;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

import edu.pse.beast.datatypes.electioncheckparameter.ElectionCheckParameter;
import edu.pse.beast.datatypes.electiondescription.ElectionDescription;
import edu.pse.beast.highlevel.BEASTCommunicator;
import edu.pse.beast.highlevel.MainApplicationClass;
import edu.pse.beast.highlevel.javafx.CheckChildTreeItem;
import edu.pse.beast.highlevel.javafx.ChildTreeItem;
import edu.pse.beast.highlevel.javafx.GUIController;
import edu.pse.beast.highlevel.javafx.ParentTreeItem;
import edu.pse.beast.propertychecker.PropertyChecker;
import edu.pse.beast.propertychecker.Result;
import edu.pse.beast.types.cbmctypes.inputplugins.Preference;
import edu.pse.beast.types.cbmctypes.outputplugins.CandidateList;
import javafx.application.Platform;

public class SBMCCompositionAnalyzer extends AdmissionCheckPrologCompositionAnalyzer {
	public SBMCCompositionAnalyzer(FrameworkRepresentation framework) throws IOException {
		super(framework);
		
		final class BEASTMainRunner implements Runnable {
			@Override
			public void run() {
				MainApplicationClass.main(new String[0]);
			}	
		}
		
		Thread beastThread = new Thread(new BEASTMainRunner());
		beastThread.start();
	}
	
	@Override
	public List<SearchResult<BooleanWithUncertainty>> analyzeComposition(DecompositionTree composition, List<Property> properties) {
		List<SearchResult<BooleanWithUncertainty>> res = new LinkedList<SearchResult<BooleanWithUncertainty>>();
		
		for(Property property: properties) {
			List<Property> singleProp = new LinkedList<Property>();
			singleProp.add(property);
			
			List<SearchResult<BooleanWithUncertainty>> superResults = super.analyzeComposition(composition, singleProp);
			
			// Single property, single result.
			SearchResult<BooleanWithUncertainty> superResult = superResults.get(0);
			
			if(superResult.hasValue() && superResult.getValue() == BooleanWithUncertainty.TRUE) {
				res.add(superResult);
			} else {
				res.add(this.runSBMCCheck(composition, property));
			}
			
		}
		
		return res;
	}
	
	private SearchResult<BooleanWithUncertainty> runSBMCCheck(DecompositionTree composition, Property property) {
		final BlockingQueue<SearchResult<BooleanWithUncertainty>> queue = new LinkedBlockingQueue<SearchResult<BooleanWithUncertainty>>();
		
		// Make sure BEAST is started and ready.
		GUIController tmpController = null;
		while(tmpController == null) {
			tmpController = GUIController.getController();
		}
		final GUIController controller = tmpController;
		
		Platform.runLater(new Runnable() {
			@Override
			public synchronized void run() {
				SearchResult<BooleanWithUncertainty> res = new SearchResult<BooleanWithUncertainty>(QueryState.FAILED, null);
				
				ElectionDescription elecDesc = new ElectionDescription("tmp", new Preference(), new CandidateList());

				String code = "unsigned int[C] voting(unsigned int amountVotes, unsigned int votes[amountVotes][C]) {\n\treturn votes[0];\n}";
				String[] lines = code.split("\n");
				elecDesc.setCode(code);
				elecDesc.setLockedPositions(0,lines[0].length(),code.length()-1);
				elecDesc.setNotNew();
				
				controller.getCodeArea().setNewElectionDescription(elecDesc);
				
				controller.getPostConditionsArea().replaceText("(1==0);");
				
				for(ChildTreeItem child: controller.getProperties().get(0).getSubItems()) {
					if(child instanceof CheckChildTreeItem) {
						child.setSelected(true);
					} else {
						child.setSelected(false);
					}
				}
				
				elecDesc = controller.getElectionDescription();
				List<ParentTreeItem> properties = controller.getProperties();
				ElectionCheckParameter parameter = controller.getParameter();
				
				if(!BEASTCommunicator.checkForErrors(elecDesc, properties)) {
					PropertyChecker checker = new PropertyChecker("CBMC");
					
					List<Result> results = checker.checkPropertiesForDescription(elecDesc, properties, parameter);
					
					//while(results == null) { /* no-op */ };
					
					// There will always be exactly one result, so this is fine.
					Result result = results.get(0);
					
					while(true) {
						synchronized(result) {
							if(result.isFinished()) {
								break;
							}
						}
					}
					
					boolean success = result.isSuccess();
					
					if(success) {
						res.setValue(BooleanWithUncertainty.MAYBE_NO_COUNTEREXAMPLE_FOUND);
					} else {
						res.setValue(BooleanWithUncertainty.FALSE);
					}
					
					res.setState(QueryState.SUCCESS);
					
					try {
						queue.put(res);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		});
		
		try {
			return queue.take();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		// TODO
		return null;
	}
}
