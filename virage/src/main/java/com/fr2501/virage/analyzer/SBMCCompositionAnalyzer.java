package com.fr2501.virage.analyzer;

import java.awt.Toolkit;
import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;
import java.util.logging.Logger;

import com.fr2501.util.ThreadSignal;
import com.fr2501.virage.beast.ElectionDescriptionFactory;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

import edu.pse.beast.datatypes.electioncheckparameter.ElectionCheckParameter;
import edu.pse.beast.datatypes.electioncheckparameter.TimeOut;
import edu.pse.beast.datatypes.electiondescription.ElectionDescription;
import edu.pse.beast.datatypes.propertydescription.FormalPropertiesDescription;
import edu.pse.beast.datatypes.propertydescription.PreAndPostConditionsDescription;
import edu.pse.beast.datatypes.propertydescription.SymbolicVariableList;
import edu.pse.beast.highlevel.BEASTCommunicator;
import edu.pse.beast.highlevel.MainApplicationClass;
import edu.pse.beast.highlevel.javafx.CheckChildTreeItem;
import edu.pse.beast.highlevel.javafx.ChildTreeItem;
import edu.pse.beast.highlevel.javafx.GUIController;
import edu.pse.beast.highlevel.javafx.ParentTreeItem;
import edu.pse.beast.highlevel.javafx.PublicParentTreeItem;
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
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, List<Property> properties) {
		// Make sure BEAST is started and ready.
		GUIController tmpController = null;
		while(tmpController == null) {
			tmpController = GUIController.getController();
		}
		final GUIController controller = tmpController;
		
		final ThreadSignal signal = new ThreadSignal();
		
		Platform.runLater(new Runnable() {
			@Override
			public void run() {
				ElectionDescription elecDesc = new ElectionDescription("tmp", new Preference(), new CandidateList());

				String code = "unsigned int[C] voting(unsigned int amountVotes, unsigned int votes[amountVotes][C]) {\n\treturn votes[0];\n}";
				String[] lines = code.split("\n");
				elecDesc.setCode(code);
				elecDesc.setLockedPositions(0,lines[0].length(),code.length()-1);
				elecDesc.setNotNew();
				
				System.out.println(String.join("\n", elecDesc.getComplexCode()));
				
				controller.getCodeArea().setNewElectionDescription(elecDesc);
				
				controller.getPostConditionsArea().replaceText("(1==1);");
				
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
					
					while(results == null) { /* no-op */ };
					
					boolean allDone = false;
					while(!allDone) {
						allDone = true;
						for(Result res: results) {
							allDone = allDone && res.isFinished(); 
						}
					}
					
					System.out.println(results.toString());
					signal.finish();
				}
			}
		});

		signal.waitFor();
		return null;
	}

	@Override
	public SearchResult<DecompositionTree> generateComposition(List<Property> properties) {
		// TODO Auto-generated method stub
		return null;
	}
}
