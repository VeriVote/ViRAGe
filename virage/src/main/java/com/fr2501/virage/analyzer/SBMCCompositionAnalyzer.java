package com.fr2501.virage.analyzer;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;

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
import edu.pse.beast.highlevel.BEASTCommunicator;
import edu.pse.beast.highlevel.MainApplicationClass;
import edu.pse.beast.highlevel.javafx.GUIController;
import edu.pse.beast.highlevel.javafx.ParentTreeItem;
import edu.pse.beast.highlevel.javafx.PublicParentTreeItem;
import edu.pse.beast.propertychecker.PropertyChecker;
import edu.pse.beast.propertychecker.Result;

public class SBMCCompositionAnalyzer extends AdmissionCheckPrologCompositionAnalyzer {
	public SBMCCompositionAnalyzer(FrameworkRepresentation framework) throws IOException {
		super(framework);
	}
	
	@Override
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, List<Property> properties) {
		PropertyChecker checker = new PropertyChecker("CBMC");
		
		final class BEASTMainRunner implements Runnable {
			@Override
			public void run() {
				// TODO Auto-generated method stub
				MainApplicationClass.main(new String[0]);
			}	
		}
		
		Thread beastThread = new Thread(new BEASTMainRunner());
		beastThread.start();
		
		// TODO
		String codeString = "";
        ElectionDescription electionDesc = ElectionDescriptionFactory.getElectionDescriptionFromString(codeString);
        
        List<Integer> amountOfVoters = new LinkedList<Integer>();
        List<Integer> amountOfCandidates = new LinkedList<Integer>();
        List<Integer> amountOfSeats = new LinkedList<Integer>();
        ElectionCheckParameter parameter = new ElectionCheckParameter(amountOfVoters, amountOfCandidates, 
        		amountOfSeats, new TimeOut(TimeUnit.MILLISECONDS, DEFAULT_TIMEOUT), 1, "");
		
		for(Property property: properties) {
			List<Property> singleProperty = new LinkedList<Property>();
			singleProperty.add(property);
			
			SearchResult<Boolean> result = super.analyzeComposition(composition, singleProperty);
			
			if(!result.hasValue() || !result.getValue()) {
				// No exact solution was found, try SBMC.
		        List<ParentTreeItem> propertiesForSBMC = new LinkedList<ParentTreeItem>();
		        
		        // Build ParentTreeItem for the Property.
		        // This seems to be really tedious, as it's essentially
		        // generating useless UI elements just to be able to
		        // call one of BEAST's functions, but I've not found
		        // any other way.
		        FormalPropertiesDescription preCondition = new FormalPropertiesDescription("");
		        FormalPropertiesDescription postCondition = new FormalPropertiesDescription("");
		        FormalPropertiesDescription boundedVars  = new FormalPropertiesDescription("");
		        
		        PreAndPostConditionsDescription desc = new PreAndPostConditionsDescription("", preCondition,
		        		postCondition, boundedVars, null);
		        ParentTreeItem propertyItem = new PublicParentTreeItem(desc);
		        
		        propertiesForSBMC.add(propertyItem);
		        
		        List<Result> sbmcResult = checker.checkPropertiesForDescription(electionDesc, propertiesForSBMC, parameter);
			}
		}
		
		BEASTCommunicator a = null;
		
		return null;
	}

	@Override
	public SearchResult<DecompositionTree> generateComposition(List<Property> properties) {
		// TODO Auto-generated method stub
		return null;
	}
}
