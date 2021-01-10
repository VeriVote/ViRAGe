package com.fr2501.virage.test.eval;

import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import com.fr2501.virage.isabelle.IsabelleProofGenerator;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.PrologProof;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.test.unit.TestDataGenerator;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class PropertySetTest {
	private static final String FRAMEWORK_PATH = "src/test/resources/framework.pl";
	
	@Test
	public void analyzerEval() throws IOException, MalformedEPLFileException, InterruptedException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		FrameworkRepresentation framework = parser.parseFramework(new File(FRAMEWORK_PATH));
		
		TestDataGenerator generator = new TestDataGenerator(framework);
		
		long timeout = 1;
		
		boolean performBase = false;
		boolean performSPCA = false;
		
		CompositionAnalyzer base = new StandardPrologCompositionAnalyzer(framework);
		base.setTimeout(timeout);
		CompositionAnalyzer spca = new SimplePrologCompositionAnalyzer(framework);
		spca.setTimeout(timeout);
		CompositionAnalyzer acca = new AdmissionCheckPrologCompositionAnalyzer(framework);
		acca.setTimeout(timeout);
		
		List<List<Property>> allProperties = generator.getAllPossiblePropertySets();
		
		int performedTests = 0;
		int allTests = 3 * allProperties.size();
		
		int[] timeoutBaseArray = new int[11];
		int[] timeoutSPCAArray = new int[11];
		int[] timeoutACCAArray = new int[11];
		int[] sizes = new int[11];

		int timeoutBase = 0;
		int failureBase = 0;
		int successBase = 0;
		
		for(List<Property> list: allProperties) {
			if(list.size() == 0) continue;
			sizes[list.size()-1]++;
			
			if(!performBase) break;
			
			SearchResult<?> res = base.generateComposition(list);
			
			if(res.getState().equals(QueryState.TIMEOUT)) {
				timeoutBase++;
				timeoutBaseArray[list.size()-1]++;
			}
			if(res.getState().equals(QueryState.FAILED))  failureBase++;
			if(res.getState().equals(QueryState.SUCCESS)) successBase++;
			
			performedTests++;
			if(performedTests % 100 == 0) {
				System.out.println((((double) performedTests/(double) allTests) * 100) + "%");
			}
		}
		
		int timeoutSPCA = 0;
		int failureSPCA = 0;
		int successSPCA = 0;
		
		for(List<Property> list: allProperties) {
			if(!performSPCA) break;
			
			SearchResult<?> res = spca.generateComposition(list);
			
			if(res.getState().equals(QueryState.TIMEOUT)) {
				timeoutSPCA++;
				timeoutSPCAArray[list.size()-1]++;
			}
			if(res.getState().equals(QueryState.FAILED))  failureSPCA++;
			if(res.getState().equals(QueryState.SUCCESS)) {
				successSPCA++;

				
				SearchResult<?> res2 = base.generateComposition(list);
				if(res2.getState() == QueryState.TIMEOUT) {
					System.out.println(StringUtils.printCollection(list));
				}
			}
			
			performedTests++;
			if(performedTests % 100 == 0) {
				System.out.println((((double) performedTests/(double) allTests) * 100) + "%");
			}
		}
		
		int timeoutACCA = 0;
		int failureACCA = 0;
		int successACCA = 0;
		
		List<String> failures = new LinkedList<String>();
		
		for(List<Property> list: allProperties) {
			SearchResult<DecompositionTree> res = acca.generateComposition(list);
			
			if(res.getState().equals(QueryState.TIMEOUT)) {
				timeoutACCA++;
				timeoutACCAArray[list.size()-1]++;
			}
			if(res.getState().equals(QueryState.FAILED))  failureACCA++;
			if(res.getState().equals(QueryState.SUCCESS)) {
				successACCA++;
				System.out.println(res.getValue().toString());
				
				if(res.getValue().toString().contains("elim") || res.getValue().toString().contains("defer_module")) {
					failures.add(res.getValue().toString());
					continue;
				}
				IsabelleProofChecker checker = IsabelleProofChecker.getInstance(framework.getSessionName(),framework.getTheoryPath());
				
				IsabelleTheoryGenerator theoryGen = new IsabelleTheoryGenerator(framework);
				
				/* List<CompositionProof> proofs = acca.proveClaims(res.getValue(), list);
				
				File file = theoryGen.generateTheoryFile(res.getValue().toString(), proofs);
				if(!checker.verifyTheoryFile(file).getFirstValue()) {
					failures.add(res.getValue().toString());
				} */
			}
			
			performedTests++;
			if(performedTests % 100 == 0) {
				//System.out.println((((double) performedTests/(double) allTests) * 100) + "%");
			}
		}
		
		System.out.println("BASE:\t" + timeoutBase + " timeouts\t" + failureBase + " failures\t" + successBase + " successes");
		System.out.println("SPCA:\t" + timeoutSPCA + " timeouts\t" + failureSPCA + " failures\t" + successSPCA + " successes");
		System.out.println("ACCA:\t" + timeoutACCA + " timeouts\t" + failureACCA + " failures\t" + successACCA + " successes");
		
		for(int i=0; i<11; i++) {
			System.out.println(timeoutBaseArray[i] + "\t" + timeoutSPCAArray[i] + "\t" + timeoutACCAArray[i] + "\t" + sizes[i]);
		}
		
		System.out.println(StringUtils.printCollection(failures));
	}
}
