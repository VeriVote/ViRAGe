package com.fr2501.virage.test.eval;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.test.unit.TestDataGenerator;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Evaluation tests for {@link CompositionAnalyzer}s.
 *
 */
public class PropertySetTest {
  private static final String FRAMEWORK_PATH = "src/test/resources/framework.pl";

  /* @Test */
  /**
   * Runs several analyzers on random queries.

   * @throws IOException if file system interaction fails
   * @throws MalformedEplFileException if the input file is not valid EPL
   * @throws ExternalSoftwareUnavailableException if external software is missing
   */
  public void analyzerEval()
      throws IOException, MalformedEplFileException, ExternalSoftwareUnavailableException {
    ExtendedPrologParser parser = new SimpleExtendedPrologParser();
    FrameworkRepresentation framework = parser.parseFramework(new File(FRAMEWORK_PATH), false);

    final TestDataGenerator generator = new TestDataGenerator(framework);

    long timeout = 10;

    boolean performBase = false;
    boolean performSpca = false;

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
    int[] timeoutSpcaArray = new int[11];
    int[] timeoutAccaArray = new int[11];
    int[] sizes = new int[11];

    int timeoutBase = 0;
    int failureBase = 0;
    int successBase = 0;

    for (List<Property> list : allProperties) {
      if (list.size() == 0) {
        continue;
      }
      sizes[list.size() - 1]++;

      if (!performBase) {
        break;
      }

      SearchResult<?> res = base.generateComposition(list);

      if (res.getState().equals(QueryState.TIMEOUT)) {
        timeoutBase++;
        timeoutBaseArray[list.size() - 1]++;
      }
      if (res.getState().equals(QueryState.FAILED)) {
        failureBase++;
      }
      if (res.getState().equals(QueryState.SUCCESS)) {
        successBase++;
      }

      performedTests++;
      if (performedTests % 100 == 0) {
        System.out.println((((double) performedTests / (double) allTests) * 100) + "%");
      }
    }

    int timeoutSpca = 0;
    int failureSpca = 0;
    int successSpca = 0;

    for (List<Property> list : allProperties) {
      if (!performSpca) {
        break;
      }

      SearchResult<?> res = spca.generateComposition(list);

      if (res.getState().equals(QueryState.TIMEOUT)) {
        timeoutSpca++;
        timeoutSpcaArray[list.size() - 1]++;
      }
      if (res.getState().equals(QueryState.FAILED)) {
        failureSpca++;
      }
      if (res.getState().equals(QueryState.SUCCESS)) {
        successSpca++;

        SearchResult<?> res2 = base.generateComposition(list);
        if (res2.getState() == QueryState.TIMEOUT) {
          System.out.println(StringUtils.printCollection(list));
        }
      }

      performedTests++;
      if (performedTests % 100 == 0) {
        System.out.println((((double) performedTests / (double) allTests) * 100) + "%");
      }
    }

    int timeoutAcca = 0;
    int failureAcca = 0;
    int successAcca = 0;

    List<String> failures = new LinkedList<String>();

    for (List<Property> list : allProperties) {
      SearchResult<DecompositionTree> res = acca.generateComposition(list);

      if (res.getState().equals(QueryState.TIMEOUT)) {
        timeoutAcca++;
        timeoutAccaArray[list.size() - 1]++;
      }
      if (res.getState().equals(QueryState.FAILED)) {
        failureAcca++;
      }
      if (res.getState().equals(QueryState.SUCCESS)) {
        successAcca++;

        if (res.getValue().toString().contains("elim")
            || res.getValue().toString().contains("defer_module")) {
          failures.add(res.getValue().toString());
          continue;
        }
        /*
         * IsabelleProofChecker checker =
         * IsabelleProofChecker.getInstance(framework.getSessionName(),framework. getTheoryPath());
         * 
         * IsabelleTheoryGenerator theoryGen = new IsabelleTheoryGenerator(framework);
         * 
         * List<CompositionProof> proofs = acca.proveClaims(res.getValue(), list);
         * 
         * File file = theoryGen.generateTheoryFile(res.getValue().toString(), proofs);
         * if(!checker.verifyTheoryFile(file, framework).getFirstValue()) {
         * failures.add(res.getValue().toString()); }
         */
      }

      performedTests++;
      if (performedTests % 100 == 0) {
        // System.out.println((((double) performedTests/(double) allTests) * 100) +
        // "%");
      }
    }

    System.out.println("BASE:\t" + timeoutBase + " timeouts\t" + failureBase + " failures\t"
        + successBase + " successes");
    System.out.println("SPCA:\t" + timeoutSpca + " timeouts\t" + failureSpca + " failures\t"
        + successSpca + " successes");
    System.out.println("ACCA:\t" + timeoutAcca + " timeouts\t" + failureAcca + " failures\t"
        + successAcca + " successes");

    for (int i = 0; i < 11; i++) {
      System.out.println(timeoutBaseArray[i] + "\t" + timeoutSpcaArray[i] + "\t"
          + timeoutAccaArray[i] + "\t" + sizes[i]);
    }

    System.out.println(StringUtils.printCollection(failures));
  }
}
