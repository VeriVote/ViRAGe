//package com.fr2501.virage.analyzer;
//
//import java.io.File;
//import java.io.IOException;
//import java.util.LinkedList;
//import java.util.List;
//import java.util.concurrent.BlockingQueue;
//import java.util.concurrent.LinkedBlockingQueue;
//import java.util.regex.Matcher;
//import java.util.regex.Pattern;
//
//import org.apache.logging.log4j.LogManager;
//import org.apache.logging.log4j.Logger;
//
//import com.fr2501.util.Pair;
//import com.fr2501.util.SimpleFileReader;
//import com.fr2501.util.SimpleFileWriter;
//import com.fr2501.virage.prolog.QueryState;
//import com.fr2501.virage.types.BooleanWithUncertainty;
//import com.fr2501.virage.types.Component;
//import com.fr2501.virage.types.ComponentType;
//import com.fr2501.virage.types.ComposableModule;
//import com.fr2501.virage.types.CompositionalStructure;
//import com.fr2501.virage.types.DecompositionTree;
//import com.fr2501.virage.types.FrameworkRepresentation;
//import com.fr2501.virage.types.Property;
//import com.fr2501.virage.types.SearchResult;
//
//import edu.pse.beast.datatypes.electioncheckparameter.ElectionCheckParameter;
//import edu.pse.beast.datatypes.electiondescription.ElectionDescription;
//import edu.pse.beast.highlevel.BEASTCommunicator;
//import edu.pse.beast.highlevel.javafx.CheckChildTreeItem;
//import edu.pse.beast.highlevel.javafx.ChildTreeItem;
//import edu.pse.beast.highlevel.javafx.GUIController;
//import edu.pse.beast.highlevel.javafx.ParentTreeItem;
//import edu.pse.beast.propertychecker.PropertyChecker;
//import edu.pse.beast.propertychecker.Result;
//import edu.pse.beast.types.cbmctypes.inputplugins.Preference;
//import edu.pse.beast.types.cbmctypes.outputplugins.CandidateList;
//import javafx.application.Platform;
//
///**
// * 
// * A {@link CompositionAnalyzer} that can use SBMC via BEAST
// *
// */
//public class SBMCCompositionAnalyzer extends AdmissionCheckPrologCompositionAnalyzer {
//  private Logger logger = LogManager.getLogger(SBMCCompositionAnalyzer.class);
//
//  private final String compositionsTemplate;
//  private final String codeFileTemplate;
//  private final String electionDescriptionForBeast;
//
//  public SBMCCompositionAnalyzer(FrameworkRepresentation framework) throws IOException {
//    super(framework);
//
//    this.compositionsTemplate = (new SimpleFileReader())
//        .readFile(new File("src/test/resources/c_implementations/compositions.template"));
//    this.codeFileTemplate = (new SimpleFileReader()).
//      readFile(new File("src/test/resources/code_file.template"));
//    this.electionDescriptionForBeast = (new SimpleFileReader())
//        .readFile(new File("src/test/resources/election_description.template"));
//
//    // FOR NOW: This is only possible via Eclipse. When executing the JAR on its
//    // own,
//    // JavaFX goes all over the place and tries to access a lot of non-existing
//    // folders
//    // within ViRAGe. This is terrible, but I don't know how to fix it. When BEAST
//    // offers a reasonable API at some point, a more robust solution might be
//    // implementable.
//    // TODO: Fix me
//    /*
//     * final class BEASTMainRunner implements Runnable {
//     * 
//     * @Override public void run() { MainApplicationClass.main(new String[0]); } }
//     * 
//     * Thread beastThread = new Thread(new BEASTMainRunner()); beastThread.start();
//     */
//  }
//
//  @Override
//  public List<SearchResult<BooleanWithUncertainty>> 
//    analyzeComposition(DecompositionTree composition,
//      List<Property> properties) {
//    List<SearchResult<BooleanWithUncertainty>> res = 
//      new LinkedList<SearchResult<BooleanWithUncertainty>>();
//
//    for (Property property : properties) {
//      List<Property> singleProp = new LinkedList<Property>();
//      singleProp.add(property);
//
//      List<SearchResult<BooleanWithUncertainty>> superResults = 
//        super.analyzeComposition(composition, singleProp);
//
//      // Single property, single result.
//      SearchResult<BooleanWithUncertainty> superResult = superResults.get(0);
//
//      if (superResult.hasValue() && superResult.getValue() == BooleanWithUncertainty.TRUE) {
//        res.add(superResult);
//      } else {
//        try {
//          File cCode = this.getCCodeFromComposition(composition);
//        } catch (Exception e) {
//          logger.error("Something went wrong while generating C code.", e);
//        }
//
//        // FOR NOW: This is only possible via Eclipse. When executing the JAR on its
//        // own,
//        // JavaFX goes all over the place and tries to access a lot of non-existing
//        // folders
//        // within ViRAGe. This is terrible, but I don't know how to fix it. When BEAST
//        // offers a reasonable API at some point, a more robust solution might be
//        // implementable.
//        // TODO: Fix me
//        // res.add(this.runSBMCCheck(composition, property));
//      }
//
//    }
//
//    return res;
//  }
//

//
//  private SearchResult<BooleanWithUncertainty> 
//    runSBMCCheck(DecompositionTree composition, Property property) {
//    final BlockingQueue<SearchResult<BooleanWithUncertainty>> queue = 
//      new LinkedBlockingQueue<SearchResult<BooleanWithUncertainty>>();
//
//    // Make sure BEAST is started and ready.
//    GUIController tmpController = null;
//    while (tmpController == null) {
//      tmpController = GUIController.getController();
//    }
//    final GUIController controller = tmpController;
//
//    final String elecDescCode = this.electionDescriptionForBeast;
//
//    Platform.runLater(new Runnable() {
//      @Override
//      public synchronized void run() {
//        SearchResult<BooleanWithUncertainty> res 
//          = new SearchResult<BooleanWithUncertainty>(QueryState.FAILED, null);
//
//        ElectionDescription elecDesc 
//          = new ElectionDescription("tmp", new Preference(), new CandidateList());
//
//        String[] lines = elecDescCode.split("\n");
//
//        int offset = 0;
//        int lockedLine = 0;
//        for (int i = 0; i < lines.length; i++) {
//          if (!lines[i].startsWith("unsigned int[C] voting")) {
//            offset += lines[i].length() + "\n".length();
//          } else {
//            lockedLine = i;
//            break;
//          }
//        }
//
//        elecDesc.setCode(elecDescCode);
//        elecDesc.setLockedPositions(offset, offset + lines[lockedLine].length(), 
//          elecDescCode.length() - 1);
//        elecDesc.setNotNew();
//
//        controller.getCodeArea().setNewElectionDescription(elecDesc);
//
//        controller.getPostConditionsArea()
//          .replaceText("(VOTES2, VOTES3) <- SPLIT(PERM(VOTES1));");
//        controller.getPreConditionsArea()
//            .replaceText("NOTEMPTY(INTERSECT(ELECT2, ELECT3))"
//              + "==> ELECT1 == INTERSECT(ELECT2, ELECT3);");
//
//        for (ChildTreeItem child : controller.getProperties().get(0).getSubItems()) {
//          if (child instanceof CheckChildTreeItem) {
//            child.setSelected(true);
//          } else {
//            child.setSelected(false);
//          }
//        }
//
//        elecDesc = controller.getElectionDescription();
//        List<ParentTreeItem> properties = controller.getProperties();
//        ElectionCheckParameter parameter = controller.getParameter();
//
//        if (!BEASTCommunicator.checkForErrors(elecDesc, properties)) {
//          PropertyChecker checker = new PropertyChecker("CBMC");
//
//          List<Result> results = checker
//            .checkPropertiesForDescription(elecDesc, properties, parameter);
//
//          // while(results == null) { /* no-op */ };
//
//          // There will always be exactly one result, so this is fine.
//          Result result = results.get(0);
//
//          while (true) {
//            synchronized (result) {
//              if (result.isFinished()) {
//                break;
//              }
//            }
//          }
//
//          boolean success = result.isSuccess();
//
//          if (success) {
//            res.setValue(BooleanWithUncertainty.MAYBE_NO_COUNTEREXAMPLE_FOUND);
//          } else {
//            res.setValue(BooleanWithUncertainty.FALSE);
//          }
//
//          res.setState(QueryState.SUCCESS);
//
//          try {
//            queue.put(res);
//          } catch (InterruptedException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//          }
//        }
//      }
//    });
//
//    try {
//      return queue.take();
//    } catch (InterruptedException e) {
//      // TODO Auto-generated catch block
//      e.printStackTrace();
//    }
//
//    // TODO
//    return null;
//  }
//}
