package com.fr2501.virage.core;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.jobs.VirageAnalyzeJob;
import com.fr2501.virage.jobs.VirageDummyJob;
import com.fr2501.virage.jobs.VirageExitJob;
import com.fr2501.virage.jobs.VirageExtractJob;
import com.fr2501.virage.jobs.VirageGenerateJob;
import com.fr2501.virage.jobs.VirageIsabelleGenerateJob;
import com.fr2501.virage.jobs.VirageIsabelleGenerateScalaJob;
import com.fr2501.virage.jobs.VirageIsabelleVerifyJob;
import com.fr2501.virage.jobs.VirageJob;
import com.fr2501.virage.jobs.VirageJobState;
import com.fr2501.virage.jobs.VirageParseJob;
import com.fr2501.virage.jobs.VirageProveJob;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComposableModule;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A simple command line interface for ViRAGe.
 *
 */
public class VirageCommandLineInterface implements VirageUserInterface {
  private final Logger logger = LogManager.getLogger(VirageCommandLineInterface.class);
  private Scanner scanner;
  private VirageCore core;

  private CommandLineProgressIndicator clpi;

  private static final String SEPARATOR 
      = "###########################################################";
  private static final String BANNER = "#\n"
      + "# Y88b      / ,e, 888~-_        e       e88~~\\           \n"
      + "#  Y88b    /   \"  888   \\      d8b     d888      e88~~8e \n"
      + "#   Y88b  /   888 888    |    /Y88b    8888 __  d888  88b\n"
      + "#    Y888/    888 888   /    /  Y88b   8888   | 8888__888\n"
      + "#     Y8/     888 888_-~    /____Y88b  Y888   | Y888    ,\n"
      + "#      Y      888 888 ~-_  /      Y88b  \"88__/   \"88___/ \n#";

  private Thread thread;

  protected VirageCommandLineInterface(VirageCore core) {
    logger.info("Initialising VirageCommandLineInterface.");

    this.printSeparator();
    System.out.println(BANNER);
    this.printSeparator();

    DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
    LocalDateTime now = LocalDateTime.now();
    System.out.println("# Version " + VirageCore.getVersion() + ", Timestamp: " + dtf.format(now));
    System.out.println("# If you need help, type \"help\", \"h\" or \"?\".");
    
    this.printSeparator();
    
    System.out.println("# Reading configuration from " 
        + ConfigReader.getInstance().getConfigPath() + ".");
    System.out.println("#");
    
    List<String> propertyNames = new LinkedList<String>();
    for (String s : ConfigReader.getInstance().getAllProperties().keySet()) {
      propertyNames.add(s);
    }
    Collections.sort(propertyNames);
    
    for (String s : propertyNames) {
      System.out.println(("# " + s.toUpperCase() + ":\n#\t" 
          + ConfigReader.getInstance().getAllProperties().get(s)).replaceAll(";", ";\n#\t"));
    }

    this.printSeparator();

    ConfigReader.getInstance().checkAvailabilityAndPrintVersions();

    this.printSeparator();

    this.scanner = new Scanner(System.in);
    this.core = core;

    this.clpi = new CommandLineProgressIndicator();
  }

  private void printSeparator() {
    System.out.println(SEPARATOR);
  }

  /**
   * Similar to run(), but creates its own new thread.
   */
  public void launch() {
    this.thread = new Thread(this, "vcli");
    this.thread.start();
  }

  @Override
  public void run() {
    logger.info("Started VirageCommandLineInterface.");

    String defaultPath = "./src/test/resources/framework.pl";

    String path;

    boolean firstTry = true;

    while (true) {
      if (ConfigReader.getInstance().hasPathToRootFile() && firstTry &&
          this.requestConfirmation("Configuration option \"ISABELLE_PATH_TO_ROOT_FILE\" " 
                + "is specified as \"" + ConfigReader.getInstance().getPathToRootFile() + "\". " 
                + "Use this Isabelle session to load a compositional framework?")) {
        path = ConfigReader.getInstance().getPathToRootFile();

        firstTry = false;
      } else {
        path = this.requestString("Please input the path to an (E)PL file or "
            + "an Isabelle ROOT file. (default: " + defaultPath + ")");
      }

      if (path.equals("")) {
        path = defaultPath;
      }

      if (this.extractAndOrParseFramework(path) != null) {
        break;
      }
    }

    while (true) {
      String arg = this.requestString("Do you want to (g)enerate a composition, (a)nalyze one, "
          + "(p)rove a claim,\n" + "generate (I)sabelle code or generate (S)cala code?");

      VirageJob<?> job = null;

      // TODO Refactor to enum
      if (arg.equals("g")) {
        job = this.createGenerationQuery();
      } else if (arg.equals("a")) {
        job = this.createAnalysisQuery();
      } else if (arg.equals("p")) {
        job = this.createProofQuery();
      } else if (arg.equals("I")) {
        job = this.createIsabelleQuery();
      } else if (arg.equals("S")) {
        job = this.createCodeGenerationQuery();
      } else {
        System.out.println("Please try again.");
        continue;
      }

      this.core.submit(job);
      // VirageCore is intended to work on jobs asynchronously
      // and that is perfectly possible. It just does not make
      // too much sense when using a CLI, so it is disabled.
      job.waitFor();
    }
  }

  private FrameworkRepresentation extractAndOrParseFramework(String path) {
    FrameworkRepresentation framework = null;
    VirageParseJob parseJob;

    if (!path.endsWith(".pl")) {
      if (path.endsWith("ROOT")) {
        path = path.substring(0, path.length() - "ROOT".length());
      }
      
      File file = new File(path);
      if (file.isDirectory()) {
        File[] files = file.listFiles();

        outer: for (File child : files) {
          if (child.getAbsolutePath().endsWith(".pl")) {
            while (true) {
              boolean conf = this.requestConfirmation(
                  "(E)PL file \"" + child.getAbsolutePath() + "\" found. " + "Do you want to "
                      + "skip generation and use this file instead? This saves time if no " 
                      + "changes to the Isabelle theories were made since the file was "
                      + "created.");

              if (conf) {
                return this.extractAndOrParseFramework(child.getAbsolutePath());
              } else {
                continue outer;
              }
            }
          }
        }
      }

      if (!ConfigReader.getInstance().hasIsabelle()) {
        System.out
            .println("Isabelle is not available. Please install or supply an (E)PL-file directly.");

        return null;
      }

      String sessionName;
      if (ConfigReader.getInstance().hasSessionName()
          && this.requestConfirmation("Configuration option \"ISABELLE_SESSION_NAME\" is specified " 
              + "as \"" + ConfigReader.getInstance().getSessionName() 
              + "\". Is this value correct?")) {

        sessionName = ConfigReader.getInstance().getSessionName();

        this.displayMessage("Extracting framework from session \"" + sessionName + "\" at " + path
            + ".\n" + "This might take some time.");
      } else {        
        sessionName = this.requestString("Please input the name of "
            + "the session within this directory.");
      }

      VirageExtractJob extractJob = new VirageExtractJob(this, path, sessionName);
      this.core.submit(extractJob);
      extractJob.waitFor();
      if (extractJob.getState().equals(VirageJobState.FAILED)) {
        return null;
      }
      framework = extractJob.getResult();

      parseJob = new VirageParseJob(this, new File(framework.getAbsolutePath()));
    } else {
      parseJob = new VirageParseJob(this, new File(path));
    }

    this.core.submit(parseJob);
    parseJob.waitFor();
    
    // Unelegant, but prevents race condition where user prompt is printed
    // before the result.
    try {
      Thread.sleep(100);
    } catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

    if (!parseJob.getState().equals(VirageJobState.FINISHED)) {
      return null;
    }

    return parseJob.getResult();
  }

  @Override
  public void notify(VirageJob<?> job) {
    System.out.println(job.presentResult() + "\n");
  }

  private VirageGenerateJob createGenerationQuery() {
    String propertyString = this.requestPropertyString();

    List<String> properties = StringUtils.separate(",", propertyString);

    VirageGenerateJob res = new VirageGenerateJob(this, properties);
    return res;
  }

  private VirageAnalyzeJob createAnalysisQuery() {
    String composition = this.requestCompositionString();

    String propertyString = this.requestPropertyString();

    List<String> properties = StringUtils.separate(",", propertyString);

    VirageAnalyzeJob res = new VirageAnalyzeJob(this, composition, properties);
    return res;
  }

  private VirageProveJob createProofQuery() {
    String composition = this.requestCompositionString();

    String propertyString = this.requestPropertyString();

    return this.createProofQuery(composition, propertyString);
  }

  private VirageProveJob createProofQuery(String composition, String propertyString) {
    List<String> properties = StringUtils.separate(",", propertyString);

    VirageProveJob res = new VirageProveJob(this, composition, properties);
    return res;
  }

  private VirageJob<?> createIsabelleQuery() {
    final String composition = this.requestCompositionString();

    final String propertyString = this.requestPropertyString();

    String defaultPath = "./target/generated-sources/";
    String outputPath = this.requestString("Please specify a directory for the "
        + "generated theory file. (default: " + defaultPath + ")");
    if (outputPath.equals("")) {
      outputPath = defaultPath;
    }

    boolean verify = true;
    while (true) {
      if (this.requestConfirmation("Shall the resulting theory file be verified automatically?")) {
        break;
      } else {
        verify = false;
        break;
      }
    }

    VirageProveJob proveJob = this.createProofQuery(composition, propertyString);
    this.core.submit(proveJob);
    proveJob.waitFor();

    if (proveJob.getState() == VirageJobState.FAILED) {
      logger.warn("Proving the given claims failed.");
      return new VirageDummyJob(this);
    }

    List<List<CompositionProof>> proofLists = proveJob.getResult();
    List<CompositionProof> bestProof = new LinkedList<CompositionProof>();
    for (List<CompositionProof> proof : proofLists) {
      if (proof.size() > bestProof.size()) {
        bestProof = proof;
      }
    }

    VirageIsabelleGenerateJob generateJob = new VirageIsabelleGenerateJob(this, composition,
        bestProof, outputPath);
    if (!verify) {
      return generateJob;
    }
    this.core.submit(generateJob);
    generateJob.waitFor();

    VirageIsabelleVerifyJob verifyJob = new VirageIsabelleVerifyJob(this, generateJob.getResult());
    return verifyJob;
  }

  private VirageIsabelleGenerateScalaJob createCodeGenerationQuery() {
    String composition = this.requestCompositionString();

    VirageIsabelleGenerateScalaJob res = new VirageIsabelleGenerateScalaJob(this, composition);
    return res;
  }

  // TODO Change to return List<Property> maybe?
  private String requestPropertyString() {
    FrameworkRepresentation framework = this.core.getFrameworkRepresentation();

    String propertiesString = this.requestString("Please input the desired "
        + "properties (separated by ',') or leave empty to display available properties.");

    boolean invalid = false;

    if (!propertiesString.isEmpty()) {
      String[] propertyStrings = propertiesString.split(",");
      for (String propertyString : propertyStrings) {
        Property property = framework.getProperty(propertyString);

        if (property == null) {
          logger.error("Property \"" + propertyString + "\" is undefined.");

          invalid = true;
          break;
        }
      }
    }

    if (propertiesString.isEmpty() || invalid) {
      List<String> sortedProps = new ArrayList<String>();
      for (Property p : this.core.getFrameworkRepresentation().getProperties()) {
        sortedProps.add("\t" + p.toString() + "\n");
      }
      Collections.sort(sortedProps);

      for (String s : sortedProps) {
        System.out.print(s);
      }
      
      return this.requestPropertyString();
    }

    return propertiesString;
  }

  private String requestCompositionString() {
    boolean invalid = false;

    String compositionString = this.requestString("Please input a composition (in Prolog format) "
        + "or leave empty to display available components.");

    if (!compositionString.isEmpty()) {
      try {
        DecompositionTree.parseString(compositionString);
      } catch (Exception e) {
        logger.error("\"" + compositionString
            + "\" could not be parsed. Please check the brackets and try again.");
        invalid = true;
      }
    }

    if (compositionString.isEmpty() || invalid) {
      List<String> sortedStrings = new ArrayList<String>();
      for (Component c : this.core.getFrameworkRepresentation().getComponents()) {
        sortedStrings.add("\t" + c.toString() + "\n");
      }
      for (ComposableModule c : this.core.getFrameworkRepresentation().getComposableModules()) {
        sortedStrings.add("\t" + c.toString() + "\n");
      }
      for (CompositionalStructure c : 
          this.core.getFrameworkRepresentation().getCompositionalStructures()) {
        sortedStrings.add("\t" + c.toString() + "\n");
      }
      Collections.sort(sortedStrings);
      for (String s : sortedStrings) {
        System.out.print(s);
      }

      return this.requestCompositionString();
    }

    return compositionString;
  }
 
  /**
   * Requests confirmation from the user.
   *
   * @return true if user answers yes, false if user answers no
   */
  public boolean requestConfirmation(String message) {
    this.clpi.hide();

    boolean returnValue;

    loop: while (true) {
      String input = this.requestString(message + " (y/n)");

      switch (input) {
        case "y":
          returnValue = true;
          break loop;
        case "n":
          returnValue = false;
          break loop;
        default: break;
      }
    }

    this.clpi.show();
    return returnValue;
  }

  @Override
  public String requestString(String message) {
    while (true) {
      System.out.print(message + "\n?- ");
      
      String input = this.scanner.nextLine();

      switch (input) {
        case "?":
        case "h":
        case "help":
          this.displayHelp();
          break;
        case "exit":
          this.core.submit(new VirageExitJob(this, 0));
          try {
            Thread.sleep(10000);
          } catch (InterruptedException e) {
            // NO-OP
          } finally {
            this.displayMessage("Graceful exit was impossible. Terminating anyways.");
            System.exit(-1);
          }
          break;
        default:
          return input;
      }
    }
  }
  
  @Override
  public void displayMessage(String message) {
    System.out.println(message);
  }

  @Override
  public void displayError(String message) {
    System.err.println(message);
  }
  
  public void displayHelp() {   
    InputStream helpStream = this.getClass().getClassLoader()
        .getResourceAsStream("help.txt");
    StringWriter writer = new StringWriter();
    try {
      IOUtils.copy(helpStream, writer, StandardCharsets.UTF_8);
    } catch (IOException e) {
      logger.error("Something went wrong.", e);
      e.printStackTrace();
    }
    System.out.println(writer.toString());
  }
}
