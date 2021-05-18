package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * The main entry point
 *
 */
public class VirageMain {
  private final static Logger logger = LogManager.getLogger(VirageMain.class);

  private final static String _NAME = "ViRAGe";
  private final static String _VERSION = "0.1.0";
  private final static String _BANNER = "\n"
      + "Y88b      / ,e, 888~-_        e       e88~~\\            \n"
      + " Y88b    /   \"  888   \\      d8b     d888      e88~~8e  \n"
      + "  Y88b  /   888 888    |    /Y88b    8888 __  d888  88b \n"
      + "   Y888/    888 888   /    /  Y88b   8888   | 8888__888 \n"
      + "    Y8/     888 888_-~    /____Y88b  Y888   | Y888    , \n"
      + "     Y      888 888 ~-_  /      Y88b  \"88__/   \"88___/  \n";
                                                           
  public static void main(String[] args) {
    System.out.println(_BANNER);
    System.out.println("--- " + _NAME + " version " + _VERSION);

    try {
      VirageCore core = new VirageCore(args);
      Thread coreThread = new Thread(core, "core");
      coreThread.start();

      while (true)
        ;
    } catch (Exception e) {
      logger.fatal("An unrecoverable error has occurred.", e);
      logger.fatal("The program will now terminate.");
    }

    System.out.println("--- Terminating " + _NAME + ".");
    System.exit(1);
  }
}
