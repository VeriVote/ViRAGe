package com.fr2501.util;

public class ProgressIndicator {
  private int phase = 0;
  
  public void advance() {
    String message = "";
    switch (this.phase) {
    case 0:
      message = "|";
      break;
    case 1:
      message = "/";
      break;
    case 2:
      message = "-";
      break;
    case 3:
      message = "\\";
      break;
    }

    phase++;
    if (phase == 4)
      phase = 0;

    System.out.print(message + "\r");
  }
}
