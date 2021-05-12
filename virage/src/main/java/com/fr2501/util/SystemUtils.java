package com.fr2501.util;

import java.lang.reflect.Field;
import java.util.Map;

public class SystemUtils {
  // TODO This is terrible and I know it. "export" is not possible from Java?
  @SuppressWarnings("unchecked")
  public static void setUnixEnvironmentVariable(String name, String value) {
    Map<String, String> env = System.getenv();

    Field field;
    try {
      field = env.getClass().getDeclaredField("m");

      field.setAccessible(true);
      ((Map<String, String>) field.get(env)).put(name, value);

      // TODO Check and notify
    } catch (NoSuchFieldException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (SecurityException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IllegalArgumentException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IllegalAccessException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
}
