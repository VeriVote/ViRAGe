package com.fr2501.virage.types;

import java.util.List;

/**
 * 
 * A composable module (a special type of components) for the modular framework.
 *
 */
public class ComposableModule extends Component {
  public ComposableModule(ComponentType type, String name) {
    super(type, name);
  }

  public ComposableModule(ComponentType type, String name, List<ComponentType> parameters) {
    super(type, name, parameters);
  }
}
