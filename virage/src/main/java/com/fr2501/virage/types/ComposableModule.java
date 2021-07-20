package com.fr2501.virage.types;

import java.util.List;

/**
 * A composable module (a special type of components) for the modular framework.
 *
 */
@Deprecated
public class ComposableModule extends Component {
    public ComposableModule(final ComponentType type, final String name) {
        super(type, name);
    }

    public ComposableModule(final ComponentType type, final String name,
            final List<ComponentType> parameters) {
        super(type, name, parameters);
    }
}
