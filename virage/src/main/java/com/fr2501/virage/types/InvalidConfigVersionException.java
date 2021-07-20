package com.fr2501.virage.types;

public class InvalidConfigVersionException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 6116199849357596875L;

    public InvalidConfigVersionException(final String message) {
        super(message);
    }
}
