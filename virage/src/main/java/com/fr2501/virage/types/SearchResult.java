package com.fr2501.virage.types;

import com.fr2501.virage.prolog.QueryState;

/**
 * A class encapsulating the result of a search. Since searches can fail in general, some wrapper is
 * required.
 *
 * @param <T> the type of the encapsulated value
 */
public final class SearchResult<T> {
    private QueryState state;
    private T value;

    public SearchResult(final QueryState state, final T value) {
        this.state = state;
        this.value = value;
    }

    public synchronized QueryState getState() {
        return this.state;
    }

    /**
     * Simple getter.
     *
     * @return the value
     * @throws ValueNotPresentException if no value is present
     */
    public T getValue() throws ValueNotPresentException {
        if (!this.hasValue()) {
            throw new ValueNotPresentException();
        }
        return this.value;
    }

    /**
     * Simple getter.
     *
     * @return true if {@code this} has a value different from null, false otherwise
     */
    public boolean hasValue() {
        return (this.value != null);
    }

    public synchronized void setState(final QueryState state) {
        this.state = state;
    }

    public void setValue(final T value) {
        this.value = value;
    }

    @Override
    public String toString() {
        String res = this.state.toString();

        if (this.hasValue()) {
            res += ": " + this.value.toString();
        }

        return res;
    }
}
