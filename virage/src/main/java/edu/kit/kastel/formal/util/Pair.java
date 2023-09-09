package edu.kit.kastel.formal.util;

/**
 * Simple wrapper for a pair of two values.
 *
 * @author VeriVote
 *
 * @param <S> type of the first value
 * @param <T> type of the second value
 *
 */
public final class Pair<S, T> {
    /**
     * First value.
     */
    private final S first;

    /**
     * Second value.
     */
    private final T second;

    /**
     * Simple constructor.
     *
     * @param firstValue the first value
     * @param secondValue the second value
     */
    public Pair(final S firstValue, final T secondValue) {
        this.first = firstValue;
        this.second = secondValue;
    }

    /**
     * Returns the first value of the pair.
     *
     * @return the first value
     */
    public S getFirstValue() {
        return this.first;
    }

    /**
     * Returns the second value of the pair.
     *
     * @return the second value
     */
    public T getSecondValue() {
        return this.second;
    }

    @Override
    public String toString() {
        String firstString = StringUtils.EMPTY;
        String secondString = StringUtils.EMPTY;
        if (this.first != null) {
            firstString = this.first.toString();
        }
        if (this.second != null) {
            secondString = this.second.toString();
        }
        return StringUtils.parenthesize(firstString, StringUtils.SPACE + secondString);
    }
}
