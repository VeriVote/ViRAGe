package com.fr2501.util;

/**
 * Simple wrapper for a pair of two values.
 *
 * @param <S> type of the first value
 * @param <T> type of the second value
 */
public class Pair<S, T> {
    private S firstValue;
    private T secondValue;

    public Pair(S firstValue, T secondValue) {
        this.firstValue = firstValue;
        this.secondValue = secondValue;
    }

    public S getFirstValue() {
        return this.firstValue;
    }

    public T getSecondValue() {
        return this.secondValue;
    }

    @Override
    public String toString() {
        String first = "null";
        String second = "null";

        if (this.firstValue != null) {
            first = this.firstValue.toString();
        }

        if (this.secondValue != null) {
            second = this.secondValue.toString();
        }

        return "(" + first + ", " + second + ")";

    }
}
