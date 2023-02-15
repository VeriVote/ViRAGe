package com.fr2501.virage.analyzer;

import java.util.List;

import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * The interface defining the methods required for analyzing and generating compositions (e.g.
 * voting rules)
 *
 * @author VeriVote
 */
public interface CompositionAnalyzer {
    /**
     * Sets the timeout in milliseconds for the implementations.
     *
     * @param millis timeout in milliseconds
     */
    void setTimeout(long millis);

    /**
     * Checks whether a given composition satisfies the specified property set.
     *
     * @param composition the composition
     * @param properties the property set
     * @return a List of {@link SearchResult}s, ordered according to the properties.
     */
    List<SearchResult<BooleanWithUncertainty>> analyzeComposition(
            DecompositionTree composition, List<Property> properties);

    /**
     * Tries to derive a new composition satisfying the specified property set.
     *
     * @param properties the property set
     * @return a {@link SearchResult} containing the result
     */
    SearchResult<DecompositionTree> generateComposition(List<Property> properties);

    /**
     * Derives the Prolog proof for a given claim. <b>May only be called on already proven
     * claims!</b>
     *
     * @param composition the composition to be used
     * @param properties the properties that shall be proven to be satisfied by the composition
     * @return a list of {@link CompositionProof}s, ordered the same way as the properties
     * @throws IllegalArgumentException if no proof can be generated (i.e. asked to prove a
     *      non-provable claim)
     */
    List<CompositionProof> proveClaims(DecompositionTree composition, List<Property> properties)
            throws IllegalArgumentException;
}
