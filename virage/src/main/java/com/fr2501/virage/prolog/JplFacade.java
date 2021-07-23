package com.fr2501.virage.prolog;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.FileUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.Atom;
import org.jpl7.Compound;
import org.jpl7.JPL;
import org.jpl7.JPLException;
import org.jpl7.PrologException;
import org.jpl7.Query;
import org.jpl7.Term;
import org.jpl7.Variable;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

/**
 * A class used to interface with JPL7.
 *
 * @author VeriVote
 */
public final class JplFacade {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(JplFacade.class);
    /**
     * Default timeout in milliseconds.
     */
    private static final long DEFAULT_TIMEOUT = 10000;

    /**
     * Counter to find new filenames.
     */
    private static int fileCounter;

    /**
     * Timeout in milliseconds.
     */
    private long timeout;

    /**
     * The Prolog parser.
     */
    private final PrologParser parser;

    /**
     * True iff ViRAGe runs in compatibility mode for SWI-Prolog 7.X.
     */
    private boolean compatibilityMode;

    /**
     * Simple constructor.
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     */
    public JplFacade() throws ExternalSoftwareUnavailableException {
        this(JplFacade.DEFAULT_TIMEOUT);
    }

    /**
     * Simple constructor.
     *
     * @param timeout query timeout
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     * @throws UnsatisfiedLinkError if SWI-Prolog library directory is not in LD_LIBRARY_PATH
     */
    public JplFacade(final long timeout)
            throws ExternalSoftwareUnavailableException, UnsatisfiedLinkError {
        this.timeout = timeout;
        this.parser = new SimplePrologParser();

        if (!ConfigReader.getInstance().hasJpl()) {
            throw new ExternalSoftwareUnavailableException();
        }

        if (!System.getenv().containsKey("LD_PRELOAD")
                || !System.getenv("LD_PRELOAD").contains("libswipl.so")) {

            throw new ExternalSoftwareUnavailableException();
        }

        try {
            JPL.setTraditional();

            JPL.init();
        } catch (final UnsatisfiedLinkError e) {
            // Unnecessary catch, but added for clarity.
            // This happens when LD_LIBRARY_PATH does not contain the SWI-Prolog library directory.
            throw e;
        }

        try {
            final Query compatQuery = new Query("subsumes_term(X,Y)");
            compatQuery.hasSolution();
        } catch (final JPLException e) {
            LOGGER.warn("Outdated version of SWI-Prolog detected. "
                    + "ViRAGe attempts to run in compatibility mode, "
                    + "but results might be unexpected. "
                    + "Especially, queries that result in Prolog terms containing variables will "
                    + "always fail.\n"
                    + "Please consider upgrading to SWI-Prolog 8.0.0 "
                    + "or newer to avoid this in the future.");
            this.compatibilityMode = true;
        }
    }

    /**
     * Returns a new Prolog variable not yet occurring in the query.
     *
     * @param queryString the query
     * @return an unused variable
     */
    public static String findUnusedVariable(final String queryString) {
        final String x = "X";

        for (int i = 1; true; i++) {
            final String unusedVariable = x + i;

            if (!queryString.contains(unusedVariable)) {
                return unusedVariable;
            }
        }
    }

    // Careful! On July, 20th 2020, SWI-Prolog rolled out an update that
    // broke this method due to JPL changing the way it prints Prolog lists.
    // This might happen again in the future. Look at the format of
    // replacementString
    // and adjust accordingly if that ever happens again.
    /**
     * Finds out the values Prolog variables need to be replaced with for unification.
     *
     * @param variable the variable containing the list of replacement
     * @param map a map containing the internal identifiers Prolog used for the variables
     * @return a map containing the replacements
     */
    public static Map<String, String> parseReplacementMap(final String variable,
            final Map<String, String> map) {
        final Map<String, String> result = new HashMap<String, String>();

        // Look like this: ['='(_108, 1)]
        // _NUMBER is an alias for a variable.
        String replacementString = map.get(variable);
        replacementString = StringUtils.removeWhitespace(replacementString);
        replacementString = replacementString.substring(1, replacementString.length() - 1);

        if (replacementString.isEmpty()) {
            // List of replacements is empty.
            return result;
        }

        final String[] replacements = replacementString.split("\\'=\\'");

        // replacements[0] is always empty, as the String starts with the splitting
        // regex.
        for (int i = 1; i < replacements.length; i++) {
            String replacement = replacements[i];

            if (replacement.endsWith(",")) {
                // Remove trailing comma, if it exists.
                replacement = replacement.substring(0, replacement.length() - 1);
            }

            // Remove bracket pair.
            replacement = replacement.substring(1, replacement.length() - 1);

            final String[] splits = replacement.split(",");

            final String key = splits[0];

            // The value might contain more commas and might thus have been split into
            // several parts.
            String value = splits[1];
            for (int j = 2; j < splits.length; j++) {
                value += "," + splits[j];
            }

            result.put(key, value);
        }

        return result;
    }

    private Term buildConjunction(final String paramString) {
        String string = paramString;
        while (paramString.startsWith("(") && paramString.endsWith(")")) {
            string = paramString.substring(0, paramString.length() - 1);
        }

        final List<String> predicates = new LinkedList<String>();

        int level = 0;
        int nextStart = 0;
        for (int i = 0; i < string.length(); i++) {
            final char cur = string.charAt(i);

            switch (cur) {
            case '(':
                level++;
                break;
            case ')':
                level--;
                break;
            case ',':
                if (level == 0) {
                    predicates.add(string.substring(nextStart, i));
                    nextStart = i + 1;
                }
                break;
            default: //NOOP
                break;
            }
        }
        predicates.add(string.substring(nextStart, string.length()));

        final List<Term> terms = new LinkedList<Term>();
        for (final String pred : predicates) {
            terms.add(this.stringToTerm(pred));
        }

        final int predCount = terms.size();

        if (predCount == 1) {
            return terms.get(0);
        }

        Compound toReturn = new Compound(",",
                new Term[] {terms.get(predCount - 2), terms.get(predCount - 1)});

        for (int i = predCount - 3; i > 0; i--) {
            toReturn = new Compound(",", new Term[] {terms.get(i), toReturn});
        }

        return toReturn;
    }

    private Query constructQuery(final String queryString) {
        if (this.compatibilityMode) {
            final Term term = this.stringToTerm(queryString);

            return new Query(term);
        } else {
            return new Query(queryString);
        }
    }

    /**
     * Consult a file so it becomes available within the JPL engine.
     *
     * @param path path to the file
     */
    public void consultFile(final String path) {
        final Query q = new Query("consult", new Term[] {new Atom(path)});
        q.hasSolution();
    }

    /**
     * Consult a file so it becomes available within the JPL engine.
     *
     * @param url the url of the file
     */
    public void consultFile(final URL url) {
        try {
            final File dest = File.createTempFile("tmp_file_" + fileCounter, ".pl");
            fileCounter++;
            dest.deleteOnExit();
            FileUtils.copyURLToFile(url, dest);
            LOGGER.debug(dest.getAbsolutePath());
            this.consultFile(dest.getAbsolutePath());
        } catch (final IOException e) {
            LOGGER.error("Something went wrong.", e);
        }
    }

    /**
     * A query not containing variables, only asking for true or false, using default timeout.
     *
     * @param queryString the query
     * @return a SearchResult representing the result of the query
     */
    public SearchResult<Boolean> factQuery(final String queryString) {
        return this.factQuery(queryString, this.timeout);
    }

    /**
     * A query not containing variables, only asking for true or false, using default timeout.
     *
     * @param queryString the query
     * @param timeout the timeout
     * @return a SearchResult representing the result of the query
     */
    public SearchResult<Boolean> factQuery(final String queryString, final long timeout) {
        final long endTime = System.currentTimeMillis() + timeout;

        final String unusedVariable = findUnusedVariable(queryString);

        int maxDepth = 0;
        while (System.currentTimeMillis() < endTime) {
            LOGGER.debug("Current maxDepth: " + maxDepth);
            final long remainingTime = endTime - System.currentTimeMillis();
            final String actualQuery = "call_with_depth_limit(" + "(" + queryString + ")" + ","
                    + maxDepth + "," + unusedVariable + ")";

            Map<String, String> result = new HashMap<String, String>();

            try {
                result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
            } catch (final PrologException e) {
                return new SearchResult<Boolean>(QueryState.ERROR, null);
            }

            if (result == null) {
                // No solution, query failed.
                return new SearchResult<Boolean>(QueryState.FAILED, false);
            }

            if (!result.containsKey(unusedVariable)) {
                // Empty Map was received, timeout.
                return new SearchResult<Boolean>(QueryState.TIMEOUT, null);
            }

            if (result.get(unusedVariable).equals("depth_limit_exceeded")) {
                // Depth limit exceeded, increase and try again.
                maxDepth++;
                continue;
            }

            if (StringUtils.isNumeric(result.get(unusedVariable))) {
                // Query succeeded.
                result.remove(unusedVariable);
                return new SearchResult<Boolean>(QueryState.SUCCESS, true);
            }

            maxDepth++;
        }

        return new SearchResult<Boolean>(QueryState.TIMEOUT, null);
    }

    public long getTimeout() {
        return this.timeout;
    }

    /**
     * A query containing variables, using default timeout.
     *
     * @param queryString the query
     * @return a SearchResult representing the result of the query
     */
    public SearchResult<Map<String, String>> iterativeDeepeningQuery(final String queryString) {
        return this.iterativeDeepeningQuery(queryString, this.timeout);
    }

    /**
     * A query containing variables.
     *
     * @param queryString the query
     * @param timeout the timeout
     * @return a SearchResult representing the result of the query
     */
    public SearchResult<Map<String, String>> iterativeDeepeningQuery(final String queryString,
            final long timeout) {
        final long endTime = System.currentTimeMillis() + timeout;

        final String unusedVariable = findUnusedVariable(queryString);

        int maxDepth = 0;
        while (System.currentTimeMillis() < endTime) {
            LOGGER.debug("Current maxDepth: " + maxDepth);
            final long remainingTime = endTime - System.currentTimeMillis();
            final String actualQuery = "call_with_depth_limit(" + "(" + queryString + ")" + ","
                    + maxDepth + "," + unusedVariable + ")";

            Map<String, String> result = new HashMap<String, String>();

            try {
                result = this.simpleQueryWithTimeout(actualQuery, remainingTime);
            } catch (final PrologException e) {
                return new SearchResult<Map<String, String>>(QueryState.ERROR, null);
            }

            if (result == null) {
                // No solution, query failed.
                return new SearchResult<Map<String, String>>(QueryState.FAILED, null);
            }

            if (!result.containsKey(unusedVariable)) {
                // Empty Map was received, timeout.
                return new SearchResult<Map<String, String>>(QueryState.TIMEOUT, null);
            }

            if (result.get(unusedVariable).equals("depth_limit_exceeded")) {
                // Depth limit exceeded, increase and try again.
                maxDepth++;
                continue;
            }

            if (StringUtils.isNumeric(result.get(unusedVariable))) {
                // Query succeeded.
                result.remove(unusedVariable);
                return new SearchResult<Map<String, String>>(QueryState.SUCCESS, result);
            }

            maxDepth++;
        }

        return new SearchResult<Map<String, String>>(QueryState.TIMEOUT, null);
    }

    /**
     * A query containing variables, disables timeout for this query and resets it afterwards.
     *
     * @param queryString the query
     * @return a SearchResult representing the result of the query
     */
    public SearchResult<Map<String, String>> iterativeDeepeningQueryWithoutTimeout(
            final String queryString) {
        final long oldTimeout = this.timeout;
        this.timeout = Integer.MAX_VALUE / 2;

        final SearchResult<Map<String, String>> res = this.iterativeDeepeningQuery(queryString);

        this.timeout = oldTimeout;
        return res;
    }

    public void setTimeout(final long timeout) {
        this.timeout = timeout;
    }

    /**
     * Simple Prolog query, returns only the first result due to Prolog limitations.
     *
     * @param queryString the query
     * @param timeout the timeout
     * @return a {@link Map} containing the result. If no solution is found within timeout, an empty
     *      Map is returned. If no solution exists, return null.
     * @throws PrologException if query is malformed.
     */
    public Map<String, String> simpleQueryWithTimeout(final String queryString, final long timeout)
            throws PrologException {
        final float timeoutInSeconds = timeout / 1000.0f;

        final String actualQuery = "call_with_time_limit(" + timeoutInSeconds + "," + "("
                + queryString + ")" + ")";

        final Query query = this.constructQuery(actualQuery);

        try {
            if (query.hasMoreSolutions()) {
                try {
                    final Map<String, Term> solution = query.nextSolution();

                    final Map<String, String> result = new HashMap<String, String>();

                    for (final String key : solution.keySet()) {
                        final String termString = solution.get(key).toString();

                        result.put(key, termString);

                    }

                    return result;
                } catch (final JPLException e) {
                    if (this.compatibilityMode) {
                        LOGGER.error(
                                "The JPL/SWI-Prolog compatibility mode "
                                        + "was unable to handle this query. "
                                        + "Please consider upgrading at least to SWI-Prolog "
                                        + "8.0.0.");

                        throw e;
                    }
                }

            } else {
                // No solution exists
                return null;
            }
        } catch (final PrologException e) {
            if (!e.getMessage().equals("PrologException: time_limit_exceeded")) {
                LOGGER.error("A Prolog error occured.");
                throw e;
            }

            return new HashMap<String, String>();
        }

        throw new IllegalArgumentException();
    }

    // This is required to ensure compatibility when using older versions of SWI-Prolog.
    // The up-to-date version of JPL and SWI-Prolog would allow using Query(String).
    private Term stringToTerm(final PrologPredicate pred) {
        if (pred.getArity() == 0) {
            if (pred.isVariable()) {
                return new Variable(pred.getName());
            } else if (StringUtils.isNumeric(pred.getName())) {
                if (pred.getName().contains(".")) {
                    return new org.jpl7.Float(Double.parseDouble(pred.getName()));
                } else {
                    return new org.jpl7.Integer(Integer.parseInt(pred.getName()));
                }
            } else {
                return new Atom(pred.getName());
            }
        } else {
            if (pred.getName().isEmpty()) {
                return this.buildConjunction(StringUtils.printCollection(pred.getParameters()));

                /*
                 * try { return Term.textToTerm(pred.toString()); } catch (JPLException e) { logger.
                 * error("The JPL/SWI-Prolog compatibility workaround cannot handle this query.");
                 * throw new IllegalArgumentException(); }
                 */
            }

            // Compound
            String name = pred.getName();

            if (name.isEmpty()) {
                name = ",";
            }

            final Term[] children = new Term[pred.getArity()];
            for (int i = 0; i < pred.getArity(); i++) {
                children[i] = this.stringToTerm(pred.getParameters().get(i));
            }

            return new Compound(name, children);
        }
    }

    private Term stringToTerm(final String predicate) {
        final PrologPredicate pred = this.parser.parsePredicate(predicate);

        return this.stringToTerm(pred);
    }

    /**
     * Checks, whether a term is a specialization of another term. Semantically similar to
     * subsumes_term\2 in SWI-Prolog
     *
     * @param generic the generic term
     * @param specific the more specific term
     * @return true if specific is a specification of generic, false otherwise.
     */
    public boolean subsumesTerm(final String generic, final String specific) {
        final String query = "subsumes_term(" + generic + "," + specific + ")";

        final SearchResult<Boolean> result = this.factQuery(query);
        if (result.hasValue()) {
            try {
                return result.getValue();
            } catch (final ValueNotPresentException e) {
                // This should never happen.
                e.printStackTrace();
            }
        }

        return false;
    }

    /**
     * Semantically similar to unifiable\3 in SWI-Prolog.
     *
     * @param a first term
     * @param b second term
     * @return a map containing the replacements
     * @throws IllegalArgumentException if a and b are not unifiable
     */
    public Map<String, String> unifiable(final String a, final String b) {
        String query = "unifiable(" + a + "," + b;

        final String unusedVariable = JplFacade.findUnusedVariable(query);
        query += "," + unusedVariable + ")";

        final SearchResult<Map<String, String>> result = this
                .iterativeDeepeningQueryWithoutTimeout(query);

        try {
            final Map<String, String> resultMap = result.getValue();

            if (!resultMap.containsKey(unusedVariable)) {
                throw new IllegalArgumentException();
            }

            final Map<String, String> replacementMap = parseReplacementMap(unusedVariable,
                    resultMap);

            final Map<String, String> res = new HashMap<String, String>();
            for (final String replacement : replacementMap.keySet()) {
                for (final String originalVariable : resultMap.keySet()) {
                    if (resultMap.get(originalVariable).equals(replacement)) {
                        res.put(originalVariable, replacementMap.get(replacement));
                    }
                }
            }

            return res;
        } catch (final ValueNotPresentException e) {
            throw new IllegalArgumentException();
        }
    }
}
