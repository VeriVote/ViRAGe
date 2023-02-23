package com.fr2501.virage.isabelle;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.fasterxml.jackson.databind.ObjectMapper;

/**
 * A factory for Isabelle events, parses the Strings given by the Isabelle CLI.
 *
 * @author VeriVote
 */
public class IsabelleEventFactory {
    /**
     * String for "OK" events.
     */
    private static final String OK_STRING = "OK";
    /**
     * String for "ERROR" events.
     */
    private static final String ERROR_STRING = "ERROR";
    /**
     * String for "NOTE" events.
     */
    private static final String NOTE_STRING = "NOTE";
    /**
     * String for "FINISHED" events.
     */
    private static final String FINISHED_STRING = "FINISHED";

    /**
     * The object mapper.
     */
    private final ObjectMapper mapper;

    /**
     * Simple constructor.
     */
    public IsabelleEventFactory() {
        this.mapper = new ObjectMapper();
    }

    /**
     * Creates an {@link IsabelleEvent} representing the event described within the given String.
     *
     * @param s the String given by the Isabelle client CLI
     * @return the corresponding event
     */
    public IsabelleEvent createEvent(final String s) {
        final Map<String, String> parameters = this.extractParameters(s);

        final IsabelleEvent res;
        if (s.startsWith(OK_STRING)) {
            res = new IsabelleOkEvent(parameters);
        } else if (s.startsWith(ERROR_STRING)) {
            res = new IsabelleErrorEvent(parameters);
        } else if (s.startsWith(NOTE_STRING)) {
            res = new IsabelleNoteEvent(parameters);
        } else if (s.startsWith(FINISHED_STRING)) {
            res = new IsabelleFinishedEvent(parameters);
        } else {
            res = new IsabelleMiscEvent();
        }

        return res;
    }

    private Map<String, String> extractParameters(final String s) {
        final Map<String, String> res = new HashMap<String, String>();
        final Pattern pattern = Pattern.compile("\\{.*\\}");
        final Matcher matcher = pattern.matcher(s);

        if (matcher.find()) {
            final String paramString = s.substring(matcher.start(), matcher.end());

            try {
                final Map<?, ?> map = this.mapper.readValue(paramString, Map.class);

                for (final Map.Entry<?, ?> e : map.entrySet()) {
                    res.put(e.getKey().toString(), e.getValue().toString());
                }

                return res;
            } catch (final IOException e) {
                // This should never happen.
                return null;
            }
        } else {
            return new HashMap<String, String>();
        }
    }
}
