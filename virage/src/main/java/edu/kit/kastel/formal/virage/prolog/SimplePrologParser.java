package edu.kit.kastel.formal.virage.prolog;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;

/**
 * A simple implementation of the {@link PrologParser} interface.
 *
 * @author VeriVote
 */
public final class SimplePrologParser implements PrologParser {

    private static String sanitizeClause(final String clause) {
        return clause.replace(StringUtils.SPACE, StringUtils.EMPTY)
                .replace(System.lineSeparator(), StringUtils.EMPTY)
                .replace(StringUtils.TAB, StringUtils.EMPTY);
    }

    private List<PrologPredicate> splitAntecedents(final String antecedentString) {
        if (antecedentString.isEmpty()) {
            throw new IllegalArgumentException();
        }
        final List<PrologPredicate> res = new LinkedList<PrologPredicate>();
        String currentPredicate = StringUtils.EMPTY;
        int level = 0;
        for (int i = 0; i < antecedentString.length(); i++) {
            final char current = antecedentString.charAt(i);
            if (current == StringUtils.LEFT_PAREN) {
                level++;
            } else if (current == StringUtils.RIGHT_PAREN) {
                level--;
                if (level < 0) {
                    throw new IllegalArgumentException();
                }
            }
            if (level == 0) {
                if (current == StringUtils.COMMA_CHAR || i == antecedentString.length() - 1) {
                    if (i == antecedentString.length() - 1) {
                        currentPredicate += current;
                    }
                    res.add(parsePredicate(currentPredicate));
                    currentPredicate = StringUtils.EMPTY;
                    continue;
                }
            }
            currentPredicate += current;
        }
        if (level != 0) {
            throw new IllegalArgumentException();
        }
        return res;
    }

    @Override
    public PrologPredicate parsePredicate(final String string) {
        if (string.isEmpty()) {
            throw new IllegalArgumentException();
        }
        final StringBuilder name = new StringBuilder();
        final List<PrologPredicate> parameters = new LinkedList<PrologPredicate>();
        String currentPredicate = StringUtils.EMPTY;
        int level = 0;
        for (int i = 0; i < string.length(); i++) {
            final char current = string.charAt(i);
            if (current == StringUtils.LEFT_PAREN) {
                level++;
                if (level == 1) {
                    continue;
                }
            } else if (current == StringUtils.RIGHT_PAREN) {
                level--;
                if (level < 0) {
                    throw new IllegalArgumentException();
                }
                if (level == 0) {
                    continue;
                }
            } else {
                if (level == 0) {
                    name.append(current);
                } else if (level == 1) {
                    if (current == StringUtils.COMMA_CHAR) {
                        parameters.add(parsePredicate(currentPredicate));
                        currentPredicate = StringUtils.EMPTY;
                        continue;
                    }
                }
            }
            if (level > 0) {
                currentPredicate += current;
            }
        }
        if (!currentPredicate.isEmpty()) {
            parameters.add(parsePredicate(currentPredicate));
        }
        if (level != 0) {
            throw new IllegalArgumentException();
        }
        // Set of superfluous brackets
        if (name.length() == 0 && parameters.size() == 1) {
            return parameters.get(0);
        }
        return new PrologPredicate(name.toString(), parameters);
    }

    @Override
    public PrologClause parseSingleClause(final String clause) {
        if (clause.isEmpty()) {
            throw new IllegalArgumentException();
        }
        String sanitizedClause = sanitizeClause(clause);
        if (sanitizedClause.charAt(sanitizedClause.length() - 1) != StringUtils.DOT_CHAR) {
            throw new IllegalArgumentException();
        }
        sanitizedClause = sanitizedClause.replace(StringUtils.PERIOD, StringUtils.EMPTY);
        final String[] cedents = sanitizedClause.split(NECK);
        if (cedents.length > 2) {
            throw new IllegalArgumentException();
        }
        final PrologPredicate succedent = parsePredicate(cedents[0]);
        if (cedents.length == 1) {
            return new PrologClause(succedent);
        }
        final String antecedentString = cedents[1];
        final List<PrologPredicate> antecedents;
        antecedents = splitAntecedents(antecedentString);
        return new PrologClause(succedent, antecedents);
    }
}
