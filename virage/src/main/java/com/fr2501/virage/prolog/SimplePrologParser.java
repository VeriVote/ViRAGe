package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

/**
 * A simple implementation of the {@link PrologParser} interface.
 *
 * @author VeriVote
 */
public final class SimplePrologParser implements PrologParser {
    @Override
    public PrologPredicate parsePredicate(final String string) {
        if (string.isEmpty()) {
            throw new IllegalArgumentException();
        }

        final StringBuilder name = new StringBuilder("");
        final List<PrologPredicate> parameters = new LinkedList<PrologPredicate>();
        String currentPredicate = "";
        int level = 0;

        for (int i = 0; i < string.length(); i++) {
            final char current = string.charAt(i);

            if (current == '(') {
                level++;
                if (level == 1) {
                    continue;
                }
            } else if (current == ')') {
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
                    if (current == ',') {
                        parameters.add(this.parsePredicate(currentPredicate));
                        currentPredicate = "";
                        continue;
                    }
                }
            }

            if (level > 0) {
                currentPredicate += current;
            }
        }

        if (!currentPredicate.isEmpty()) {
            parameters.add(this.parsePredicate(currentPredicate));
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

        String sanitizedClause = this.sanitizeClause(clause);
        if (sanitizedClause.charAt(sanitizedClause.length() - 1) != '.') {
            throw new IllegalArgumentException();
        }
        sanitizedClause = sanitizedClause.replace(".", "");

        final String[] cedents = sanitizedClause.split(":-");

        if (cedents.length > 2) {
            throw new IllegalArgumentException();
        }

        final PrologPredicate succedent = this.parsePredicate(cedents[0]);
        if (cedents.length == 1) {
            return new PrologClause(succedent);
        }

        final String antecedentString = cedents[1];
        final List<PrologPredicate> antecedents;
        antecedents = this.splitAntecedents(antecedentString);

        return new PrologClause(succedent, antecedents);
    }

    private String sanitizeClause(final String clause) {
        String res = clause.replace(" ", "");
        res = res.replace(System.lineSeparator(), "");
        res = res.replace("\t", "");

        return res;
    }

    private List<PrologPredicate> splitAntecedents(final String antecedentString) {
        if (antecedentString.isEmpty()) {
            throw new IllegalArgumentException();
        }
        final List<PrologPredicate> res = new LinkedList<PrologPredicate>();
        String currentPredicate = "";
        int level = 0;

        for (int i = 0; i < antecedentString.length(); i++) {
            final char current = antecedentString.charAt(i);

            if (current == '(') {
                level++;
            } else if (current == ')') {
                level--;
                if (level < 0) {
                    throw new IllegalArgumentException();
                }
            }

            if (level == 0) {
                if (current == ',' || i == antecedentString.length() - 1) {
                    if (i == antecedentString.length() - 1) {
                        currentPredicate += current;
                    }

                    res.add(this.parsePredicate(currentPredicate));
                    currentPredicate = "";
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
}
