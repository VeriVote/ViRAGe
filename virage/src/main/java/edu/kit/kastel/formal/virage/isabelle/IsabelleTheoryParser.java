package edu.kit.kastel.formal.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;

/**
 * Very simple parser for Isabelle theories, nowhere near to complete.
 * <b>Warning:</b> This was set to deprecated with no explicit justification,
 * maybe handle with care.
 *
 * @author VeriVote
 */
public final class IsabelleTheoryParser {
    /**
     * The Isabelle keyword for definitions.
     */
    private static final String DEFINITION = "definition";
    /**
     * The Isabelle keyword for fun.
     */
    private static final String FUNCTION = "fun";

    private IsabelleTheoryParser() { }

    /**
     * This method simply collects the files from the given directory and returns them as a list.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     * @param dir the given directory
     * @return the list of contained files
     * @throws IllegalArgumentException if given file is not a directory
     */
    private static List<File> collectContainedFiles(final File dir) {
        if (!dir.isDirectory()) {
            throw new IllegalArgumentException();
        }
        final List<File> files = new LinkedList<File>();
        final File[] dirContent = dir.listFiles();
        if (dirContent != null) {
            for (final File file: dirContent) {
                if (file.isDirectory()) {
                    files.addAll(collectContainedFiles(file));
                } else {
                    files.add(file);
                }
            }
        }
        return files;
    }

    /**
     * Extracts all functions and definitions from a folder or a single file of Isabelle theories
     * and maps them to the file they originate from.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     *
     * @param path the path
     * @return a map containing all functions and definitions and their corresponding files
     * @throws IOException if file system interaction fails
     */
    public static Map<String, String> getAllFunctionsAndDefinitions(final String path)
            throws IOException {
        final Map<String, String> res = new HashMap<String, String>();
        final File pathFile = SystemUtils.file(path);
        List<File> files = new LinkedList<File>();
        if (pathFile.isDirectory()) {
            files = collectContainedFiles(pathFile);
        } else {
            files.add(pathFile);
        }

        final SimpleFileReader reader = new SimpleFileReader();
        for (final File file: files) {
            if (!file.getAbsolutePath().endsWith(IsabelleUtils.DOT_THY)) {
                continue;
            }
            final List<String> lines = reader.readFileByLine(file);
            for (final String line: lines) {
                if (line.startsWith(DEFINITION) || line.startsWith(FUNCTION)) {
                    final String[] splits = line.split(StringUtils.SPACE);
                    // Name of the object is second "word" on the line.
                    res.put(splits[1], file.getName());
                }
            }
        }
        return res;
    }

    /**
     * This method returns a list of all imports in the given theory file.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     *
     * @param theory the theory file
     * @return a list of the imports
     * @throws IOException if reading the file is not possible
     */
    public static List<String> getImportsFromTheoryFile(final File theory) throws IOException {
        final List<String> res = new LinkedList<String>();
        final SimpleFileReader reader = new SimpleFileReader();
        final List<String> lines = reader.readFileByLine(theory);

        for (final String line: lines) {
            if (line.contains(IsabelleUtils.IMPORTS)) {
                final String[] splits = line.split(StringUtils.SPACE);
                for (final String split: splits) {
                    if (StringUtils.removeWhitespace(split).equals(StringUtils.EMPTY)
                            || split.equals(IsabelleUtils.IMPORTS)) {
                        continue;
                    }
                    res.add(split);
                }
                return res;
            }
        }
        // No imports found.
        return res;
    }

    /**
     * Extracts a definition from an Isabelle file.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     *
     * @param name the name of the definition
     * @param theory the theory file
     * @return a String representing the definition
     * @throws IOException if file system interaction fails
     * @throws IllegalArgumentException if the definition is not found
     */
    public static String getDefinitionByName(final String name, final File theory)
            throws IOException {
        final SimpleFileReader reader = new SimpleFileReader();
        final String prefix = DEFINITION + name;
        final List<String> lines = reader.readFileByLine(theory);

        for (int i = 0; i < lines.size(); i++) {
            final String line = lines.get(i);
            if (StringUtils.removeWhitespace(line).startsWith(prefix)) {
                return line + System.lineSeparator() + lines.get(i + 1);
            }
        }
        throw new IllegalArgumentException();
    }
}
