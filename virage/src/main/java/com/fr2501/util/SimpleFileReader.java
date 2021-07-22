package com.fr2501.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Utility class to read files line by line.
 *
 */
public class SimpleFileReader {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(SimpleFileReader.class.getName());

    /**
     * The file reader.
     */
    private BufferedReader reader;

    /**
     * Reads the specified file line by line.
     *
     * @param file the file to be read.
     * @return a list containing the lines of that file.
     * @throws IOException if reading the file is not possible.
     */
    public List<String> readFileByLine(final File file) throws IOException {
        LOGGER.info("Trying to read from file \"" + file + "\"");

        final List<String> res = new LinkedList<String>();

        try {
            this.reader = new BufferedReader(new FileReader(file));

            String line = this.reader.readLine();
            while (line != null) {
                res.add(line);
                line = this.reader.readLine();
            }
        } catch (final FileNotFoundException e) {
            LOGGER.error("Invalid file.");
            throw e;
        } catch (final IOException e) {
            LOGGER.error("Something went wrong while reading the file.");
            throw e;
        } finally {
            try {
                if (this.reader != null) {
                    this.reader.close();
                }
            } catch (final IOException e) {
                LOGGER.warn("Closing the FileWriter was impossible.");
            }
        }

        return res;
    }

    /**
     * Reads the specified file.
     *
     * @param file the file to be read.
     * @return a String representing the contents of that file.
     * @throws IOException if reading the file is not possible.
     */
    public String readFile(final File file) throws IOException {
        final List<String> list = this.readFileByLine(file);

        String res = "";
        for (final String s : list) {
            res += s + "\n";
        }

        return res;
    }
}
