package edu.kit.kastel.formal.util;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Collection;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Utility class to write files line by line.
 *
 * @author VeriVote
 */
public class SimpleFileWriter {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(SimpleFileWriter.class.getName());

    /**
     * The FileWriter.
     */
    private FileWriter writer;

    /**
     * Writes Collection to file, with every item on its own line, creates file if needed.
     *
     * @param path the file to be written to
     * @param collection the collection
     */
    public void writeToFile(final String path, final Collection<?> collection) {
        try {
            this.writer = new FileWriter(SystemUtils.file(path), StandardCharsets.UTF_8);
            for (final Object o: collection) {
                this.writer.write(o.toString() + System.lineSeparator());
            }
        } catch (final IOException e) {
            LOGGER.error(e);
        } finally {
            try {
                this.writer.close();
            } catch (final IOException e) {
                LOGGER.warn(e);
            }
        }
    }

    /**
     * Writes String to file.
     *
     * @param path the file to be written to
     * @param contents the String to be written to the file
     */
    public void writeToFile(final String path, final String contents) {
        try {
            final File file = SystemUtils.file(path);
            this.writer = new FileWriter(file, StandardCharsets.UTF_8);
            this.writer.write(contents);
        } catch (final IOException e) {
            LOGGER.error(e);
        } finally {
            try {
                this.writer.close();
            } catch (final IOException e) {
                LOGGER.warn(e);
            }
        }
    }
}
