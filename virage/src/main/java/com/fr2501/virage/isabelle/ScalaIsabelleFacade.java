package com.fr2501.virage.isabelle;

import static scala.concurrent.ExecutionContext.global;

import java.io.File;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.IsabelleBuildFailedException;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.control.Isabelle.Setup;
import de.unruh.isabelle.mlvalue.ListConverter;
import de.unruh.isabelle.mlvalue.MLFunction;
import de.unruh.isabelle.mlvalue.MLFunction0;
import de.unruh.isabelle.mlvalue.MLValue;
import de.unruh.isabelle.mlvalue.MLValue.Converter;
import de.unruh.isabelle.mlvalue.StringConverter;
import de.unruh.isabelle.mlvalue.Tuple2Converter;
import de.unruh.isabelle.pure.Context;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.Thm;
import scala.Some;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.concurrent.ExecutionContext;
import scala.concurrent.Future;

/**
 * A facade for scala-isabelle by Dominique Unruh.
 *
 * @author VeriVote
 */
public final class ScalaIsabelleFacade {
    /**
     * The Isabelle instance.
     */
    private static Isabelle isabelle;
    /**
     * The list converter for scala-isabelle.
     */
    private static final ListConverter<String> LIST_CONVERTER = new ListConverter<String>(
            new JavaStringConverter());
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();
    /**
     * The string converter for scala-isabelle.
     */
    private static final JavaStringConverter STRING_CONVERTER = new JavaStringConverter();

    /**
     * The "pair-to-list" converter for scala-isabelle.
     */
    private static final ListConverter<Tuple2<String, String>> PAIR_TO_LIST_CONVERTER
        = new ListConverter<Tuple2<String, String>>(
            new Tuple2Converter<String, String>(STRING_CONVERTER, STRING_CONVERTER));

    /**
     * All functions and definitions extracted from a given session.
     */
    private Map<String, Map<String, String>> functionsAndDefinitions;

    /**
     * The session directory.
     */
    private final String sessionDir;
    /**
     * The session name.
     */
    private final String sessionName;

    /**
     * The scala-isabelle setup object.
     */
    private final Setup setup;
    /**
     * All theorems of a given session.
     */
    private Map<String, Map<String, String>> theorems;

    /**
     * Names of all theories within the given session.
     */
    private final Set<String> theoryNames;

    /**
     * Simple constructor.
     *
     * @param sessionDirValue the session base directory
     * @param sessionNameValue the session name
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the build process fails
     */
    public ScalaIsabelleFacade(final String sessionDirValue, final String sessionNameValue)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        this.sessionDir = new File(sessionDirValue).getAbsolutePath();
        this.sessionName = sessionNameValue;

        this.theoryNames = new HashSet<String>();

        final List<Path> sessionDirs = new LinkedList<Path>();
        sessionDirs.add(Path.of(this.sessionDir));

        this.setup = new Setup(Path.of(ConfigReader.getInstance().getIsabelleHome()),
                sessionNameValue,
                new Some<Path>(Path.of(ConfigReader.getInstance().getIsabelleSessionDir())),
                Path.of(sessionDirValue),
                JavaConverters.asScalaIteratorConverter(sessionDirs.iterator()).asScala().toSeq(),
                true, true /*try verbose first*/, null, null /* try to get away with null first */);

        try {
            isabelle = new Isabelle(this.setup);
            // Scala has no checked Exceptions and the constructor is not annotated.
            // Therefore, javac thinks that the (implicitly checked) IsabelleBuildException
            // cannot be thrown.
        } catch (/* IsabelleBuild */final Exception e) {
            e.printStackTrace();
            LOGGER.error("Building "
                    + "session " + sessionNameValue
                    + " failed. Restarting ViRAGe "
                    + "or building"
                    + " the session manually within Isabelle "
                    + "might help. If the session is supposed"
                    + " to generate documentation, "
                    + "texlive is required!");
            throw new IsabelleBuildFailedException();
        }
        this.init();
    }

    /**
     * Triggers the Isabelle build process for a given session.
     *
     * @param sessionDir the session directory
     * @param sessionName the session name
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the build process fails
     */
    public static void buildSession(final String sessionDir, final String sessionName)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {

        if (isabelle != null) {
            return;
        }

        final List<Path> sessionDirs = new LinkedList<Path>();
        sessionDirs.add(Path.of(new File(sessionDir).getAbsolutePath()));

        final Setup setup = new Setup(Path.of(ConfigReader.getInstance().getIsabelleHome()),
                sessionName,
                new Some<Path>(Path.of(ConfigReader.getInstance().getIsabelleSessionDir())),
                Path.of(sessionDir),
                JavaConverters.asScalaIteratorConverter(sessionDirs.iterator()).asScala().toSeq(),
                true, true /*try verbose first*/, null, null /* try to get away with null first */);

        try {
            isabelle = new Isabelle(setup);
            isabelle.destroy();
            // Scala has no checked Exceptions and the constructor is not annotated.
            // Therefore, javac thinks that the (implicitly checked) IsabelleBuildException
            // cannot be thrown.
        } catch (/* IsabelleBuild */final Exception e) {
            LOGGER.error("Building session " + sessionName
                    + " failed. Restarting ViRAGe or building"
                    + " the session manually within Isabelle might help. If the session is supposed"
                    + " to generate documentation, texlive is required!");
            throw new IsabelleBuildFailedException();
        }

    }

    /**
     * Extracts functions and definitions from a given framework in Isabelle.
     */
    public void extractFunctionsAndDefinitions() {
        this.functionsAndDefinitions = new HashMap<String, Map<String, String>>();
        final MLFunction<Theory, scala.collection.immutable.List<String>> mlFunToExtractAllNames
            = MLValue
                .compileFunction(
                        "fn thy => " + "(map " + "(fn x => " + "(#description " + "(hd "
                                + "(snd(x))" + "))) (filter (fn x => " + "(String.isPrefix "
                                + "(Context.theory_name thy) " + "(snd (fst (x))"
                                + ")))(Defs.all_specifications_of (Theory.defs_of thy))))",
                        ScalaIsabelleFacade.isabelle, global(), Implicits.theoryConverter(),
                        LIST_CONVERTER);

        final String extractConstFunString = "#constants (Consts.dest (Sign.consts_of thy))";

        final String toStringFunction = "(fn x => let fun typ_to_string "
                + "(x: Basic_Term.typ): string = case x of\n"
                + "Type x => \"(\" ^ (fst x) ^ String.concat (map (typ_to_string) (snd x)) "
                + "^ \")\"\n| _ => \"(?\'a)\" in typ_to_string x end)";

        final MLFunction<Theory, scala.collection.immutable.List<Tuple2<String, String>>>
            mlFunToExtractSigns = MLValue.compileFunction(
                        "fn thy => ListPair.zip ((map (fn x => (fst x)) (" + extractConstFunString
                        + ")),map " + toStringFunction + "(map (fn x => (fst (snd x))) ("
                        + extractConstFunString + ")))",
                ScalaIsabelleFacade.isabelle, global(), Implicits.theoryConverter(),
                PAIR_TO_LIST_CONVERTER);

        for (final String thyName : this.theoryNames) {
            final String thyNameWithoutSession = thyName.split("\\.")[1];

            final Map<String, String> toBeFilled = new HashMap<String, String>();
            this.functionsAndDefinitions.put(thyName, toBeFilled);

            final Context ctxt = Context.apply(thyName, ScalaIsabelleFacade.isabelle, global());
            final Theory theory = ctxt.theoryOf(ScalaIsabelleFacade.isabelle, global());

            final List<String> names = JavaConverters.asJava(mlFunToExtractAllNames
                    .apply(theory.mlValue(), ScalaIsabelleFacade.isabelle, global())
                    .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle, global()));
            final List<Tuple2<String, String>> types = JavaConverters.asJava(mlFunToExtractSigns
                    .apply(theory.mlValue(), ScalaIsabelleFacade.isabelle, global())
                    .retrieveNow(PAIR_TO_LIST_CONVERTER, ScalaIsabelleFacade.isabelle, global()));

            for (int i = 0; i < names.size(); i++) {
                String name = names.get(i);

                if (!name.startsWith(thyNameWithoutSession + ".")) {
                    continue;
                }

                final String defSuffix = "_def";
                if (name.endsWith(defSuffix) || name.endsWith("_def_raw")) {
                    name = name.replace("_raw", "");
                    name = name.replace(defSuffix, "");

                    if (name.endsWith("_rel") || name.endsWith("_graph")
                            || name.endsWith("_sumC")) {
                        continue;
                    }

                    String type = "";

                    for (final var tup : types) {
                        if (tup._1.equals(name)) {
                            type = tup._2;
                        }
                    }

                    type = type.replace("Set.set(alternative)", "alternatives");

                    toBeFilled.put(name, type);
                }
            }
        }
    }

    private void extractTheorems() {
        this.theorems = new HashMap<String, Map<String, String>>();

        final MLFunction<Theory, scala.collection.immutable.List<String>> mlFun = MLValue
                .compileFunction(
                        "fn thy => map (fn x => fst (snd x)) (Global_Theory.dest_thm_names thy) ",
                        ScalaIsabelleFacade.isabelle, global(), Implicits.theoryConverter(),
                        LIST_CONVERTER);
        final MLFunction<Thm, String> convString = MLValue.compileFunction(
                "fn thm => (Syntax.string_of_term_global (hd (Theory.ancestors_of "
                        + "(Thm.theory_of_thm thm))) (Thm.prop_of thm))",
                isabelle, global(), Implicits.thmConverter(), STRING_CONVERTER);

        for (final String thyName : this.theoryNames) {
            final Map<String, String> toBeFilled = new HashMap<String, String>();
            this.theorems.put(thyName, toBeFilled);

            final Context ctxt = Context.apply(thyName, ScalaIsabelleFacade.isabelle, global());
            final Theory theory = ctxt.theoryOf(ScalaIsabelleFacade.isabelle, global());

            final scala.collection.immutable.List<String> defs = mlFun
                    .apply(theory, ScalaIsabelleFacade.isabelle, global(),
                            Implicits.theoryConverter())
                    .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle, global());

            for (int i = 0; i < defs.length(); i++) {
                final String thmName = defs.apply(i);

                // This filters out all theorems generated by Isabelle for internal usage.
                if (thmName.matches(".*\\..*\\..*")) {
                    continue;
                }

                final MLFunction<Theory, Thm> thmFun = MLValue.compileFunction(
                        "fn thy => Global_Theory.get_thm thy \"" + thmName + "\"",
                        ScalaIsabelleFacade.isabelle, global(), Implicits.theoryConverter(),
                        Implicits.thmConverter());
                final Thm thm = thmFun.apply(theory, ScalaIsabelleFacade.isabelle, global(),
                        Implicits.theoryConverter()).retrieveNow(Implicits.thmConverter(),
                                ScalaIsabelleFacade.isabelle, global());
                final String pretty = convString.apply(thm.mlValue(), isabelle, global())
                        .retrieveNow(STRING_CONVERTER, isabelle, global());

                toBeFilled.put(thmName, pretty);
            }
        }
    }

    private void extractTheoryNames() {
        final String prefix = this.sessionName + IsabelleUtils.THEORY_NAME_SEPARATOR;

        final MLFunction0<scala.collection.immutable.List<String>> mlFun = MLValue.compileFunction0(
                "Thy_Info.get_names", ScalaIsabelleFacade.isabelle, global(), LIST_CONVERTER);
        final var thys = mlFun.apply(ScalaIsabelleFacade.isabelle, global())
                .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle, global());

        for (final String thy : JavaConverters.asJava(thys)) {
            if (thy.startsWith(prefix)) {
                this.theoryNames.add(thy);
            }
        }
    }

    public Map<String, Map<String, String>> getFunctionsAndDefinitions() {
        return this.functionsAndDefinitions;
    }

    public Map<String, Map<String, String>> getTheorems() {
        return this.theorems;
    }

    public Set<String> getTheoryNames() {
        return this.theoryNames;
    }

    private void init() {
        this.extractTheoryNames();
        this.extractTheorems();
        this.extractFunctionsAndDefinitions();

        isabelle.destroy();
    }

    /**
     * Required, as StringConverter cannot be instantiated.
     */
    private static class JavaStringConverter extends Converter<String> {

        @Override
        public String exnToValue(final Isabelle localIsabelle, final ExecutionContext ec) {
            return StringConverter.exnToValue(localIsabelle, ec);
        }

        @Override
        public String mlType(final Isabelle localIsabelle, final ExecutionContext ec) {
            return StringConverter.mlType(localIsabelle, ec);
        }

        @Override
        public Future<String> retrieve(final MLValue<String> value, final Isabelle localIsabelle,
                final ExecutionContext ec) {
            return StringConverter.retrieve(value, localIsabelle, ec);
        }

        @Override
        public MLValue<String> store(final String value, final Isabelle localIsabelle,
                final ExecutionContext ec) {
            return StringConverter.store(value, localIsabelle, ec);
        }

        @Override
        public String valueToExn(final Isabelle localIsabelle, final ExecutionContext ec) {
            return StringConverter.valueToExn(localIsabelle, ec);
        }

    }

}
