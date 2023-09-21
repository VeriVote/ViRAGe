package edu.kit.kastel.formal.virage.isabelle;

import static edu.kit.kastel.formal.util.StringUtils.addSpace;
import static edu.kit.kastel.formal.util.StringUtils.func;
import static edu.kit.kastel.formal.util.StringUtils.func2;
import static edu.kit.kastel.formal.util.StringUtils.map;
import static edu.kit.kastel.formal.util.StringUtils.parenthesize2;
import static edu.kit.kastel.formal.util.StringUtils.printCollection2;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.control.Isabelle.Setup;
import de.unruh.isabelle.control.IsabelleBuildException;
import de.unruh.isabelle.java.JIsabelle;
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
import edu.kit.kastel.formal.util.JIsabelleWrapper;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.IsabelleBuildFailedException;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.concurrent.Future;

/**
 * A facade for <a href="https://dominique-unruh.github.io/scala-isabelle/">scala-isabelle</a>.
 *
 * @author VeriVote
 */
public final class ScalaIsabelleFacade {
    /**
     * String "x".
     */
    public static final String DEFAULT_VARIABLE = "x";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * The Isabelle instance.
     */
    private static Isabelle isabelle;

    /**
     * The function application sign.
     */
    private static final String TO = "=>";

    /**
     * The fn function.
     */
    private static final String FN = "fn";

    /**
     * Theory string.
     */
    private static final String THY = "thy";

    /**
     * Theorem string.
     */
    private static final String THM = "thm";

    /**
     * The head function.
     */
    private static final String HD = "hd";

    /**
     * The function that takes the first element.
     */
    private static final String FST = "fst";

    /**
     * The function that takes the second element.
     */
    private static final String SND = "snd";

    /**
     * The set function.
     */
    private static final String SET_FUN = "set";

    /**
     * Type for alternatives.
     */
    private static final String ALTERNATIVE = "alternative";

    /**
     * New name for alternatives.
     */
    private static final String ALTERNATIVES_NAME = "alternatives";

    /**
     * The type command.
     */
    private static final String TYPE = "Type";

    /**
     * Theory.
     */
    private static final String THEORY = "Theory";

    /**
     * Global theory.
     */
    private static final String GLOBAL_THEORY = "Global_Theory";

    /**
     * Theorem type.
     */
    private static final String THM_TYPE = "Thm";

    /**
     * The Isabelle string theory.
     */
    private static final String STRING_THEORY = "String";

    /**
     * The zipping function.
     */
    private static final String ZIP =
            "ListPair" + IsabelleUtils.THEORY_NAME_SEPARATOR + "zip";

    /**
     * The is-prefix function.
     */
    private static final String IS_PREFIX =
            STRING_THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "isPrefix";

    /**
     * The theory-name function.
     */
    private static final String THY_NAME =
            "Context" + IsabelleUtils.THEORY_NAME_SEPARATOR + "theory_base_name";

    /**
     * The specifications-of function.
     */
    private static final String SPECS_OF =
            "Defs" + IsabelleUtils.THEORY_NAME_SEPARATOR + "all_specifications_of";

    /**
     * The definitions-of function.
     */
    private static final String DEFS_OF =
            THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "defs_of";

    /**
     * The destination function.
     */
    private static final String DEST = "Consts" + IsabelleUtils.THEORY_NAME_SEPARATOR + "dest";

    /**
     * The constants-of function.
     */
    private static final String CONSTS_OF =
            "Sign" + IsabelleUtils.THEORY_NAME_SEPARATOR + "consts_of";

    /**
     * The type-to-string function.
     */
    private static final String TYP_TO_STRING = "typ_to_string";

    /**
     * The String concatenation function.
     */
    private static final String CONCAT =
            STRING_THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "concat";

    /**
     * The type function for terms.
     */
    private static final String TYP = "Basic_Term" + IsabelleUtils.THEORY_NAME_SEPARATOR + "typ";

    /**
     * The destination theorem names function.
     */
    private static final String DEST_THM_NAMES =
            GLOBAL_THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "dest_thm_names";

    /**
     * The string-of-term-global function.
     */
    private static final String STRING_OF_TERM =
            "Syntax" + IsabelleUtils.THEORY_NAME_SEPARATOR + "string_of_term_global";

    /**
     * The ancestors-of function.
     */
    private static final String ANCESTS_OF =
            THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "ancestors_of";

    /**
     * The theory-of-theorem function.
     */
    private static final String THY_OF_THM =
            THM_TYPE + IsabelleUtils.THEORY_NAME_SEPARATOR + "theory_of_thm";

    /**
     * The proposition-of function.
     */
    private static final String PROP_OF =
            THM_TYPE + IsabelleUtils.THEORY_NAME_SEPARATOR + "prop_of";

    /**
     * The get-theorem function.
     */
    private static final String GET_THM =
            GLOBAL_THEORY + IsabelleUtils.THEORY_NAME_SEPARATOR + "get_thm";

    /**
     * The get-names function.
     */
    private static final String GET_NAMES =
            "Thy_Info" + IsabelleUtils.THEORY_NAME_SEPARATOR + "get_names";

    /**
     * The list converter for scala-isabelle.
     */
    private static final ListConverter<String> LIST_CONVERTER =
            new ListConverter<String>(new JavaStringConverter());

    /**
     * The string converter for scala-isabelle.
     */
    private static final JavaStringConverter STRING_CONVERTER = new JavaStringConverter();

    /**
     * The "pair-to-list" converter for scala-isabelle.
     */
    private static final ListConverter<Tuple2<String, String>> PAIR_TO_LIST_CONVERTER =
            new ListConverter<Tuple2<String, String>>(
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
        this.sessionDir = SystemUtils.file(sessionDirValue).getAbsolutePath();
        this.sessionName = sessionNameValue;
        this.theoryNames = new HashSet<String>();
        final List<String> sessionDirs = new LinkedList<String>();
        sessionDirs.add(this.sessionDir);
        final String isabelleHome = ConfigReader.getInstance().getIsabelleHome();
        final boolean verbosity = true;
        final String isabelleDir = ConfigReader.getInstance().getIsabelleSessionDir();
        this.setup = setup(isabelleHome, verbosity, isabelleDir, sessionNameValue,
                           this.sessionDir, sessionDirs);
        try {
            buildAndSetIsabelle(this.setup);
            // Scala has no checked Exceptions and the constructor is not annotated.
            // Therefore, the Java compiler thinks that the (implicitly checked)
            // IsabelleBuildException cannot be thrown.
        } catch (/* IsabelleBuild */final IsabelleBuildException e) {
            e.printStackTrace();
            LOGGER.error("Building "
                    + "session " + sessionNameValue
                    + " failed. Restarting ViRAGe "
                    + "or building"
                    + " the session manually within Isabelle "
                    + "might help. If the session is supposed"
                    + " to generate documentation, "
                    + "TeX Live is required!");
            throw new IsabelleBuildFailedException();
        }
        this.init();
    }

    private static Iterable<Path> toPaths(final Iterable<String> paths) {
        final List<Path> dirs = new LinkedList<Path>();
        if (paths == null) {
            return dirs;
        }
        for (final String path: paths) {
            dirs.add(Path.of(path));
        }
        return dirs;
    }

    private static Setup setup(final String isabelleHome, final boolean verbose,
                               final String isabelleDirectory, final String sessionName,
                               final String sessionDir,
                               final Iterable<String> sessionDirs) {
        Setup s = JIsabelle.setup(Path.of(isabelleHome));
        s = JIsabelle.setupSetVerbose(true, s);
        s = JIsabelle.setupSetUserDir(Path.of(isabelleDirectory), s);
        s = JIsabelle.setupSetWorkingDirectory(Path.of(sessionDir), s);
        s = JIsabelle.setupSetSessionRoots(toPaths(sessionDirs), s);
        s = JIsabelleWrapper.setupSetLogic(sessionName, s);
        s = JIsabelle.setupSetBuild(true, s);
        return s;
    }

    private static synchronized void setIsabelleInstance(final Isabelle instance) {
        isabelle = instance;
    }

    private static void buildAndSetIsabelle(final Setup setup) throws IsabelleBuildException {
        setIsabelleInstance(JIsabelleWrapper.isabelle(setup));
    }

    private static synchronized void destroyIsabelleInstance() {
        isabelle.destroy();
        setIsabelleInstance(null);
    }

    private static String fnTo(final String s, final String... args) {
        return printCollection2(FN, s, TO, printCollection2(args));
    }

    private static String funToExtractAllNames(final String thy) {
        final String descr = "#description";
        final String filter = "filter";
        return func2(fnTo(thy),
                     map(func2(fnTo(DEFAULT_VARIABLE),
                               func2(descr, func2(HD, func2(SND, DEFAULT_VARIABLE)))),
                         map(filter,
                             func2(fnTo(DEFAULT_VARIABLE),
                                   map(IS_PREFIX, printCollection2(THY_NAME, thy),
                                       func2(SND, func2(FST, DEFAULT_VARIABLE)))),
                             func2(SPECS_OF, DEFS_OF, thy))));
    }

    private static String toStringFun() {
        final String polyType = "\'a";
        return fnTo(DEFAULT_VARIABLE, "let", "fun",
                    func2(TYP_TO_STRING, DEFAULT_VARIABLE + StringUtils.COLON,
                          TYP) + StringUtils.COLON,
                    "string", StringUtils.EQ, "case", DEFAULT_VARIABLE, "of")
                    + System.lineSeparator()
                + printCollection2(TYPE, DEFAULT_VARIABLE, TO, StringUtils.QUOTATION)
                + parenthesize2(func2(printCollection2(StringUtils.QUOTATION, StringUtils.CARET),
                                      FST, DEFAULT_VARIABLE), StringUtils.CARET,
                                func2(CONCAT,
                                      map(TYP_TO_STRING, printCollection2(SND, DEFAULT_VARIABLE))),
                                StringUtils.CARET, StringUtils.QUOTATION)
                + StringUtils.QUOTATION + System.lineSeparator()
                + func(printCollection2("|", IsabelleTheoryGenerator.NAME_SEPARATOR, TO,
                                        StringUtils.QUOTATION),
                       "?" + polyType)
                + printCollection2(StringUtils.QUOTATION, "in", TYP_TO_STRING,
                                   DEFAULT_VARIABLE, "end");
    }

    private static String funToExtractSigns(final String thy) {
        final String consts = "#constants";
        final String extractConstFunString = func2(consts, func2(DEST, CONSTS_OF, thy));
        final String toStringFunction = toStringFun();
        return fnTo(thy,
                    func(addSpace(ZIP),
                         parenthesize2(map(func2(fnTo(DEFAULT_VARIABLE), FST, DEFAULT_VARIABLE),
                                           extractConstFunString)),
                         map(toStringFunction,
                             map(func2(fnTo(DEFAULT_VARIABLE), func2(FST, SND, DEFAULT_VARIABLE)),
                                 extractConstFunString))));
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
        if (ScalaIsabelleFacade.isabelle != null) {
            return;
        }
        final String session = SystemUtils.file(sessionDir).getAbsolutePath();
        final ConfigReader configReader = ConfigReader.getInstance();
        final List<String> sessionDirs = new LinkedList<String>();
        sessionDirs.add(session);
        final String isabelleHome = configReader.getIsabelleHome();
        final boolean verbosity = true;
        final String isabelleDir = configReader.getIsabelleSessionDir();
        final Setup setup = setup(isabelleHome, verbosity, isabelleDir, sessionName,
                                  session, sessionDirs);
        try {
            buildAndSetIsabelle(setup);
            // Scala has no checked Exceptions and the constructor is not annotated.
            // Therefore, the Java compiler thinks that the (implicitly checked)
            // IsabelleBuildException cannot be thrown.
        } catch (/* IsabelleBuild */final IsabelleBuildException e) {
            e.printStackTrace();
            LOGGER.error("Building session " + sessionName
                    + " failed. Restarting ViRAGe or building "
                    + "the session manually within Isabelle might help. "
                    + "If the session is supposed "
                    + "to generate documentation, TeX Live is required!");
            throw new IsabelleBuildFailedException();
        }
        destroyIsabelleInstance();
    }

    /**
     * Extracts functions and definitions from a given framework in Isabelle.
     */
    public void extractFunctionsAndDefinitions() {
        this.functionsAndDefinitions = new HashMap<String, Map<String, String>>();
        final MLFunction<Theory, scala.collection.immutable.List<String>> mlFunToExtractAllNames =
                MLValue.compileFunction(funToExtractAllNames(THY), ScalaIsabelleFacade.isabelle,
                                        Implicits.theoryConverter(), LIST_CONVERTER);
        final MLFunction<Theory, scala.collection.immutable.List<Tuple2<String, String>>>
            mlFunToExtractSigns =
            MLValue.compileFunction(funToExtractSigns(THY), ScalaIsabelleFacade.isabelle,
                                    Implicits.theoryConverter(), PAIR_TO_LIST_CONVERTER);
        for (final String thy: this.theoryNames) {
            final String thyWithoutSession = thy.split("\\.")[1];
            final Map<String, String> toBeFilled = new HashMap<String, String>();
            this.functionsAndDefinitions.put(thy, toBeFilled);
            final Context ctxt = Context.apply(thy, ScalaIsabelleFacade.isabelle);
            final Theory theory = ctxt.theoryOf(ScalaIsabelleFacade.isabelle);
            final List<String> names =
                    JavaConverters.asJava(mlFunToExtractAllNames
                            .apply(theory.mlValue(), ScalaIsabelleFacade.isabelle)
                            .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle));
            final List<Tuple2<String, String>> types =
                    JavaConverters.asJava(mlFunToExtractSigns
                            .apply(theory.mlValue(), ScalaIsabelleFacade.isabelle)
                            .retrieveNow(PAIR_TO_LIST_CONVERTER, ScalaIsabelleFacade.isabelle));
            for (int i = 0; i < names.size(); i++) {
                String name = names.get(i);
                if (!name.startsWith(thyWithoutSession + IsabelleUtils.THEORY_NAME_SEPARATOR)) {
                    continue;
                }
                final String defSfx = "_def";
                final String relSfx = "_rel";
                final String rawSfx = "_raw";
                final String graphSfx = "_graph";
                final String sumSfx = "_sumC";
                final String defRawSfx = defSfx + rawSfx;
                if (name.endsWith(defSfx) || name.endsWith(defRawSfx)) {
                    name = name.replace(rawSfx, StringUtils.EMPTY);
                    name = name.replace(defSfx, StringUtils.EMPTY);
                    if (name.endsWith(relSfx) || name.endsWith(graphSfx) || name.endsWith(sumSfx)) {
                        continue;
                    }
                    String type = StringUtils.EMPTY;
                    for (final Tuple2<String, String> tup: types) {
                        if (tup._1.equals(name)) {
                            type = tup._2;
                        }
                    }
                    type = type.replace(
                            IsabelleUtils.SET + IsabelleUtils.THEORY_NAME_SEPARATOR
                            + StringUtils.func(SET_FUN, ALTERNATIVE),
                            ALTERNATIVES_NAME);
                    toBeFilled.put(name, type);
                }
            }
        }
    }

    private void extractTheorems() {
        this.theorems = new HashMap<String, Map<String, String>>();
        final MLFunction<Theory, scala.collection.immutable.List<String>> mlFun =
                MLValue.compileFunction(
                        addSpace(fnTo(THY,
                                      map(fnTo(DEFAULT_VARIABLE, func2(FST, SND, DEFAULT_VARIABLE)),
                                          printCollection2(DEST_THM_NAMES, THY)))),
                        ScalaIsabelleFacade.isabelle,
                        Implicits.theoryConverter(), LIST_CONVERTER);
        final MLFunction<Thm, String> convString =
                MLValue.compileFunction(
                        func2(fnTo(THM),
                              map(STRING_OF_TERM,
                                  func2(HD, func2(ANCESTS_OF, THY_OF_THM, THM)),
                                  printCollection2(PROP_OF, THM))),
                        ScalaIsabelleFacade.isabelle,
                        Implicits.thmConverter(), STRING_CONVERTER);
        for (final String thyName: this.theoryNames) {
            final Map<String, String> toBeFilled = new HashMap<String, String>();
            this.theorems.put(thyName, toBeFilled);
            final Context ctxt = Context.apply(thyName, ScalaIsabelleFacade.isabelle);
            final Theory theory = ctxt.theoryOf(ScalaIsabelleFacade.isabelle);
            final scala.collection.immutable.List<String> defs =
                    mlFun.apply(theory, ScalaIsabelleFacade.isabelle, Implicits.theoryConverter())
                    .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle);
            for (int i = 0; i < defs.length(); i++) {
                final String thmName = defs.apply(i);
                // This filters out all theorems generated by Isabelle for internal usage.
                if (thmName.matches(".*\\..*\\..*")) {
                    continue;
                }
                final MLFunction<Theory, Thm> thmFun =
                        MLValue.compileFunction(
                                fnTo(THY, GET_THM, THY,
                                        StringUtils.QUOTATION + thmName + StringUtils.QUOTATION),
                                ScalaIsabelleFacade.isabelle,
                                Implicits.theoryConverter(), Implicits.thmConverter());
                final Thm thm =
                        thmFun.apply(theory, ScalaIsabelleFacade.isabelle,
                                     Implicits.theoryConverter())
                        .retrieveNow(Implicits.thmConverter(), ScalaIsabelleFacade.isabelle);
                final String pretty =
                        convString.apply(thm.mlValue(), ScalaIsabelleFacade.isabelle)
                        .retrieveNow(STRING_CONVERTER, ScalaIsabelleFacade.isabelle);
                toBeFilled.put(thmName, pretty);
            }
        }
    }

    private void extractTheoryNames() {
        final String prefix = this.sessionName + IsabelleUtils.THEORY_NAME_SEPARATOR;
        final MLFunction0<scala.collection.immutable.List<String>> mlFun =
                MLValue.compileFunction0(GET_NAMES, ScalaIsabelleFacade.isabelle, LIST_CONVERTER);
        final scala.collection.immutable.List<String> thys =
                mlFun.apply(ScalaIsabelleFacade.isabelle)
                .retrieveNow(LIST_CONVERTER, ScalaIsabelleFacade.isabelle);
        for (final String thy: JavaConverters.asJava(thys)) {
            if (thy.startsWith(prefix)) {
                this.theoryNames.add(thy);
            }
        }
    }

    /**
     * Returns the functions and definitions as a map of maps.
     *
     * @return the functions and definitions
     */
    public Map<String, Map<String, String>> getFunctionsAndDefinitions() {
        return this.functionsAndDefinitions;
    }

    /**
     * Returns the theorems as a map of maps.
     *
     * @return the theorems
     */
    public Map<String, Map<String, String>> getTheorems() {
        return this.theorems;
    }

    /**
     * Returns the theory names as a set.
     *
     * @return the theory names
     */
    public Set<String> getTheoryNames() {
        return this.theoryNames;
    }

    private synchronized void init() {
        this.extractTheoryNames();
        this.extractTheorems();
        this.extractFunctionsAndDefinitions();
        destroyIsabelleInstance();
    }

    /**
     * Required, as StringConverter cannot be instantiated.
     */
    private static final class JavaStringConverter extends Converter<String> {
        @Override
        public String exnToValue(final Isabelle localIsabelle) {
            return StringConverter.exnToValue(localIsabelle);
        }

        @Override
        public String mlType(final Isabelle localIsabelle) {
            return StringConverter.mlType(localIsabelle);
        }

        @Override
        public Future<String> retrieve(final MLValue<String> value, final Isabelle localIsabelle) {
            return StringConverter.retrieve(value, localIsabelle);
        }

        @Override
        public MLValue<String> store(final String value, final Isabelle localIsabelle) {
            return StringConverter.store(value, localIsabelle);
        }

        @Override
        public String valueToExn(final Isabelle localIsabelle) {
            return StringConverter.valueToExn(localIsabelle);
        }
    }
}
