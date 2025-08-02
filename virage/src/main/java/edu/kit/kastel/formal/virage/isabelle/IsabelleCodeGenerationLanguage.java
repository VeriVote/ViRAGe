package edu.kit.kastel.formal.virage.isabelle;

/**
 * The target programming languages of Isabelle's code generator.
 *
 * @author VeriVote
 */
public enum IsabelleCodeGenerationLanguage {
    /**
     * The strong statically typed object-oriented and functional Scala language that runs on Java.
     */
    Scala,

    /**
     * The multi-paradigm object-oriented and functional OCaml (Objective Caml) language.
     */
    OCaml,

    /**
     * The functional type-safe SML (Standard Meta Language) language.
     */
    SML,

    /**
     * The statically typed and functional Haskell language.
     */
    Haskell
}
