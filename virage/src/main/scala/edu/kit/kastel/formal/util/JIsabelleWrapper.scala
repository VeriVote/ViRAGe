package edu.kit.kastel.formal.util

import java.nio.file.Path

import de.unruh.isabelle.control
import de.unruh.isabelle.control.Isabelle
import collection.JavaConverters._

object JIsabelleWrapper {

  /** Sets the [[de.unruh.isabelle.control.Isabelle.Setup.verbose verbose]] flag in the setup `setup`.
   *
   * @return `setup` with [[de.unruh.isabelle.control.Isabelle.Setup.verbose verbose]] set to `verbose`
   * @param verbose the new value for `setup.`[[de.unruh.isabelle.control.Isabelle.Setup.verbose verbose]]
   * */
  def setupSetVerbose(verbose : Boolean, setup : Isabelle.Setup): Isabelle.Setup = setup.copy(verbose = verbose)

  /** Sets the [[de.unruh.isabelle.control.Isabelle.Setup.userDir userDir]] directory in the setup `setup`.
   * Note: There is no way to change the `userDir` to `None`. However, the default value for `userDir` is `None`.
   *
   * @return `setup` with [[de.unruh.isabelle.control.Isabelle.Setup.userDir userDir]] set to `Some(userDir)`
   * @param verbose the new value for `setup.`[[de.unruh.isabelle.control.Isabelle.Setup.verbose verbose]]
   * */
  def setupSetUserDir(userDir: Path, setup: Isabelle.Setup): Isabelle.Setup = setup.copy(userDir = Some(userDir))

  /** Sets the [[de.unruh.isabelle.control.Isabelle.Setup.workingDirectory workingDirectory]] directory in the setup `setup`.
   *
   * @return `setup` with [[de.unruh.isabelle.control.Isabelle.Setup.workingDirectory workingDirectory]] set to `workingDirectory`
   * @param workingDirectory the new value for `setup.`[[de.unruh.isabelle.control.Isabelle.Setup.workingDirectory workingDirectory]]
   * */
  def setupSetWorkingDirectory(workingDirectory: Path, setup: Isabelle.Setup): Isabelle.Setup =
    setup.copy(workingDirectory = workingDirectory)

  /** Sets the [[de.unruh.isabelle.control.Isabelle.Setup.sessionRoots sessionRoots]] directories in the setup `setup`.
   *
   * @return `setup` with [[de.unruh.isabelle.control.Isabelle.Setup.sessionRoots sessionRoots]] set to `sessionRoots`
   * @param sessionRoots the new value for `setup.`[[de.unruh.isabelle.control.Isabelle.Setup.sessionRoots sessionRoots]].
   *                     It will automatically be converted to a Scala [[Seq]].
   * */
  def setupSetSessionRoots(sessionRoots: java.lang.Iterable[Path], setup: Isabelle.Setup): Isabelle.Setup =
    setup.copy(sessionRoots = sessionRoots.asScala.toSeq)

}