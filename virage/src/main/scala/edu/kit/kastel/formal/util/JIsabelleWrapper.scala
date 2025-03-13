package edu.kit.kastel.formal.util

import java.nio.file.Path

import de.unruh.isabelle.control
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.control.IsabelleBuildException
import scala.jdk.CollectionConverters._

object JIsabelleWrapper {
  /**
   * Invokes the constructor [[de.unruh.isabelle.control.Isabelle]]`(setup: SetupGeneral)` and
   * explicitly declares that exceptions of [[de.unruh.isabelle.control.IsabelleBuildException]]
   * may be thrown.
   *
   * @constructor Partly asynchronous initialization of the Isabelle instance
   * @param setup Configuration object that specifies the path of the Isabelle binary, the heap
   *              image, and more
   * @throws IsabelleBuildException if building the Isabelle instance fails
   */
  @throws(classOf[IsabelleBuildException])
  def isabelle(setup: Isabelle.Setup): Isabelle = new Isabelle(setup)
}
