package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path

class BenchTestRunner
  extends DiffTestRunnerBase(DiffTestRunner.State)
  with ParallelTestExecution
:
  override protected lazy val diffTestFiles = os.list(os.pwd/"benchmark"/"src"/"test"/"bench")

  override protected def createDiffMaker(file: Path, preludePath: Path, predefPath: Path, relativeName: String): DiffMaker =
    new BenchDiffMaker((os.pwd/"benchmark").toString, file, preludePath, predefPath, relativeName)

