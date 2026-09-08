/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator
import Export.Parse

/- Local compatibility change (2026-09-07): use the upstream Lean4Checker
   replayer pinned by Comparator v4.28.0, including kernel-level private
   declaration checks, in place of the later built-in kernel replay API. -/
import Lean4Checker.Replay

namespace Comparator
structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  definitionNames : Array Lean.Name
  legalAxioms : Array Lean.Name
  leanPrefix : System.FilePath
  gitLocation : System.FilePath
  whichLandrun : String
  whichLean4Export : String
  externalKernels : (Std.TreeMap String (Array String))

abbrev M := ReaderT Context IO
structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  readablePaths : Array System.FilePath
  writablePaths : Array System.FilePath
  executablePaths : Array System.FilePath

@[inline]
def getExternalKernels : M (Std.TreeMap String (Array String)) := do return (← read).externalKernels

@[inline]
def getTheoremNames : M (Array Lean.Name) := do return (← read).theoremNames
@[inline]
def getDefinitionNames : M (Array Lean.Name) := do return (← read).definitionNames

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

@[inline]
def getChallengeModule : M Lean.Name := do return (← read).challengeModule

@[inline]
def getSolutionModule : M Lean.Name := do return (← read).solutionModule

@[inline]
def getLegalAxioms : M (Array Lean.Name) := do return (← read).legalAxioms
@[inline]
def getLeanPrefix : M System.FilePath := do return (← read).leanPrefix

@[inline]
def getGitLocation : M System.FilePath := do return (← read).gitLocation

def queryGitLocation : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "which",
    args := #["git"],
    stdout := .piped,
  }
  return out.trimAscii.toString
def queryLeanPrefix (projectDir : System.FilePath) : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "lean",
    args := #["--print-prefix"],
    stdout := .piped,
    cwd := projectDir
  }
  return out.trimAscii.toString
def buildLandrunArgs (spawnArgs : LandrunArgs) : Array String :=
  let args := #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]
  let args := spawnArgs.envPass.foldl (init := args) (fun acc env => acc ++ #["--env", env])
  let args := spawnArgs.readablePaths.foldl (init := args) (fun acc path => acc ++ #["--ro", path.toString])
  let args := spawnArgs.writablePaths.foldl (init := args) (fun acc path => acc ++ #["--rwx", path.toString])
  let args := spawnArgs.executablePaths.foldl (init := args) (fun acc path => acc ++ #["--rox", path.toString])
  args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args
def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args := buildLandrunArgs spawnArgs
  let { stdout, stderr, exitCode } ← IO.Process.output {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout

def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args := buildLandrunArgs spawnArgs
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"
def safeLakeBuild (target : Lean.Name) : M Unit := do
  IO.println s!"Building {target}"
  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  let gitLocation ← getGitLocation

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir
  runSandBoxed {
    cmd := "lake",
    args := #["build", target.toString],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    executablePaths := #[leanPrefix, gitLocation]
  }
def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let baseArgs := #[module.toString, "--"]
  let args := decls.foldl (·.push <| ·.toString) baseArgs
  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  runSandBoxedWithStdout {
    cmd := (← read).whichLean4Export
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, dotLakeDir]
    writablePaths := #[]
    executablePaths := #[leanPrefix]
  }
def runExternalKernel (kernelName : String) (kernelCommand : Array String)
    (solutionExport : String) : M (Option String) := do
  IO.println s!"Running {kernelName} kernel on solution"
  -- just always put out a nanoda-like config file for now
  IO.FS.withTempFile fun configHandle configPath => do
  IO.FS.withTempFile fun solutionHandle solutionPath => do
    let legalAxioms ← getLegalAxioms
    configHandle.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", false),
      ("export_file_path", solutionPath.toString),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("num_threads", 4),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    configHandle.flush
    solutionHandle.putStr solutionExport
    solutionHandle.flush

    let mut kernelArgs := kernelCommand[1...*].toArray
    if isNanodaKernel kernelName then
      kernelArgs := kernelArgs.push configPath.toString
    else
      kernelArgs := kernelArgs.push solutionPath.toString
    let spawnArgs := {
      cmd := kernelCommand[0]!,
      args := kernelArgs,
      envPass := #[]
      readablePaths := #[configPath.toString, solutionPath.toString]
      writablePaths := #[]
      executablePaths := #[]
    }
    let args := buildLandrunArgs spawnArgs

    try
      let proc ← IO.Process.spawn {
        cmd := (← read).whichLandrun,
        args,
        env := spawnArgs.envOverride
        cwd := (← getProjectDir)
      }
      let ret ← proc.wait
      if ret != 0 then
        IO.println s!"{kernelName} kernel rejected the solution"
        return some s!"{kernelName} exited with {ret}"
      else
        IO.println s!"{kernelName} kernel accepts the solution"
        return none
    catch e => do
      IO.println s!"Error while interacting with {kernelName} kernel"
      return some s!"Error while interacting with {kernelName} kernel: {e.toString}"
where
  isNanodaKernel (kernelName : String) : Bool :=
    -- TODO: get rid of this heuristic
    kernelName.contains "noda"
def runBuiltinKernel (solution : Export.ExportedEnv) : M (Option String) := do
  IO.println "Running Lean default kernel on solution."
  (← IO.getStdout).flush
  let env ← Lean.mkEmptyEnvironment
  unless env.constants.toList.isEmpty do
    throw <| IO.userError "Replay must start from an empty environment"
  IO.println "Replay starts with zero imported declarations"
  (← IO.getStdout).flush
  let mut kernelEnv := env
  let origConstMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
  try
    kernelEnv ← kernelEnv.replay' kernelConstMap
    IO.println "Lean default kernel accepts the solution"
  catch e =>
    IO.println "Lean default kernel rejects the solution"
    return some e.toString
  try
    let verifyTargets := `Quot :: quotTargets
    for quotTarget in verifyTargets do
      if let some info := origConstMap[quotTarget]? then
        let some info' := kernelEnv.toKernelEnv.find? quotTarget |
          throw <| .userError s!"Could not find quotient constant in final kernel env: {quotTarget}"
        if info != info' then
          throw <| .userError s!"Quotient constant mismatch on: {quotTarget}"
    return none
  catch e =>
    IO.println "Quotient post-check rejects the solution"
    return some e.toString
def primitiveTargets : M (Array Lean.Name) := do
  -- The challenge needs to have all the built-in constants of the kernel, as the
  -- kernel makes no guarantees when fed other definitions here.
  -- List from `git grep new_persistent_expr_const src/kernel/`
  return #[
    -- ``Nat.zero,
    -- ``Nat.succ,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.gcd,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight,
    ``String.ofList,
    ``Char.ofNat,
    ``List,
    ``eagerReduce,
    ``Nat,
    ``String,
    ``String.mk,
    ``Char,
    ``optParam,
    ``autoParam,
    ``semiOutParam,
    ``outParam
  ]
def builtinTargets : M (Array Lean.Name) := do
  let mut additional := #[]
  if (← getLegalAxioms).contains ``Quot.sound then
    additional := additional ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  return additional

def stringStream (s : String) : BaseIO IO.FS.Stream := do
  let ref ← IO.mkRef {
    data := s.toByteArray
  }
  return IO.FS.Stream.ofBuffer ref
/- Local memory adaptation (2026-09-07): share the original verification
   sequence between the upstream CLI and a file-streaming entry point. -/
def verifyParsedMatch (challenge solution : Export.ExportedEnv)
    (solutionExport : String) : M Unit := do
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames
  let targets := (← getTheoremNames) ++ (← getLegalAxioms)
  IO.ofExcept <| Comparator.compareAt challenge solution targets definitionNames (← primitiveTargets)
  IO.println "Comparator statement and primitive comparison passed"
  (← IO.getStdout).flush
  IO.ofExcept <| Comparator.checkAxioms solution theoremNames definitionNames (← getLegalAxioms)
  IO.println "Comparator permitted-axiom check passed"
  (← IO.getStdout).flush
  let mut result := none
  for (kernelName, kernelCommand) in ← getExternalKernels do
    result := result <|> (← runExternalKernel kernelName kernelCommand solutionExport)
  result := result <|> (← runBuiltinKernel solution)
  if let some error := result then
    throw <| IO.userError error
def verifyMatch (challengeExport : String) (solutionExport : String) : M Unit := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  verifyParsedMatch challenge solution solutionExport

def compareExports (challengePath solutionPath : String) : M Unit := do
  unless (← getExternalKernels).isEmpty do
    throw <| IO.userError "The file-streaming entry point requires external_kernels to be empty"
  IO.println "Parsing challenge export from disk"
  (← IO.getStdout).flush
  let challengeHandle ← IO.FS.Handle.mk challengePath .read
  let challenge ← Export.parseStream (IO.FS.Stream.ofHandle challengeHandle)
  IO.println s!"Challenge export parsed: {challenge.constMap.size} declarations"
  (← IO.getStdout).flush
  let solutionHandle ← IO.FS.Handle.mk solutionPath .read
  let solution ← Export.parseStream (IO.FS.Stream.ofHandle solutionHandle)
  IO.println s!"Solution export parsed: {solution.constMap.size} declarations"
  (← IO.getStdout).flush
  verifyParsedMatch challenge solution ""
  IO.println "Your solution is okay!"
  (← IO.getStdout).flush

/- Local memory adaptation (2026-09-07): obtain the dependency graph directly
   from our already-built local artifacts. This deliberately does not claim
   Comparator's adversarial-olean isolation guarantee. The comparison, axiom
   checks, and full replay into an empty kernel remain the same. -/
def collectLocalGraph (env : Lean.Environment) (roots : Array Lean.Name) : IO Export.ExportedEnv := do
  let kernel := env.checked.get
  let mut work := roots
  let mut constMap : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  let mut constOrder := #[]
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if constMap.contains name then continue
    let some info := kernel.find? name |
      throw <| IO.userError s!"Missing local proof dependency: {name}"
    constMap := constMap.insert name info
    constOrder := constOrder.push name
    let (_, deps) := (runForUsedConsts info fun n =>
      (modify (fun a : Array Lean.Name => a.push n) : StateM (Array Lean.Name) Unit)).run #[]
    work := work ++ deps
    if let .recInfo recInfo := info then
      work := work ++ recInfo.all.toArray
    if constMap.size % 10000 == 0 then
      IO.println s!"Collected {constMap.size} declarations; at {name}"
      (← IO.getStdout).flush
  return { constMap, constOrder }

unsafe def compareLocalObjects : M Unit := do
  unless (← getExternalKernels).isEmpty do
    throw <| IO.userError "The local-object entry point requires external_kernels to be empty"
  Lean.initSearchPath (← Lean.findSysroot)
  let targets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)
  IO.println "Loading the independently compiled challenge objects"
  (← IO.getStdout).flush
  let challengeEnv ← Lean.importModules #[{module := ← getChallengeModule}] {}
    (loadExts := false) (leakEnv := true)
  let challenge ← collectLocalGraph challengeEnv targets
  IO.println s!"Challenge graph: {challenge.constMap.size} declarations"
  (← IO.getStdout).flush
  let solutionEnv ← Lean.importModules #[{module := ← getSolutionModule}] {}
    (loadExts := false) (leakEnv := true)
  let solution ← collectLocalGraph solutionEnv targets
  IO.println s!"Solution graph: {solution.constMap.size} declarations"
  (← IO.getStdout).flush
  if (← getTheoremNames).contains `CourtadeKumar.courtadeKumar_via_completed_certificates then
    let mut batches := 0
    let mut chunks := 0
    for (name, _) in solution.constMap.toList do
      let s := name.toString
      if s.startsWith "CourtadeKumar.LRCompactReducedCertificate.Batch" && s.endsWith ".checked" then
        if (s.splitOn ".").length == 4 then batches := batches + 1
        if (s.splitOn ".").length == 5 then chunks := chunks + 1
    unless batches == 42 && chunks == 9457 do
      throw <| IO.userError s!"Incomplete compact certificate dependency graph: {batches} batches, {chunks} chunks"
    IO.println s!"CK graph includes all {batches} batches and {chunks} kernel chunks"
    (← IO.getStdout).flush
  verifyParsedMatch challenge solution ""
  IO.println "Your solution is okay!"
  (← IO.getStdout).flush
def compareIt : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)

  let challengeModule ← getChallengeModule
  safeLakeBuild challengeModule
  let challengeExport ← safeExport challengeModule exportTargets

  let solutionModule ← getSolutionModule
  safeLakeBuild solutionModule
  let solutionExport ← safeExport solutionModule exportTargets

  verifyMatch challengeExport solutionExport
  IO.println "Your solution is okay!"

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda? : Option Bool
  external_kernels? : Option (Std.TreeMap String (Array String))
  deriving Lean.FromJson, Lean.ToJson, Repr
def M.run (x : M α) (cfg : Config) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  let leanPrefix ← queryLeanPrefix cwd
  let gitLocation ← queryGitLocation
  let whichLean4Export := (← IO.getEnv "COMPARATOR_LEAN4EXPORT").getD "lean4export"
  let whichLandrun := (← IO.getEnv "COMPARATOR_LANDRUN").getD "landrun"
  let mut externalKernels := cfg.external_kernels?.getD {}
  let defaultNanoda := "nanoda_bin"
  let nanodaOverride? ← IO.getEnv "COMPARATOR_NANODA"
  if cfg.enable_nanoda?.getD false && !externalKernels.isEmpty then
    throw <| .userError "Cannot use enable_nanoda and an external kernel list at the same time, register nanoda in the list instead."

  for (kernelName, kernelCommand) in externalKernels do
    if kernelCommand.isEmpty then
      throw <| .userError s!"{kernelName} has an empty command"
  if cfg.enable_nanoda?.getD false then
    let whichNanoda := nanodaOverride?.getD defaultNanoda
    externalKernels := externalKernels.insert "nanoda" #[whichNanoda]
  else if let some nanodaOverride := nanodaOverride? then
    externalKernels := externalKernels.modify "nanoda" fun cmd => cmd.set! 0 nanodaOverride
  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.map String.toName,
    definitionNames := cfg.definition_names.getD #[] |>.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    leanPrefix := leanPrefix,
    gitLocation := gitLocation,
    whichLean4Export := whichLean4Export,
    whichLandrun := whichLandrun,
    externalKernels := externalKernels
  }
end Comparator

unsafe def main (args : List String) : IO Unit := do
  let fromFiles := args[0]? == some "--exports"
  let fromLocal := args[0]? == some "--local-objects"
  let args := if fromFiles || fromLocal then args.drop 1 else args
  let some (configPath : String) := args[0]?
    | throw <| .userError "Expected config file path as first argument."
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  if fromLocal then
    Comparator.M.run Comparator.compareLocalObjects config
  else if fromFiles then
    let some challenge := args[1]? | throw <| IO.userError "Missing challenge export"
    let some solution := args[2]? | throw <| IO.userError "Missing solution export"
    Comparator.M.run (Comparator.compareExports challenge solution) config
  else
    Comparator.M.run Comparator.compareIt config
