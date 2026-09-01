import Lean.Elab.Command
import Lean.Elab.DeclarationRange

/-!
# Kernel-checked Boolean certificate declarations

`#kernel_checked_bool theoremName expression` elaborates the closed
`expression` at type `Bool`, then submits the theorem `expression = true`
with value `Eq.refl true` through ordinary `Lean.addDecl`.  Elaboration does
not evaluate the Boolean; the ordinary kernel declaration check establishes
the definitional equality exactly once.

This command is deliberately opt-in and should be imported only by generated
certificate replay modules.  It refuses both skipped kernel checking and open
expressions.  It does not use the native evaluator, VM evaluation, an unsafe
declaration, or a compiler-backed proof.
-/

open Lean Elab Command

syntax (name := kernelCheckedBoolDeclaration)
  "#kernel_checked_bool" ident term : command

@[command_elab kernelCheckedBoolDeclaration]
def elabKernelCheckedBoolDeclaration : CommandElab
  | stx@`(#kernel_checked_bool $theoremId:ident $checkTerm:term) =>
    withRef stx do
      if debug.skipKernelTC.get (← getOptions) then
        throwError
          "#kernel_checked_bool refuses to run with debug.skipKernelTC"
      let currentNamespace ← getCurrNamespace
      let theoremName := currentNamespace ++ theoremId.getId
      unless !(← getEnv).contains theoremName do
        throwErrorAt theoremId "declaration already exists: {theoremName}"
      let checkExpr ← liftTermElabM do
        let checkExpr ← Term.elabTermEnsuringType checkTerm (mkConst ``Bool)
        Term.synthesizeSyntheticMVarsNoPostponing
        let checkExpr ← instantiateMVars checkExpr
        if checkExpr.hasMVar then
          throwErrorAt checkTerm
            "#kernel_checked_bool expression contains unresolved metavariables"
        if checkExpr.hasFVar then
          throwErrorAt checkTerm
            "#kernel_checked_bool expression must be closed"
        pure checkExpr
      let theoremType := mkApp3
        (mkConst ``Eq [Level.succ Level.zero])
        (mkConst ``Bool) checkExpr (mkConst ``Bool.true)
      let theoremValue := mkApp2
        (mkConst ``Eq.refl [Level.succ Level.zero])
        (mkConst ``Bool) (mkConst ``Bool.true)
      addDeclarationRangesFromSyntax theoremName stx theoremId
      liftCoreM <| addDecl <| .thmDecl {
        name := theoremName
        levelParams := []
        type := theoremType
        value := theoremValue
      }
  | _ => throwUnsupportedSyntax
