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

syntax (name := kernelCheckedBoolFamilyDeclaration)
  "#kernel_checked_bool_family" ident num term : command

private def addKernelCheckedBoolDeclaration
    (theoremName : Name) (checkExpr : Expr) : CoreM Unit := do
  let theoremType := mkApp3
    (mkConst ``Eq [Level.succ Level.zero])
    (mkConst ``Bool) checkExpr (mkConst ``Bool.true)
  let theoremValue := mkApp2
    (mkConst ``Eq.refl [Level.succ Level.zero])
    (mkConst ``Bool) (mkConst ``Bool.true)
  addDecl <| .thmDecl {
    name := theoremName
    levelParams := []
    type := theoremType
    value := theoremValue
  }

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
      addDeclarationRangesFromSyntax theoremName stx theoremId
      liftCoreM <| addKernelCheckedBoolDeclaration theoremName checkExpr
  | _ => throwUnsupportedSyntax

/-- Kernel-check an indexed family one member at a time.  The generated
theorems are named by appending the zero-based index to the supplied prefix.
Keeping the declarations separate is important: no large conjunction is
ever normalized, and later assembly can reuse each opaque equality. -/
@[command_elab kernelCheckedBoolFamilyDeclaration]
def elabKernelCheckedBoolFamilyDeclaration : CommandElab
  | stx@`(#kernel_checked_bool_family $theoremPrefix:ident
      $countSyntax:num $checkFamily:term) =>
    withRef stx do
      if debug.skipKernelTC.get (← getOptions) then
        throwError
          "#kernel_checked_bool_family refuses to run with debug.skipKernelTC"
      let some count := countSyntax.raw.isNatLit?
        | throwErrorAt countSyntax "family count must be a natural literal"
      if count = 0 then
        throwErrorAt countSyntax "family count must be positive"
      let currentNamespace ← getCurrNamespace
      let theoremPrefixName := currentNamespace ++ theoremPrefix.getId
      let familyExpr ← liftTermElabM do
        let expectedType ← mkArrow (mkConst ``Nat) (mkConst ``Bool)
        let familyExpr ← Term.elabTermEnsuringType checkFamily expectedType
        Term.synthesizeSyntheticMVarsNoPostponing
        let familyExpr ← instantiateMVars familyExpr
        if familyExpr.hasMVar then
          throwErrorAt checkFamily
            "#kernel_checked_bool_family expression contains unresolved metavariables"
        if familyExpr.hasFVar then
          throwErrorAt checkFamily
            "#kernel_checked_bool_family expression must be closed"
        pure familyExpr
      for index in [:count] do
        let theoremName := theoremPrefixName.appendAfter (toString index)
        unless !(← getEnv).contains theoremName do
          throwErrorAt theoremPrefix "declaration already exists: {theoremName}"
        let checkExpr := mkApp familyExpr (mkNatLit index)
        addDeclarationRangesFromSyntax theoremName stx theoremPrefix
        liftCoreM <| addKernelCheckedBoolDeclaration theoremName checkExpr
  | _ => throwUnsupportedSyntax
