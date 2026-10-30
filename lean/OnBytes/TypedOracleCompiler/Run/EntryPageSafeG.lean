-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryPageSafeG.lean: the family of typed oracles of the page of an entry's judge, in
`famSafe`'s text but for the answers, with the hash function an argument.

Definitions, and statements with their proofs. OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean writes the string
of a leaf query, a vertex query and a chain query under either tag by functions that name no hash
function (`codeLeaf`, `codeNode`, `codeLink`, `codeSeed`), ties each to the code of
`EntryPage.implE` at every query, and then hashes the strings at the format's realised oracle on bit
strings (`hashS`, `famSafe`). Here the last step is said once more with a letter g : `Fam (rom 256)`
in the place of that oracle. The text is that file's; nothing of the writing side is said again.

Main names (namespace `TypedOracleCompiler.Run.EntryPageSafe`):
  `ansG`, `decG`: the answer to a typed query as an array of digests, one for each block; the array
    as a typed answer.
  `famSafeG`: the family: `famSafe`'s text with g.
  `famSafeG_eq`: it is `readBlocks (implE …) g`, at every g, oracle and query.
  `famSafeG_oBits`: at `Run.oBits` it is `famSafe`: an equation of values; it says nothing of what a
    run of either costs.

Limits.
  1. That it comes home is a fact of a run, and no run of it has been made. What that costs at a g
    made of a hash on bytes is not measured. `famSafe` keeps the answers as byte strings and hashes
     bytes; this form keeps digests as g gives them, as functions on 256 places: a run may ask g
     anew at every bit that it reads (OnBytes/TypedOracleCompiler/Run/EntryPageSafeO.lean is written against that).
  2. At the oracles outside the four kinds it is the plain family (`famRun`), which by the head of
     EntryPageSafe.lean does not come home: if a run asked one, it would end without a verdict.
  3. The pins P are a letter. They hold two digests (of the public files; of the parameter bytes):
     that these are g's own answers is the caller's to see to.
  4. All that the head of EntryPageSafe.lean does not claim. No probability stands here. Nothing on
     soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPageSafe

set_option autoImplicit false

namespace TypedOracleCompiler.Run.EntryPageSafe
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.EntryPageRun
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.Chain162G TypedOracleCompiler.Run.KeyRanges TypedOracleCompiler.Strings
open TypedOracleCompiler.Run.EntryFirst (YE first0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} [DecidableEq Sd] (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry) (dd : Sd)
  (P : PinsE D early e) (K : ℕ) (n : ℕ) (back : StrCode (AllPts 256 K (Le D early e)))
  (g : Fam (rom 256))

/-- The answer to a typed query as data, the hash function an argument: one digest for each block.
-/
def ansG : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 (Le D early e) o → Array (Dig 256)
  | .leaf, q => #[g () (codeLeaf D early e P K n back q)]
  | .node, q => #[g () (codeNode D early e P K back q)]
  | .fb .link, q => Array.ofFn (n := K + 1) fun j => g () (codeLink D early e dd P K back q j)
  | .fb .test, q => Array.ofFn (n := K + 1) fun j => g () (codeSeed D early e dd P K back q j)
  | _, _ => #[]

/-- The digests as a typed answer. -/
def decG (o : TypedOracleCompiler.Compile.Batch.OracleName) (a : Array (Dig 256)) : rngOf 256 K o :=
  (rngEquiv 256 K o).symm fun j => a.getD j.val fun _ => false

/-- The page's family with the hash function an argument: `famSafe`'s text with g where that has the
realised oracle. -/
def famSafeG : Fam (typedOracleFamily 256 K (Le D early e)) := fun o q =>
  if asked o = true then decG K o (ansG D early e dd P K n back g o q)
  else famRun dd P K (Vn D early e P n) back g o q

/-- It is the family that is read out of g through `EntryPage.implE`, at every g, oracle and query.
-/
theorem famSafeG_eq :
    famSafeG D early e dd P K n back g = readBlocks (implE P dd K (Vn D early e P n) back) g := by
  funext o q
  unfold famSafeG
  have one : ∀ (s : List Bool) (j : Fin 1),
      ((#[g () s] : Array (Dig 256)).getD j.val fun _ => false) = g () s := by
    intro s j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have many : ∀ (f : Fin (K + 1) → List Bool) (j : Fin (K + 1)),
      ((Array.ofFn (n := K + 1) fun i => g () (f i)).getD j.val fun _ => false) = g () (f j) := by
    intro f j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
    rfl
  have rest : ∀ o' q', asked o' = false →
      (if asked o' = true then decG K o' (ansG D early e dd P K n back g o' q')
        else famRun dd P K (Vn D early e P n) back g o' q') =
        readBlocks (implE P dd K (Vn D early e P n) back) g o' q' := fun o' q' h =>
    (if_neg (by rw [h]; exact Bool.false_ne_true)).trans
      (congrFun (congrFun (famRun_eq _ _ _ _ _ _) _) _)
  cases o with
  | leaf =>
    refine (if_pos (rfl : asked .leaf = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .leaf).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (g ()) (codeLeaf_eq D early e dd P K n back q j))
  | node =>
    refine (if_pos (rfl : asked .node = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .node).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (g ()) (codeNode_eq D early e dd P K n back q j))
  | fb t =>
    cases t with
    | link =>
      refine (if_pos (rfl : asked (.fb .link) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .link)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (g ()) (codeLink_eq D early e dd P K n back q j))
    | test =>
      refine (if_pos (rfl : asked (.fb .test) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .test)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (g ()) (codeSeed_eq D early e dd P K n back q j))
    | onl => exact rest (.fb .onl) q rfl
  | rleaf => exact rest .rleaf q rfl
  | rnode => exact rest .rnode q rfl
  | g t => exact rest (.g t) q rfl
  | ann => exact rest .ann q rfl
  | other => exact rest .other q rfl
  | fbw t k => exact rest (.fbw t k) q rfl

/-- At the realised oracle it is `famSafe`. -/
theorem famSafeG_oBits : famSafeG D early e dd P K n back oBits = famSafe D early e dd P K n back :=
  (famSafeG_eq D early e dd P K n back oBits).trans (famSafe_eq D early e dd P K n back).symm

end TypedOracleCompiler.Run.EntryPageSafe
