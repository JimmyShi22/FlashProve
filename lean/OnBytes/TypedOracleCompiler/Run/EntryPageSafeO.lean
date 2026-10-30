-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryPageSafeO.lean: the family of typed oracles of the page of an entry's judge, in
the form that a run can evaluate, with a hash function on bytes an argument.

Definitions, and statements with their proofs. `famSafeG` (OnBytes/TypedOracleCompiler/Run/EntryPageSafeG.lean)
keeps each answer as a digest, and a digest is a function from 256 places to bits: a run may then
hash a string anew at every bit that it reads (of a like form the head of
OnBytes/TypedOracleCompiler/Run/CodingFnThin.lean reports 256 calls for one digest). `famSafe`
(OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean) hashes the blocks' strings first, as bytes, and decodes them
afterwards. Here that text stands with a letter O : `ByteArray → ByteArray` where `famSafe` has the
format's oracle.


Main names (namespace `TypedOracleCompiler.Run.EntryPageSafe`):
  `gOf O`: the function on bit strings that is made of O: the string as bytes; O; the first 256
    bits.
  `gOf_oracle`: at `Fmt.oracle` it is `Run.oBits`.
  `ansO`, `famSafeO`: `ansS` and `famSafe` with O.
  `famSafeO_eq`: it is `readBlocks (implE …) (gOf O)`, at every O, oracle and query.
  `famSafeO_G`: it is `famSafeG` at `gOf O`.

Limits.
  1. Of these two terms nothing is measured: that a run hashes anew at every bit under `famSafeG`,
     and does not under `famSafeO`, rests on that head's report of a like pair and on the likeness
     of the texts. That either comes home is a fact of a run: of `famSafeG` none has been made; the
     closed check that is written with `famSafeO` (`runEntryFull`, `runEntrySmall`,
     OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) is run by an asking file outside the library,
     lean/Ask/EntryRecord.lean, whose head tells what that took.
  2. Not every function on bit strings is `gOf O` for some O that a program can hold; the theorems
     over all g stand at `famSafeG`.
  3. All that the heads of EntryPageSafe.lean and EntryPageSafeG.lean do not claim. No probability
     stands here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPageSafeG

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

/-- The function on bit strings that is made of a function O on bytes: the string as bytes, by the
library's looping way; O; the first 256 bits of what O returns. -/
def gOf (O : ByteArray → ByteArray) : Fam (rom 256) := fun _ s => digS (O (toBytesT s))

/-- At the format's oracle on bytes it is the realised oracle on bit strings. -/
theorem gOf_oracle : gOf _root_.Fmt.oracle = oBits :=
  funext fun _ => funext fun s => hashS_eq s

variable {Sd : Type} [DecidableEq Sd] (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry) (dd : Sd)
  (P : PinsE D early e) (K : ℕ) (n : ℕ) (back : StrCode (AllPts 256 K (Le D early e)))
  (O : ByteArray → ByteArray)

/-- `ansS` with O where that has the format's oracle: one byte string for each block. -/
def ansO : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 (Le D early e) o → Array ByteArray
  | .leaf, q => #[O (toBytesT (codeLeaf D early e P K n back q))]
  | .node, q => #[O (toBytesT (codeNode D early e P K back q))]
  | .fb .link, q =>
      Array.ofFn (n := K + 1) fun j => O (toBytesT (codeLink D early e dd P K back q j))
  | .fb .test, q =>
      Array.ofFn (n := K + 1) fun j => O (toBytesT (codeSeed D early e dd P K back q j))
  | _, _ => #[]

/-- The page's family with a hash function on bytes an argument, for a run: `famSafe`'s text with O:
the blocks' strings are hashed first, as bytes, then decoded. -/
def famSafeO : Fam (typedOracleFamily 256 K (Le D early e)) := fun o q =>
  if asked o = true then decS K o (ansO D early e dd P K n back O o q)
  else famRun dd P K (Vn D early e P n) back (gOf O) o q

/-- It is the family that is read out of `gOf O` through `EntryPage.implE`: every O. -/
theorem famSafeO_eq :
    famSafeO D early e dd P K n back O =
      readBlocks (implE P dd K (Vn D early e P n) back) (gOf O) := by
  funext o q
  unfold famSafeO
  have one : ∀ (s : List Bool) (j : Fin 1),
      digS ((#[O (toBytesT s)] : Array ByteArray).getD j.val ByteArray.empty) = gOf O () s := by
    intro s j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have many : ∀ (f : Fin (K + 1) → List Bool) (j : Fin (K + 1)),
      digS ((Array.ofFn (n := K + 1) fun i => O (toBytesT (f i))).getD j.val ByteArray.empty) =
        gOf O () (f j) := by
    intro f j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
    rfl
  have rest : ∀ o' q', asked o' = false →
      (if asked o' = true then decS K o' (ansO D early e dd P K n back O o' q')
        else famRun dd P K (Vn D early e P n) back (gOf O) o' q') =
        readBlocks (implE P dd K (Vn D early e P n) back) (gOf O) o' q' := fun o' q' h =>
    (if_neg (by rw [h]; exact Bool.false_ne_true)).trans
      (congrFun (congrFun (famRun_eq _ _ _ _ _ _) _) _)
  cases o with
  | leaf =>
    refine (if_pos (rfl : asked .leaf = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .leaf).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (gOf O ()) (codeLeaf_eq D early e dd P K n back q j))
  | node =>
    refine (if_pos (rfl : asked .node = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .node).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (gOf O ()) (codeNode_eq D early e dd P K n back q j))
  | fb t =>
    cases t with
    | link =>
      refine (if_pos (rfl : asked (.fb .link) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .link)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (gOf O ()) (codeLink_eq D early e dd P K n back q j))
    | test =>
      refine (if_pos (rfl : asked (.fb .test) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .test)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (gOf O ()) (codeSeed_eq D early e dd P K n back q j))
    | onl => exact rest (.fb .onl) q rfl
  | rleaf => exact rest .rleaf q rfl
  | rnode => exact rest .rnode q rfl
  | g t => exact rest (.g t) q rfl
  | ann => exact rest .ann q rfl
  | other => exact rest .other q rfl
  | fbw t k => exact rest (.fbw t k) q rfl

/-- It is `famSafeG` at `gOf O`. -/
theorem famSafeO_G : famSafeO D early e dd P K n back O = famSafeG D early e dd P K n back (gOf O)
  :=
  (famSafeO_eq D early e dd P K n back O).trans (famSafeG_eq D early e dd P K n back (gOf O)).symm

end TypedOracleCompiler.Run.EntryPageSafe
