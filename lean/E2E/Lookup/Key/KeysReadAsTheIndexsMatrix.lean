-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: the keys that the thread's witness spells must be the prover's keys. `keyVec` reads a matrix only at the rows of the
  lookup's runs and at columns below the key's, so the one thing that is left is that the stored table's cells spell the index's
  matrix there: `CellsSpellTheIndexsMatrix`, a premise by name.

E2E/Lookup/Key/KeysReadAsTheIndexsMatrix.lean. Theorems with proofs.

  `ARowThatTheKeysRead`          a row of the matrix that a lookup's runs name
  `keyAtReadsAlike`, `keysReadAlikeWhereTheMatricesDo`   `keyAt` and `keyVec` read alike where the matrices do
  `planMatrixIsTheWrittenOne`    in scope the plan's matrix has the written numbers
  `CellsSpellTheIndexsMatrix`    the debt that is left
  `keysReadAsTheIndexsMatrix`    **the join**: the premise `keys`, pointwise

Limits. `CellsSpellTheIndexsMatrix` is a premise: that the stored table holds the index's matrix is not said here. Nothing on any
property of a protocol.
-/
import E2E.Lookup.Key.LookupValuesAtTheNamedParts
import E2E.KeyMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Lookup.Key
open OnBytes
open OnBytes.Slice (GF GE readE toF)
open OnBytes.Params (WfLookup WfRun)
open ProofFile.Honest
open AtPublicFiles.KeyThread
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyFile (In1)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi keyVec keyAt matAt)
open Johnson.RunOne.KeyRows1 (plan₁)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)

/-! ## 1 Reading alike -/

/-- A row of the matrix that the keys of a lookup read: of a run of a part, at a place of the run, at a digit. -/
def ARowThatTheKeysRead (l : WfLookup) (y : Nat) : Prop :=
  ∃ part ∈ l.parts, ∃ r ∈ part.runs, ∃ t, t < r.places ∧ ∃ digit, digit < l.digitWeight.length ∧
    y = r.firstRow + t + digit * r.stride

theorem foldOfDigitsReadsAlike (first second : Nat → Nat → F) (row : Nat → Nat) (c : Nat) :
    ∀ (digits : List (F × Nat)) (a b : E), readE a = readE b →
      (∀ q ∈ digits, toF (first (row q.2) c) = toF (second (row q.2) c)) →
      readE (digits.foldl (fun s q => addE s (mulE (ofF q.1) (ofF (first (row q.2) c)))) a) =
        readE (digits.foldl (fun s q => addE s (mulE (ofF q.1) (ofF (second (row q.2) c)))) b)
  | [], _, _, same, _ => same
  | q :: digits, a, b, same, alike => by
    simp only [List.foldl_cons]
    refine foldOfDigitsReadsAlike first second row c digits _ _ ?_
      fun p hp => alike p (List.mem_cons_of_mem _ hp)
    rw [OnBytes.Slice.readE_add, OnBytes.Slice.readE_add, OnBytes.Slice.readE_mul,
      OnBytes.Slice.readE_mul, OnBytes.Slice.readE_ofF (first _ _), OnBytes.Slice.readE_ofF (second _ _),
      same, alike q List.mem_cons_self]

/-- **A key reads alike where the two matrices do, at the key's digits' rows.** -/
theorem keyAtReadsAlike (l : WfLookup) (first second : Nat → Nat → F) (r : WfRun) (t c : Nat)
    (alike : ∀ digit, digit < l.digitWeight.length →
      toF (first (r.firstRow + t + digit * r.stride) c) = toF (second (r.firstRow + t + digit * r.stride) c)) :
    readE (keyAt l first r t c) = readE (keyAt l second r t c) := by
  unfold keyAt
  refine foldOfDigitsReadsAlike first second (fun digit => r.firstRow + t + digit * r.stride) c _ _ _ rfl ?_
  intro q member
  have hAt := List.mem_zipIdx_iff_getElem?.1 member
  exact alike q.2 (List.getElem?_eq_some_iff.1 hAt).1

/-- **`keyVec` reads alike where the two matrices do**, at the rows that the lookup's runs name and the columns of a key. -/
theorem keysReadAlikeWhereTheMatricesDo (m : Wf.Matrix) (l : WfLookup) (first second : Nat → Nat → F)
    (alike : ∀ y, ARowThatTheKeysRead l y → ∀ c, c < 2 ^ m.kCol → toF (first y c) = toF (second y c))
    (part i : Nat) : readE (keyVec m l first part i) = readE (keyVec m l second part i) := by
  unfold keyVec
  dsimp only
  cases found : (((l.parts[part]?).map (·.runs)).getD []).find? (fun r =>
      decide (r.firstPlace ≤ i / 2 ^ m.kCol) &&
        decide (i / 2 ^ m.kCol < r.firstPlace + r.places)) with
  | none => rfl
  | some r =>
    have holds := List.find?_some found
    have inRuns := List.mem_of_find?_eq_some found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
    cases hPart : l.parts[part]? with
    | none =>
      rw [hPart] at inRuns
      cases inRuns
    | some p =>
      rw [hPart] at inRuns
      have hMember : p ∈ l.parts := List.mem_of_getElem? hPart
      refine keyAtReadsAlike l first second r _ _ fun digit inDigits => ?_
      exact alike _ ⟨p, hMember, r, inRuns, i / 2 ^ m.kCol - r.firstPlace, by omega, digit, inDigits, rfl⟩ _
        (Nat.mod_lt _ (Nat.two_pow_pos _))

/-! ## 2 The plan's matrix -/

/-- **In scope the plan's matrix has the written numbers.** -/
theorem planMatrixIsTheWrittenOne {files : VerifierAndGoals.PublicFiles} {source : Source} {numbers : H2U.PlaceNums}
    {later : LaterPlaces} (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) : (plan₁ (one₀ source)).m = ⟨kRef, 3076096⟩ := by
  obtain ⟨_, _, read, made, fromMade, -, -⟩ := sourced.source
  obtain ⟨-, -, shape, -, -⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO read) made fromMade sourced.named.plan
  show Wf.matrixOf source.Y.k.oneTime.lin = _
  rw [shape]
  exact AtPublicFiles.Key.item_written.2.2.2.2

/-! ## 3 The join -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec : Type} (filling : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (f : W₀ → Weights) (source : Source)

/-- **THE DEBT THAT IS LEFT**: at the rows that the lookup's keys read, and the columns of a key, the stored table's cells spell the
index's matrix. -/
def CellsSpellTheIndexsMatrix (number : Nat) : Prop :=
  ∀ (w₀ : W₀) (rc : Rc) y, ARowThatTheKeysRead (writtenStructure number) y → ∀ c, c < 2 ^ kRef →
    toF (matAt (plan₁ (one₀ source)).lin (filling.R.tab (filling.cells w₀ rc)) y c) = (f w₀).entry y c

/-- **THE KEYS THAT THE THREAD's WITNESS SPELLS READ AS THE PROVER's KEYS**, pointwise, at every part and every number. Conditional: the
description is sourced from the files in scope; the cells spell the index's matrix. -/
theorem keysReadAsTheIndexsMatrix {numbers : H2U.PlaceNums} {later : LaterPlaces} {files : VerifierAndGoals.PublicFiles}
    (sourced : KeySourced files source numbers later) (scope : VerifierAndGoals.InScope files = true) (number : Nat)
    (cells : CellsSpellTheIndexsMatrix filling f source number) (k : Coins Bk)
    (input : Local W₀ Rc Xi Unit) (heard : List Fmt.Drawn) (part i : Nat) :
    readE (keyVec (plan₁ (one₀ source)).m (writtenStructure number)
        (VerifiableInference.Desc.Key.matOf (plan₁ (one₀ source)) filling.R
          (filling.wit k input.w₀ input.rc heard [])) part i) =
      readE (keyReaderAt f number input part i) := by
  unfold keyReaderAt
  rw [planMatrixIsTheWrittenOne sourced scope]
  refine keysReadAlikeWhereTheMatricesDo _ _ _ _ (fun y row c column => ?_) part i
  show toF (matAt (plan₁ (one₀ source)).lin (filling.R.tab (filling.cells input.w₀ input.rc)) y c) =
    toF (OnBytes.Slice.ofF ((f input.w₀).entry y c))
  rw [OnBytes.Slice.toF_ofF]
  exact cells _ _ y row c column

end

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.foldOfDigitsReadsAlike
#print axioms AtPublicFiles.Lookup.Key.keyAtReadsAlike
#print axioms AtPublicFiles.Lookup.Key.keysReadAlikeWhereTheMatricesDo
#print axioms AtPublicFiles.Lookup.Key.planMatrixIsTheWrittenOne
#print axioms AtPublicFiles.Lookup.Key.keysReadAsTheIndexsMatrix
