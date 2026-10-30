-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchTerms.lean: THE BATCHING MEMBER's STEP ON SHAPES AND ITS ONE Bool AS PLAIN
TERMS IN PLAIN TABLES. batch_of_slots (BatchWhole.lean) states both through a RunsLaw that is built
of slots; a table of steps wants them written out. General laws; nothing is evaluated.

  `gatherFrom_congr`, **`batchGS_congr`**: the step on shapes hangs on the table of the runs on
    shapes at the order's pairs alone.
  **`preAllT`**, **`batchVT p runT preT os`**: the member's one Bool as a term in two plain tables:
    the seated runs; their premises' Bools.
  `preAllB_is`, **`batchV_is`**: batchV p R B os IS batchVT p R.run (fun o => (B o).preB) os.
  `preAllT_congr`, **`batchVT_congr`**: it hangs on the two tables at the pairs of the list alone.

Limits. Terms and their equations alone. batchVT = true CAN MEAN THAT LITTLE WAS TESTED: its first
clause is true where no ledger is open, its second where the draw refuses, and preAllT asks nothing
of the runs behind one that refuses. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchFrames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh ClaimSh)
open VerifiableInference.Desc.K9 (SegSort Where atS drawAlone ledgerEmpty)
open VerifiableInference.Desc.K9.Shape

/-! ## 1 The step on shapes -/

theorem gatherFrom_congr (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)} :
    ∀ (os : List (Nat × String)), (∀ o ∈ os, g o = g' o) → ∀ x,
      gatherFrom k g os x = gatherFrom k g' os x
  | [], _, _ => rfl
  | o :: os, h, x => by
    show (stepG k g x o).bind (gatherFrom k g os) = (stepG k g' x o).bind (gatherFrom k g' os)
    have e1 : stepG k g x o = stepG k g' x o := by
      unfold stepG
      rw [h o (by simp)]
    have e2 : gatherFrom k g os = gatherFrom k g' os :=
      funext fun y => gatherFrom_congr k os (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')) y
    rw [e1, e2]

theorem batchGS_congr (rows : Nat) (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (order : List (Nat × String)) (h : ∀ o ∈ order, g o = g' o) :
    batchGS rows k g order = batchGS rows k g' order := by
  funext a
  unfold batchGS batchG
  have e : addsG k g order = addsG k g' order := by
    funext b
    unfold addsG gatherG
    rw [gatherFrom_congr k order h]
  rw [e]

/-! ## 2 The one Bool -/

/-- The runs' premises along the gathering, in two plain tables. Behind a run that refuses nothing
more is asked: true. -/
def preAllT (runT : Nat × String → VerifiableInference.Desc.K9.Shape.Run)
    (preT : Nat × String → Nat → S → Bool) : List (Nat × String) → Nat → S → Bool
  | [], _, _ => true
  | o :: os, n, s =>
    preT o n s &&
      match runT o n s with
      | .ok y => preAllT runT preT os (n + y.1.length) y.2
      | .error _ => true

/-- **The member's one Bool, in two plain tables.** Where no ledger is open its first clause says
true; where the draw alone refuses, its second. -/
def batchVT (p : Where) (runT : Nat × String → VerifiableInference.Desc.K9.Shape.Run)
    (preT : Nat × String → Nat → S → Bool) (os : List (Nat × String)) (s : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  (s.fork?.map ledgerEmpty).getD true &&
    match (drawAlone (Cl := Claim) atS p).decide s rs gs with
    | .ok s₁ => preAllT runT preT os 0 s₁
    | .error _ => true

theorem preAllB_is {bs : List (Block S Claim)} {order : List (Nat × String)}
    (R : RunsLaw bs order) (B : ∀ o, RunLawB (R.law o)) :
    ∀ (os : List (Nat × String)) (n : Nat) (s : S),
      preAllB R B os n s = preAllT R.run (fun o => (B o).preB) os n s
  | [], _, _ => rfl
  | o :: os, n, s => by
    show ((B o).preB n s &&
      match R.run o n s with
      | .ok y => preAllB R B os (n + y.1.length) y.2
      | .error _ => true) = ((B o).preB n s &&
      match R.run o n s with
      | .ok y => preAllT R.run (fun o => (B o).preB) os (n + y.1.length) y.2
      | .error _ => true)
    cases R.run o n s with
    | error e => rfl
    | ok y =>
      dsimp only
      rw [preAllB_is R B os]

theorem batchV_is {bs : List (Block S Claim)} {order : List (Nat × String)} (p : Where)
    (R : RunsLaw bs order) (B : ∀ o, RunLawB (R.law o)) (os : List (Nat × String)) :
    batchV p R B os = batchVT p R.run (fun o => (B o).preB) os := by
  funext s rs gs
  unfold batchV batchVT
  cases (drawAlone (Cl := Claim) atS p).decide s rs gs with
  | error e => rfl
  | ok s₁ =>
    dsimp only
    rw [preAllB_is R B os]

theorem preAllT_congr {runT runT' : Nat × String → VerifiableInference.Desc.K9.Shape.Run}
    {preT preT' : Nat × String → Nat → S → Bool} :
    ∀ (os : List (Nat × String)), (∀ o ∈ os, runT o = runT' o ∧ preT o = preT' o) →
      ∀ (n : Nat) (s : S), preAllT runT preT os n s = preAllT runT' preT' os n s
  | [], _, _, _ => rfl
  | o :: os, h, n, s => by
    obtain ⟨e1, e2⟩ := h o (by simp)
    show (preT o n s &&
      match runT o n s with
      | .ok y => preAllT runT preT os (n + y.1.length) y.2
      | .error _ => true) = (preT' o n s &&
      match runT' o n s with
      | .ok y => preAllT runT' preT' os (n + y.1.length) y.2
      | .error _ => true)
    rw [e1, e2]
    cases runT' o n s with
    | error e => rfl
    | ok y =>
      dsimp only
      rw [preAllT_congr os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]

theorem batchVT_congr (p : Where)
    {runT runT' : Nat × String → VerifiableInference.Desc.K9.Shape.Run}
    {preT preT' : Nat × String → Nat → S → Bool} (os : List (Nat × String))
    (h : ∀ o ∈ os, runT o = runT' o ∧ preT o = preT' o) :
    batchVT p runT preT os = batchVT p runT' preT' os := by
  funext s rs gs
  unfold batchVT
  cases (drawAlone (Cl := Claim) atS p).decide s rs gs with
  | error e => rfl
  | ok s₁ =>
    dsimp only
    rw [preAllT_congr os h]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.gatherFrom_congr
#print axioms Johnson.AtFull.Shape.batchGS_congr
#print axioms Johnson.AtFull.Shape.preAllB_is
#print axioms Johnson.AtFull.Shape.batchV_is
#print axioms Johnson.AtFull.Shape.preAllT_congr
#print axioms Johnson.AtFull.Shape.batchVT_congr
#print axioms Johnson.AtFull.Shape.preAllT
#print axioms Johnson.AtFull.Shape.batchVT
