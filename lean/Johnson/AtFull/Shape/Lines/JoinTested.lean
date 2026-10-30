-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/JoinTested.lean: a test on the shape that a stretch of the run on shapes
returns, with no written value for that shape; and what such a fact gives under the premise AtMgA:
over the table's own steps, and at a state. General laws, general in the test; nothing is evaluated
here.

Why. Inside a link some components of the chain's shape are long, and the written values there are
not whole: at an attention link and at the head's link they leave out look and lookHeard
(PairAside.lean), at a layers' link named parts of look, lookHeard and own
(Lines/Layers/LayersPartsAside.lean). A caller who needs a Bool of the shape at such a place is
served by "the run returns some x, and the Bool accepts x", which one closed line can state: the
Bool of that line runs the last member and hands what it returns to the test. What such a line costs
is not said here.

Main names.
  `testedB r t`   the run's outcome r is a return, and t accepts what it returned.
  `RunsToTested m n start t`   at every record X₀ that publicOfO returns at the stored full-size
      files: from `start X₀` the n members from m on return some x with t x = true, over
      `shapeL (LWn X₀)`, the text of the table over a record of letters (TabLetters.lean).
  `runsToTested_of_line`   from `testedB` over `runOverLightTail` at every record.
  `RunsBetween.thenTested`   a piece (Lines/JoinRecords.lean) and, after it, a tested stretch are
      one tested stretch.
  `runsBetween_of_attentionFront`   the first members of an attention link up to and with its
      batching, as one piece, from the three closed facts P1, P2a, P2b of four_all (JoinAll.lean).
      It ends at the very term at which four_all's fourth fact starts.
  `RunsToTested.fromStart`   a tested stretch that starts at the written value before link n, with
      the front and the n links before it (Lines/JoinLinks.lean), is a tested stretch from startShA.
  `run_eq_runFrom_zero`   the run over the first n members is the run of n members from member 0 on.
  `RunsToTested.atTable`   a tested stretch from member 0 and from a constant start: under AtMgA at
      the stored full-size files, baseOf's return and the layout file's size, the run over the
      table's own steps returns some y that t accepts. By run_of_public_numerals
      (JoinKeepsLastShape.lean).
  `RunsToTested.atState`   so t accepts the shape of every state s with shapeJ at that number
      (Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean: the run over the members before returns the
      state's shape).

Limits. `RunsToTested` holds emptily if publicOfO returns nothing at these files; the two laws under
AtMgA take the layout file's size and so have a record (record_there, JoinAll.lean). It does not say
what x is. Nothing holds m + n at or below 358: from 358 on the table answers every number with the
seal's cell (Table.lean). `RunsToTested.atState` takes shapeJ at the state as a premise; nothing
here shows it at any state. That AtMgA has a member is not shown here. At VerifierAndGoals.storedPublicFiles and
OnBytes.secondHashFunction, the format's second hash function, alone. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinRecords
import Johnson.AtFull.Shape.Lines.JoinLinks
import Johnson.AtFull.Shape.JoinKeepsLastShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside
open VerifiableInference.Desc.First.Shape (ChainSh ClaimSh)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- "It returns x, and t accepts x." -/
def testedB (r : Except String ShA) (t : ShA → Bool) : Bool :=
  match r with
  | .ok x => t x
  | .error _ => false

/-- Where testedB accepts, the run returned a shape that t accepts. -/
theorem testedB_ok {r : Except String ShA} {t : ShA → Bool} (h : testedB r t = true) :
    ∃ x : ShA, r = .ok x ∧ t x = true := by
  cases r with
  | error e => cases h
  | ok x => exact ⟨x, rfl, h⟩

/-- From `start X₀` the n members from m on return some x that t accepts, over the text of the table
over a record of letters, at every record X₀ that publicOfO returns at the stored full-size files.
It does not say that a record is there, nor what x is. -/
def RunsToTested (m n : Nat) (start : Verify.Public → ShA) (t : ShA → Bool) : Prop :=
  ∀ X₀ : Verify.Public,
    publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
    ∃ x : ShA, (shapeL (LWn X₀)).runFrom m n (start X₀) = .ok x ∧ t x = true

/-- **A tested stretch from a line's fact at every record.** -/
theorem runsToTested_of_line (hint : Nat → List (Nat × Nat)) (m k : Nat)
    (start : Verify.Public → ShA) (t : ShA → Bool)
    (h : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      testedB (runOverLightTail hint X₀ m k (start X₀)) t = true) :
    RunsToTested m k start t := fun X₀ hX => by
  obtain ⟨x, e, ht⟩ := testedB_ok (h X₀ hX)
  exact ⟨x, (runFrom_eq_lightTail hint hX m k (start X₀)).trans e, ht⟩

/-- **A piece and, after it, a tested stretch are one tested stretch.** -/
theorem RunsBetween.thenTested {m n₁ n₂ : Nat} {a b : Verify.Public → ShA} {t : ShA → Bool}
    (h1 : RunsBetween m n₁ a b) (h2 : RunsToTested (m + n₁) n₂ b t) :
    RunsToTested m (n₁ + n₂) a t := fun X₀ hX => by
  obtain ⟨x, e, ht⟩ := h2 X₀ hX
  exact ⟨x, runFrom_chain _ (h1 X₀ hX) e, ht⟩

/-- **The members of an attention link up to and with its batching, as one piece**: four_all's first
three facts, sign for sign. The piece ends at the term at which four_all's fourth fact starts. -/
theorem runsBetween_of_attentionFront (hint : Nat → List (Nat × Nat))
    (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k : Nat) {l : Nat} (hl : l < 24) (ho : l % 2 = 1)
    (hm : m + k = 14 * l + 9) (j : Nat) (c₀ c₁ c₂ : ShA) (cl : List ClaimSh) (st : ChainSh)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2a : atXLC (fun X => frontB (frontH X l j (withLk c₁ (lkA hint m k c₀ X))) cl st) = true)
    (P2b : atXLC (fun X => backB (backH X l j
      (cl, withLkC st (pairH (frontH X l j (withLk c₁ (lkA hint m k c₀ X)))))) c₁.2 c₂) = true) :
    RunsBetween m (k + 1) (fun _ => c₀) fun X => withLk c₂ (lkB hint m k 1 c₀ c₁ X) :=
  fun _ hX => pieces_run hint hsz hX [.run k .pair c₁, .halves l j cl st c₂] m (fun _ => c₀)
    ⟨P1, ⟨hl, ho, hm, P2a, P2b⟩, trivial⟩

/-- **From startShA**: the front, the n links before, and a tested stretch that starts at the
written value before link n. -/
theorem RunsToTested.fromStart (border : Nat → ShA) (n : Nat)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < n → RunsAll (14 * l + 1) 14 (border l) (border (l + 1))) {k : Nat}
    {t : ShA → Bool} (inLink : RunsToTested (14 * n + 1) k (fun _ => border n) t) :
    RunsToTested 0 (14 * n + 1 + k) (fun _ => startShA) t := by
  have toLink : RunsAll 0 (1 + 14 * n) startShA (border n) :=
    RunsAll.chain front (links_chain border n links)
  have first : 0 + (1 + 14 * n) = 14 * n + 1 := by omega
  have count : 1 + 14 * n + k = 14 * n + 1 + k := by omega
  rw [← count]
  exact RunsBetween.thenTested (RunsAll.runsBetween toLink) (by rw [first]; exact inLink)

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- The run over the first n members is the run of n members from member 0 on. -/
theorem run_eq_runFrom_zero (Z : ProofFile.Honest.Shape S) (n : Nat) (a : Z.Sh) :
    Z.run n a = Z.runFrom 0 n a := by
  have e := ProofFile.Honest.run_add Z 0 n a
  rw [Nat.zero_add] at e
  exact e

/-- **A tested stretch from member 0, over the table's own steps**: under AtMgA and baseOf's
return. -/
theorem RunsToTested.atTable (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {n : Nat} {a : ShA}
    {t : ShA → Bool} (hr : RunsToTested 0 n (fun _ => a) t) :
    ∃ y : ShA, (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run n a = .ok y ∧ t y = true := by
  obtain ⟨X₀, hX⟩ := record_there hsz
  obtain ⟨y, e, ht⟩ := hr X₀ hX
  have fromZero : (shapeL (LWn X₀)).run n a = .ok y :=
    (run_eq_runFrom_zero (shapeL (LWn X₀)) n a).trans e
  have atTable := run_of_public_numerals hsz h hB (a := a) (e := y) (n := n) ⟨X₀, hX, fromZero⟩
  exact ⟨y, atTable, ht⟩

/-- **The test accepts the state's shape**, at a state s of which the run over the n members before
returns the shape. -/
theorem RunsToTested.atState (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {n : Nat} {a : ShA}
    {t : ShA → Bool} (hr : RunsToTested 0 n (fun _ => a) t) (s : S)
    (hJ : ProofFile.Honest.shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a n s) :
    t (shA s) = true := by
  obtain ⟨y, e, ht⟩ := hr.atTable hsz h hB
  obtain rfl : shA s = y := Except.ok.inj (Eq.trans (Eq.symm hJ) e)
  exact ht

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.testedB
#print axioms Johnson.AtFull.Shape.testedB_ok
#print axioms Johnson.AtFull.Shape.RunsToTested
#print axioms Johnson.AtFull.Shape.runsToTested_of_line
#print axioms Johnson.AtFull.Shape.RunsBetween.thenTested
#print axioms Johnson.AtFull.Shape.runsBetween_of_attentionFront
#print axioms Johnson.AtFull.Shape.RunsToTested.fromStart
#print axioms Johnson.AtFull.Shape.run_eq_runFrom_zero
#print axioms Johnson.AtFull.Shape.RunsToTested.atTable
#print axioms Johnson.AtFull.Shape.RunsToTested.atState
