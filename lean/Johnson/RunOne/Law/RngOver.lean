-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngOver.lean: THE RANGES' TEST OF A KEY FILE's FIRST CHAIN STANDS OVER THE KIND K12's BLOCK, STEP FOR STEP. Statements with proofs.
OBJECT. `Block.step` of `rangesTest laid back N` (Johnson/Desc/Key/Ranges.lean), and of it at a key file's own halves, as Johnson/Desc/Key/Chain1.lean's firstChain seats it.
USER. Johnson/RunOne/Law/RngOverCoin.lean (rounds_over, step_over, enter_one); K12SeatsLaw.lean and K12SeatsHeld.lean (form_over).
LETTERS. All free: the state σ, the type of claims Cl, the two halves laid and back, the place's numbers N. No premise but the step's yes.

The seat (Johnson/Desc/Key/Ranges.lean: rangesTest laid back N) is no bare Block.inside: it bears a name of its own, asks more on the plan, and stands at whatever type of claims its chain has. A law of the kind's block at its own record, (proximityTestKind guardedProximityTestParts p : Block T12 Unit), goes over to a block that stands over it under ONE SENTENCE ON THAT BLOCK's STEP. Here that sentence is proved, in plain words, with no frame's type in it:
  rounds_over: the seat declares the kind's block's rounds (the very list).
  decide_over: the seat's decision is: enter, the kind's block's decision, leave. bindE: where a bind returns.
  step_both: THE SENTENCE, AS AN "IF AND ONLY IF"; step_over and step_back are its two directions.
  step_over: where the seat's step goes from s to s' on whatever first tree's number, rounds and columns, taking k columns: there are t, which the seat's entering (reading, then asking) returns at s, and t', which the seat's leaving lays back as s', such that the kind's block's step goes from t to t' on the same number, rounds and columns, taking k.
  form_over: what Block.step asks of rounds and columns hangs on the declared rounds alone (over step_iff, Johnson/Top/H0/StepLaws/StepLaws.lean).
  step_back: the converse: so the sentence says all that the seat's step is.
  enter_one: the entering names at most one t.
  keyD_rounds (the LENGTHS of the two lists of rounds), keyD_step, keyD_one: the three at a key file's own halves (Key.enterRanges one, Key.leaveRanges) and type of claims.
Limits. On the test on the plan nothing (Johnson/RunOne/Law/RngAsked.lean: planOk_ok). A block that says no to all meets step_over. Nothing on soundness.
Of the key file's description (Johnson/Desc/Key/Chain1.lean) it names enterRanges and leaveRanges alone.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.RunOne.Law.RngAnyCl
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngOver
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn step_iff)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key
open Johnson.RunOne.Law.RngAnyCl (same_k12)

variable {σ Cl : Type} (laid : σ → Except String RangesLaid) (back : σ → T12 → Except String σ) (N : H2U.PlaceNums)

/-- The seat declares the kind's block's rounds. -/
theorem rounds_over : (rangesTest laid back N : Block σ Cl).rounds = (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).rounds :=
  (same_k12 (A := Cl) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds

/-- The seat's decision: enter, the kind's block's decision, leave. -/
theorem decide_over (s : σ) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (rangesTest laid back N : Block σ Cl).decide s rs gs =
      (enterAndAsk laid (rangesParams N) s).bind fun t =>
        ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide t rs gs).bind (back s) := by
  show (enterAndAsk laid (rangesParams N) s).bind (fun t =>
      ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).decide t rs gs).bind (back s)) = _
  rw [(same_k12 (A := Cl) (B := Unit) guardedProximityTestParts (rangesParams N)).decide]

theorem bindE {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b :=
  VerifiableInference.Desc.Except.bind_eq_ok x f b

/-- What Block.step asks of rounds and columns, what it shows the decision and how many columns it takes hang on the block's declared rounds alone. -/
theorem form_over {S S' A A' : Type} (b : Block S A) (b' : Block S' A') (h : b.rounds = b'.rounds) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (b.Fits ft rs cols ↔ b'.Fits ft rs cols) ∧ b.shown ft rs cols = b'.shown ft rs cols ∧ b.want ft rs = b'.want ft rs := by
  unfold Block.Fits Block.shown Block.want
  rw [h]
  exact ⟨Iff.rfl, rfl, rfl⟩

/-- **The seat's step is the kind's block's step between the seat's two halves.** -/
theorem step_both (ft : Nat) (s s' : σ) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    (rangesTest laid back N : Block σ Cl).step ft s rs cols = .ok (s', k) ↔
      ∃ t t', enterAndAsk laid (rangesParams N) s = .ok t ∧
        (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).step ft t rs cols = .ok (t', k) ∧ back s t' = .ok s' := by
  obtain ⟨f1, f2, f3⟩ := form_over (rangesTest laid back N : Block σ Cl) (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit)
    (rounds_over laid back N) ft rs cols
  rw [step_iff, decide_over, f1, f2, f3]
  constructor
  · rintro ⟨h1, h3, h4⟩
    obtain ⟨t, ht, h5⟩ := bindE.1 h3
    obtain ⟨t', ht', h6⟩ := bindE.1 h5
    exact ⟨t, t', ht, (step_iff _ _ _ _ _ _ _).2 ⟨h1, ht', h4⟩, h6⟩
  · rintro ⟨t, t', ht, hs, hb⟩
    obtain ⟨h1, h3, h4⟩ := (step_iff _ _ _ _ _ _ _).1 hs
    exact ⟨h1, bindE.2 ⟨t, ht, bindE.2 ⟨t', h3, hb⟩⟩, h4⟩

theorem step_over (ft : Nat) (s : σ) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : σ) (k : Nat)
    (h : (rangesTest laid back N : Block σ Cl).step ft s rs cols = .ok (s', k)) :
    ∃ t t', enterAndAsk laid (rangesParams N) s = .ok t ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).step ft t rs cols = .ok (t', k) ∧ back s t' = .ok s' :=
  (step_both laid back N ft s s' rs cols k).1 h

theorem step_back (ft : Nat) (s : σ) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : σ) (k : Nat) (t t' : T12)
    (h1 : enterAndAsk laid (rangesParams N) s = .ok t)
    (h2 : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).step ft t rs cols = .ok (t', k)) (h3 : back s t' = .ok s') :
    (rangesTest laid back N : Block σ Cl).step ft s rs cols = .ok (s', k) :=
  (step_both laid back N ft s s' rs cols k).2 ⟨t, t', h1, h2, h3⟩

/-- The entering names at most one record. -/
theorem enter_one (s : σ) (t₁ t₂ : T12) (h₁ : enterAndAsk laid (rangesParams N) s = .ok t₁)
    (h₂ : enterAndAsk laid (rangesParams N) s = .ok t₂) : t₁ = t₂ := Except.ok.inj (h₁.symm.trans h₂)

/-! ## At a key file's own halves -/

open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)

variable (one : OnBytes.Params.OneTime)

theorem keyD_rounds : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).rounds.length =
    (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).rounds.length := by rw [rounds_over]

theorem keyD_step (ft : Nat) (s : FirstState) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : FirstState) (k : Nat)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).step ft s rs cols = .ok (s', k)) :
    ∃ t t', enterAndAsk (enterRanges one) (rangesParams N) s = .ok t ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).step ft t rs cols = .ok (t', k) ∧ leaveRanges s t' = .ok s' :=
  step_over (enterRanges one) leaveRanges N ft s rs cols s' k h

theorem keyD_one (s : FirstState) (t₁ t₂ : T12) (h₁ : enterAndAsk (enterRanges one) (rangesParams N) s = .ok t₁)
    (h₂ : enterAndAsk (enterRanges one) (rangesParams N) s = .ok t₂) : t₁ = t₂ := enter_one (enterRanges one) N s t₁ t₂ h₁ h₂

end Johnson.RunOne.Law.RngOver

#print axioms Johnson.RunOne.Law.RngOver.rounds_over
#print axioms Johnson.RunOne.Law.RngOver.form_over
#print axioms Johnson.RunOne.Law.RngOver.step_both
#print axioms Johnson.RunOne.Law.RngOver.step_over
#print axioms Johnson.RunOne.Law.RngOver.step_back
#print axioms Johnson.RunOne.Law.RngOver.keyD_rounds
#print axioms Johnson.RunOne.Law.RngOver.keyD_step
#print axioms Johnson.RunOne.Law.RngOver.keyD_one
