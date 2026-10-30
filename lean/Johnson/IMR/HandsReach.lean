-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HandsReach.lean: KIND-FREE: IT IMPORTS Johnson/IMR/HandsFence.lean AND Johnson/Top/H0/Walk/Reach.lean (StepYes · Reach · reach_of_fold · Reach.fold · step_less) AND Johnson/Desc/Sound/Gather.lean (roundsFit_len) ALONE: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: HandsR AT THE FENCE «REACHED», AND WHAT FALLS THERE.
THE POINT. At the fence Fk k s := Reach ft bs start k (z, s) THE STATE BEHIND AN ACCEPTING STEP IS REACHED TOO (reach_next). SO WHATEVER IS KNOWN AT EVERY REACHED STATE NEED NOT BE HANDED ON BY ANY SUB-PROTOCOL: a field of HandsR whose sentence at border k + 1 is such a fact IS PAID AT EVERY ROW AT ONCE. So for «book»: bookAt_whole (Johnson/IMR/BookAtWhole.lean) says bookAt at the state
behind every cut of the fold: under it the field «book», and with it every share's two premises on the plan's counts (hT | hM), fall at all rows (book_of_reach · HandsR.of_five).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.

  yes_stepYes       an accepting step (Yes) is StepYes of Johnson/Top/H0/Walk/Reach.lean (as many rounds as declared; just the columns read).
  reach_next        reached in front · the sub-protocol at that number accepts ⟹ reached behind.
  RF ft bs start z  the fence.
  fence_reach       x_at_cutR's premise hF at that fence: a theorem (reach_of_fold, Reach.lean).
  x_at_reach        HandsR (RF …) at every sub-protocol · X 0 at the first state, if it bears no mark ⟹ X k AT EVERY REACHED STATE WITHOUT A MARK.
  field_of_reach    a sentence that holds at every reached state holds behind every accepting step from a reached state.
  book_of_reach · HandsR.of_five   «book» from «bookAt at every reached state»; HandsR from the other five fields and that.

  counts_of_reach   THE PLAN's TWO COUNTS AT NEIGHBOURS ARE THEOREMS UNDER THE FENCE: an accepting step from a reached state that adds dT trees and dM oracle messages shows them.
  handsR_of_counts · handsR_of_same   A TOOL FOR EVERY KIND's FILES: A SHARE THAT ENDS IN Hands UNDER THE PLAN's TWO COUNTS (hT | hM) STANDS AT HandsR (RF …) WITHOUT THEM: NO PROOF IS RETYPED.

What is not claimed. HandsR at any sub-protocol. bookAt at any state. No soundness.
-/
import Johnson.IMR.HandsFence
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.Gather

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt rowsHeld membersHeld bookAt)
open Johnson.Desc.First.Walk.Tied (StepYes Reach)
open ProofFile (Cl)

/-- An accepting step is StepYes (Johnson/Top/H0/Walk/Reach.lean). -/
theorem yes_stepYes {ft : Nat} {b : Block S Cl} {s s' : S} (h : Yes ft b s s') :
    StepYes ft b s s' := by
  obtain ⟨rs, cols, n, hy⟩ := h
  have h1 := (VerifiableInference.Desc.step_inv ft b s s' rs cols n hy).1
  exact ⟨rs, cols.take n, VerifiableInference.Desc.Sound.roundsFit_len _ _ h1,
    Johnson.Desc.First.Walk.Tied.step_less hy⟩

variable {P : Type}

/-- **Reached in front, an accepting step: reached behind.** -/
theorem reach_next {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {k : Nat} {z : P}
    {s s' : S} {b : Block S Cl} (h : Reach ft bs start k (z, s)) (hb : bs[k]? = some b)
    (hy : Yes ft b s s') : Reach ft bs start (k + 1) (z, s') :=
  Reach.succ h hb (yes_stepYes hy)

/-- **The fence «reached».** -/
def RF (ft : Nat) (bs : List (Block S Cl)) (start : P → S) (z : P) (k : Nat) (s : S) : Prop :=
  Reach ft bs start k (z, s)

theorem fence_reach {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} : ∀ j, j < bs.length → ∀ r,
    foldBlocks ft (bs.take j) (start z) rs cols = .ok r → RF ft bs start z j r.1 :=
  fun j hj r h => Johnson.Desc.First.Walk.Tied.reach_of_fold j (Nat.le_of_lt hj) r.1 rs r.2.1 cols
    r.2.2 h

/-- **X AT EVERY REACHED STATE WITHOUT A MARK.** -/
theorem x_at_reach {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (h : ∀ k b, bs[k]? = some b → HandsR (RF ft bs start z) N links ps E ft k b)
    (h0 : (start z).failed = none → XK N links ps E 0 (start z) = true) {k : Nat} {s : S}
    (hr : Reach ft bs start k (z, s)) (hu : s.failed = none) : XK N links ps E k s = true := by
  obtain ⟨hk, rs, cols, hf⟩ := hr.fold
  exact x_at_cutR h fence_reach h0 k hk _ hf hu

/-- A sentence that holds at every reached state holds behind every accepting step from a reached state. -/
theorem field_of_reach {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    {Φ : Nat → S → Prop} (hΦ : ∀ k s, Reach ft bs start k (z, s) → Φ k s) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b) {s s' : S} (hf : RF ft bs start z k s)
    (hy : Yes ft b s s') : Φ (k + 1) s' :=
  hΦ (k + 1) s' (reach_next hf hb hy)

/-- **THE FIELD «book», AT EVERY ROW AT ONCE.** -/
theorem book_of_reach {N : Numbers} {ps : List Place} {ft : Nat} {bs : List (Block S Cl)}
    {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b) {s s' : S} (hf : RF ft bs start z k s)
    (hy : Yes ft b s s') : bookAt N ps[k + 1]? s' = true :=
  field_of_reach (Φ := fun k s => bookAt N ps[k]? s = true) hB hb hf hy

/-- **HandsR at the fence «reached», from the other five fields and «bookAt at every reached state».** -/
theorem HandsR.of_five {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b)
    (mark : ∀ s s', RF ft bs start z k s → Yes ft b s s' → s.failed ≠ none → s'.failed ≠ none)
    (shape : ∀ s s', RF ft bs start z k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → shapeAt links ps[k + 1]? s' = true)
    (rows : ∀ s s', RF ft bs start z k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → rowsHeld N (openAt links ps (k + 1)) s' = true)
    (members : ∀ s s', RF ft bs start z k s → Yes ft b s s' → s.failed = none →
      s'.failed = none → XK N links ps E k s = true →
      membersHeld N (openAt links ps (k + 1)) s' = true)
    (more : ∀ s s', RF ft bs start z k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → E (k + 1) s' = true) :
    HandsR (RF ft bs start z) N links ps E ft k b :=
  ⟨mark, shape, rows, members, fun _ _ hf hy _ _ _ => book_of_reach hB hb hf hy, more⟩

/-- **THE PLAN's TWO COUNTS AT NEIGHBOURS, UNDER THE FENCE**: where an accepting step from a reached state adds dT trees and dM oracle messages, the plan's counts at the two borders differ by just these. (They are sentences on N alone: but an accepting step from a reached state is what shows them.) -/
theorem counts_of_reach {N : Numbers} {ps : List Place} {ft : Nat} {bs : List (Block S Cl)}
    {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b) {s s' : S} (hf : RF ft bs start z k s)
    (hy : Yes ft b s s') {dT dM : Nat} (hT : s'.book.trees.size = s.book.trees.size + dT)
    (hM : s'.st.oracles.size = s.st.oracles.size + dM) :
    N.treesAt ps[k + 1]? = N.treesAt ps[k]? + dT ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + dM := by
  have h1 := hB k s hf
  have h2 := book_of_reach hB hb hf hy
  unfold bookAt at h1 h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact ⟨by rw [← h2.1.1, ← h1.1.1, hT], by rw [← h2.2, ← h1.2, hM]⟩

/-- **A SHARE THAT ENDS IN Hands UNDER THE PLAN's TWO COUNTS STANDS AT HandsR (REACHED) WITHOUT THEM.** -/
theorem handsR_of_counts {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b) {dT dM : Nat}
    (adds : ∀ s s', Yes ft b s s' → s'.book.trees.size = s.book.trees.size + dT ∧
      s'.st.oracles.size = s.st.oracles.size + dM)
    (H : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + dT →
      N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + dM → Hands N links ps E ft k b) :
    HandsR (RF ft bs start z) N links ps E ft k b := by
  have key : ∀ s s', RF ft bs start z k s → Yes ft b s s' → Hands N links ps E ft k b :=
    fun s s' hf hy =>
      have c := counts_of_reach hB hb hf hy (adds s s' hy).1 (adds s s' hy).2
      H c.1 c.2
  exact ⟨fun s s' hf hy => (key s s' hf hy).mark s s' hy,
    fun s s' hf hy => (key s s' hf hy).shape s s' hy,
    fun s s' hf hy => (key s s' hf hy).rows s s' hy,
    fun s s' hf hy => (key s s' hf hy).members s s' hy,
    fun s s' hf hy => (key s s' hf hy).book s s' hy,
    fun s s' hf hy => (key s s' hf hy).more s s' hy⟩

/-- The like where the step adds nothing. -/
theorem handsR_of_same {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b)
    (same : ∀ s s', Yes ft b s s' → s'.book.trees.size = s.book.trees.size ∧
      s'.st.oracles.size = s.st.oracles.size)
    (H : N.treesAt ps[k + 1]? = N.treesAt ps[k]? → N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? →
      Hands N links ps E ft k b) : HandsR (RF ft bs start z) N links ps E ft k b :=
  handsR_of_counts (dT := 0) (dM := 0) hB hb same H

end IM

#print axioms IM.counts_of_reach
#print axioms IM.handsR_of_counts
#print axioms IM.handsR_of_same
#print axioms IM.yes_stepYes
#print axioms IM.reach_next
#print axioms IM.fence_reach
#print axioms IM.x_at_reach
#print axioms IM.field_of_reach
#print axioms IM.book_of_reach
#print axioms IM.HandsR.of_five
