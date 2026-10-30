-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/HandsDef.lean: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE
VERIFIER's STATE ALONE: THE TERMS AND THE RULES THAT NAME NO SEAT: A LIGHT FILE.
«ℕ» IS WRITTEN «Nat» (the file imports no Mathlib of its own); every name is IM.‹name›.
ON WORDS: «the state» is the value of type S that the description's fold carries from block to block; «the state's book» its list of commitment trees with the oracle messages' places.
IT IMPORTS: Johnson/Desc/First/PromiseRides.lean · BordersSucc.lean (and through them Borders.lean · BordersKeep.lean) · Johnson/Desc/ProofFile/LotCore.lean (for the type Cl of the fold's claims) · Johnson/Desc/Sound/SeatGuardChain.lean (Block.UnderR · step_under). NOTHING UNDER Johnson/IMR/.
A FORM WITH ITS HYPOTHESES COUNTED: NOTHING OF e₁ (the first chain's premise of fold_three_chains, Johnson/Desc/Plain/FileChains.lean) IS PROVED HERE.

  openAt · BK · XK   the statement's terms: the table's open set at border k · the four Bools of the table's promise that read the state and the plan's numbers alone · with further Bools E k, border by border.
  Yes ft b s s'     b's step says yes from the state s to the state s', at the first tree ft.
  Hands N links ps E ft k b WHAT IS ASKED OF ONE BLOCK: six fields: mark · shape · rows · members ·
  book · more.
  S1 · s1_of_hands  (S1) from Hands at each block. Both run over ALL states: see IMR/HandsFence.lean
  xk_parts          X k s, cut in its five.
  Yes.under · Hands.under   the hypothesis on a SEATED block is that on its lot's block: b.UnderR b' carries Hands from b' to b.
  Keeps4 · hands_quiet   at a quiet row (it closes and opens no class of rows and no pin) rows · members · book follow from one relation on the two states (Rq, Johnson/Desc/First/Link/Law/RbDef.lean, field by field) and two equations on the plan's numbers.
  hands_same        a block whose yes hands the state back asks only what the table says of its two borders.

What is not claimed. No block is shown here to meet its hypothesis. (S0). That X is inductive at a sender or a switch. The promise's other half; the ties (t1) · (t3) · (t4) · (t5). No soundness.
-/
import Johnson.Desc.First.PromiseRides
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Item openSets start shapeAt rowsHeld membersHeld
  bookAt stepOpen rowOf quietRow)
open ProofFile (Cl)

/-! ## 1 The statement's terms -/

/-- The table's open set at border k. -/
def openAt (links : List ModelPart) (ps : List Place) (k : Nat) : List Item :=
  ((openSets links ps (start links))[k]?).getD []

/-- The four Bools of the table's promise that read the record and the plan's numbers alone. -/
def BK (N : Numbers) (links : List ModelPart) (ps : List Place) (k : Nat) (s : S) : Bool :=
  shapeAt links ps[k]? s && rowsHeld N (openAt links ps k) s &&
    membersHeld N (openAt links ps k) s && bookAt N ps[k]? s

/-- With further Bools on the record. -/
def XK (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool) (k : Nat) (s : S) : Bool :=
  BK N links ps k s && E k s

/-- The block's step says yes from s to s', at the first tree ft (the number of trees that stand in front of the chain: the caller's letter; in other files' walks: 0). -/
def Yes (ft : Nat) (b : Block S Cl) (s s' : S) : Prop :=
  ∃ (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (n : Nat),
    b.step ft s rs cols = .ok (s', n)

/-- **What is asked of one block.** -/
structure Hands (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool) (ft k : Nat)
    (b : Block S Cl) : Prop where
  mark : ∀ s s', Yes ft b s s' → s.failed ≠ none → s'.failed ≠ none
  shape : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → XK N links ps E k s = true →
    shapeAt links ps[k + 1]? s' = true
  rows : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → XK N links ps E k s = true →
    rowsHeld N (openAt links ps (k + 1)) s' = true
  members : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → XK N links ps E k s = true →
    membersHeld N (openAt links ps (k + 1)) s' = true
  book : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → XK N links ps E k s = true →
    bookAt N ps[k + 1]? s' = true
  more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → XK N links ps E k s = true →
    E (k + 1) s' = true

/-- **(S1)**, at a chain. -/
def S1 (N : Numbers) (links : List ModelPart) (E : Nat → S → Bool) (ft : Nat) (c : Chain S Cl) : Prop :=
  ∀ k b, c.blocksInOrder[k]? = some b → ∀ s s', Yes ft b s s' →
    (s.failed ≠ none → s'.failed ≠ none) ∧
      (s.failed = none → s'.failed = none → XK N links (c.blocksInOrder.map (·.place)) E k s = true →
        XK N links (c.blocksInOrder.map (·.place)) E (k + 1) s' = true)

theorem s1_of_hands {N : Numbers} {links : List ModelPart} {E : Nat → S → Bool} {ft : Nat} {c : Chain S Cl}
    (h : ∀ k b, c.blocksInOrder[k]? = some b → Hands N links (c.blocksInOrder.map (·.place)) E ft k b) :
    S1 N links E ft c := by
  intro k b hb s s' hy
  have H := h k b hb
  refine ⟨H.mark s s' hy, fun h0 h1 hx => ?_⟩
  unfold XK BK
  rw [H.shape s s' hy h0 h1 hx, H.rows s s' hy h0 h1 hx, H.members s s' hy h0 h1 hx,
    H.book s s' hy h0 h1 hx, H.more s s' hy h0 h1 hx]
  rfl

theorem xk_parts {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool} {k : Nat} {s : S}
    (h : XK N links ps E k s = true) :
    shapeAt links ps[k]? s = true ∧ rowsHeld N (openAt links ps k) s = true ∧
      membersHeld N (openAt links ps k) s = true ∧ bookAt N ps[k]? s = true ∧ E k s = true := by
  unfold XK BK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  exact ⟨a, b, c, d, e⟩

/-! ## 2 From the seated block to the lot's block -/

theorem Yes.under {ft : Nat} {b b' : Block S Cl} (hU : b.UnderR b') {s s' : S} (h : Yes ft b s s') :
    Yes ft b' s s' := by
  obtain ⟨rs, cols, n, e⟩ := h
  exact ⟨rs, cols, n, VerifiableInference.Desc.step_under hU e⟩

/-- **The hypothesis on a seated block is that on its lot's block.** -/
theorem Hands.under {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool} {ft k : Nat}
    {b b' : Block S Cl} (hU : b.UnderR b') (H : Hands N links ps E ft k b') :
    Hands N links ps E ft k b :=
  ⟨fun s s' hy => H.mark s s' (hy.under hU), fun s s' hy => H.shape s s' (hy.under hU),
    fun s s' hy => H.rows s s' (hy.under hU), fun s s' hy => H.members s s' (hy.under hU),
    fun s s' hy => H.book s s' (hy.under hU), fun s s' hy => H.more s s' (hy.under hU)⟩

/-! ## 3 At a quiet row -/

/-- The one relation: the four things that the three Bools read are as they were. -/
def Keeps4 (s s' : S) : Prop :=
  s'.st.groups = s.st.groups ∧ s'.book.place = s.book.place ∧
    s'.book.trees.size = s.book.trees.size ∧ s'.st.oracles.size = s.st.oracles.size

/-- **At a quiet row three of the six fields follow from Keeps4 and two equations on the plan's numbers.** -/
theorem hands_quiet {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool} {ft k : Nat}
    {b : Block S Cl} {p : Place} (hp : ps[k]? = some p) (hq : quietRow (rowOf links p) = true)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (hK : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none → Keeps4 s s')
    (mark : ∀ s s', Yes ft b s s' → s.failed ≠ none → s'.failed ≠ none)
    (shape : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → shapeAt links ps[k + 1]? s' = true)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → E (k + 1) s' = true) : Hands N links ps E ft k b := by
  have hO : openAt links ps (k + 1) = stepOpen (openAt links ps k) (rowOf links p) :=
    VerifiableInference.Desc.First.openSets_succ links ps (start links) k p hp
  refine ⟨mark, shape, fun s s' hy h0 h1 hx => ?_, fun s s' hy h0 h1 hx => ?_,
    fun s s' hy h0 h1 hx => ?_, more⟩
  · obtain ⟨g, -, -, -⟩ := hK s s' hy h0 h1
    rw [hO, VerifiableInference.Desc.First.rowsHeld_step N _ _ hq,
      VerifiableInference.Desc.First.rowsHeld_of_groups N _ s s' g]
    exact (xk_parts hx).2.1
  · obtain ⟨g, pl, -, -⟩ := hK s s' hy h0 h1
    rw [hO, VerifiableInference.Desc.First.membersHeld_step N _ _ hq,
      VerifiableInference.Desc.First.membersHeld_of_groups N _ s s' g pl]
    exact (xk_parts hx).2.2.1
  · obtain ⟨-, pl, tr, orc⟩ := hK s s' hy h0 h1
    have hb := (xk_parts hx).2.2.2.1
    unfold bookAt at hb ⊢
    rw [tr, pl, orc, hT, hM]
    exact hb

/-! ## 4 A block that hands the record back; the front -/

/-- A block whose yes hands the record back is asked only what the table says of its two borders. -/
theorem hands_same {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool} {ft k : Nat}
    {b : Block S Cl} (hs : ∀ s s', Yes ft b s s' → s' = s)
    (hT : ∀ s, s.failed = none → XK N links ps E k s = true → XK N links ps E (k + 1) s = true) :
    Hands N links ps E ft k b := by
  refine ⟨fun s s' hy h => ?_, fun s s' hy h0 _ hx => ?_, fun s s' hy h0 _ hx => ?_,
    fun s s' hy h0 _ hx => ?_, fun s s' hy h0 _ hx => ?_, fun s s' hy h0 _ hx => ?_⟩
  · rw [hs s s' hy]; exact h
  · rw [hs s s' hy]; exact (xk_parts (hT s h0 hx)).1
  · rw [hs s s' hy]; exact (xk_parts (hT s h0 hx)).2.1
  · rw [hs s s' hy]; exact (xk_parts (hT s h0 hx)).2.2.1
  · rw [hs s s' hy]; exact (xk_parts (hT s h0 hx)).2.2.2.1
  · rw [hs s s' hy]; exact (xk_parts (hT s h0 hx)).2.2.2.2

end IM

#print axioms IM.s1_of_hands
#print axioms IM.Hands.under
#print axioms IM.hands_quiet
#print axioms IM.hands_same
