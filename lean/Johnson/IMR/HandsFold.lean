-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HandsFold.lean: A LIGHT FILE (it imports Johnson/IMR/HandsDef.lean and
Johnson/Desc/K15/FoldInv.lean alone): THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT
READS THE VERIFIER's STATE ALONE: FROM «EACH SUB-PROTOCOL HANDS X ON» TO «X HOLDS AT EVERY
STATE THAT THE FOLD REACHES WITHOUT A MARK»: THE KIND-FREE LEMMA («Rch (k + 1) b ⟹ the four Bools at border k + 1: then no [kind]'s second tie shows them»).
ON WORDS: «the state» is the verifier's state: the value of type S that the fold carries from sub-protocol (block) to sub-protocol.
OBJECT. foldBlocks ft (bs.take k) s₀ rs cols = .ok out (Johnson/Desc/Block.lean): the form of rchAt_fold's | reach_fold's conclusion (Johnson/Top/H0/Walk/ReachAt.lean · Reach.lean: at ft := 0, s₀ := F.start₁ z, bs := F.first.blocksInOrder). USER. «reached» · every kind's second tie.
CALLED, NOT TYPED: foldBlocks_cons | foldBlocks_nil (Johnson/Desc/K15/FoldInv.lean).

  Hands.step        one sub-protocol: its step's yes between two states without a mark hands X k on to X (k + 1).
  xk_along          a list of sub-protocols, the first at number k₀, each with Hands at its number: where the fold accepts and the state behind bears no mark: the state in front bears none, and X k₀ in front gives X (k₀ + ‹the list's length›) behind.
  x_at_cut          AT A CHAIN: (S1) and «X 0 at the first state, if it bears no mark» give X k at the state behind the first k sub-protocols, wherever the fold over these accepts and leaves no mark. WHATEVER ROUNDS AND COLUMNS ARE LEFT OVER.
  bk_at_cut         … so the table's four fixed tests there: shapeAt · rowsHeld · membersHeld · bookAt.

What is not claimed. (S1) and (S0) are premises: (S1) in the goals' scope from ten shares: Johnson/IMR/GrownJoin.lean's s1_of_shares; no share but that of the files of Johnson/IMR/ is paid there · (S0): Johnson/IMR/GrownStart.lean. No soundness.
-/
import Johnson.IMR.HandsDef
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt rowsHeld membersHeld bookAt)
open ProofFile (Cl)

/-- One sub-protocol hands X on. -/
theorem Hands.step {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft k : Nat} {b : Block S Cl} (H : Hands N links ps E ft k b) {s s' : S} (hy : Yes ft b s s')
    (h0 : s.failed = none) (h1 : s'.failed = none) (hx : XK N links ps E k s = true) :
    XK N links ps E (k + 1) s' = true := by
  unfold XK BK
  rw [H.shape s s' hy h0 h1 hx, H.rows s s' hy h0 h1 hx, H.members s s' hy h0 h1 hx,
    H.book s s' hy h0 h1 hx, H.more s s' hy h0 h1 hx]
  rfl

/-- **Along a list of sub-protocols.** -/
theorem xk_along {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} : ∀ (bs : List (Block S Cl)) (k₀ : Nat),
    (∀ j b, bs[j]? = some b → Hands N links ps E ft (k₀ + j) b) →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok out → out.1.failed = none →
      s.failed = none ∧
        (XK N links ps E k₀ s = true → XK N links ps E (k₀ + bs.length) out.1 = true)
  | [], k₀, _, s, rs, cols, out, h, hu => by
    obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s rs cols out h
    exact ⟨hu, fun hx => hx⟩
  | b :: l, k₀, hH, s, rs, cols, out, h, hu => by
    obtain ⟨s', n, -, hs, hl⟩ := VerifiableInference.Desc.foldBlocks_cons ft b l s rs cols out h
    have hHl : ∀ j b', l[j]? = some b' → Hands N links ps E ft (k₀ + 1 + j) b' := by
      intro j b' hj
      have := hH (j + 1) b' (by simpa using hj)
      rwa [show k₀ + (j + 1) = k₀ + 1 + j by omega] at this
    obtain ⟨hu', hx'⟩ := xk_along l (k₀ + 1) hHl s' _ _ out hl hu
    have Hb : Hands N links ps E ft k₀ b := hH 0 b rfl
    have hy : Yes ft b s s' := ⟨_, _, _, hs⟩
    have h0 : s.failed = none := Classical.byContradiction fun hm => Hb.mark s s' hy hm hu'
    refine ⟨h0, fun hx => ?_⟩
    have := hx' (Hb.step hy h0 hu' hx)
    rwa [show k₀ + 1 + l.length = k₀ + (b :: l).length by simp; omega] at this

/-- (S1) at a chain is Hands at every sub-protocol of its flat list. -/
theorem hands_of_s1 {N : Numbers} {links : List ModelPart} {E : Nat → S → Bool} {ft : Nat}
    {c : Chain S Cl} (h : S1 N links E ft c) :
    ∀ k b, c.blocksInOrder[k]? = some b → Hands N links (c.blocksInOrder.map (·.place)) E ft k b := by
  intro k b hb
  refine ⟨fun s s' hy => (h k b hb s s' hy).1, fun s s' hy h0 h1 hx => ?_,
    fun s s' hy h0 h1 hx => ?_, fun s s' hy h0 h1 hx => ?_, fun s s' hy h0 h1 hx => ?_,
    fun s s' hy h0 h1 hx => ?_⟩
  · exact (xk_parts ((h k b hb s s' hy).2 h0 h1 hx)).1
  · exact (xk_parts ((h k b hb s s' hy).2 h0 h1 hx)).2.1
  · exact (xk_parts ((h k b hb s s' hy).2 h0 h1 hx)).2.2.1
  · exact (xk_parts ((h k b hb s s' hy).2 h0 h1 hx)).2.2.2.1
  · exact (xk_parts ((h k b hb s s' hy).2 h0 h1 hx)).2.2.2.2

/-- **Under premises h1 (S1: ALL states), h0: X at each state the fold reaches without a mark.** -/
theorem x_at_cut {N : Numbers} {links : List ModelPart} {E : Nat → S → Bool} {ft : Nat} {c : Chain S Cl}
    (h1 : S1 N links E ft c) {s₀ : S}
    (h0 : s₀.failed = none → XK N links (c.blocksInOrder.map (·.place)) E 0 s₀ = true)
    {k : Nat} (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn} (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out)
    (hu : out.1.failed = none) : XK N links (c.blocksInOrder.map (·.place)) E k out.1 = true := by
  have hH : ∀ j b, (c.blocksInOrder.take k)[j]? = some b →
      Hands N links (c.blocksInOrder.map (·.place)) E ft (0 + j) b := by
    intro j b hj
    rw [Nat.zero_add]
    refine hands_of_s1 h1 j b ?_
    rw [List.getElem?_take] at hj
    split at hj
    · exact hj
    · cases hj
  obtain ⟨hs, hx⟩ := xk_along (c.blocksInOrder.take k) 0 hH s₀ rs cols out hf hu
  have := hx (h0 hs)
  rwa [Nat.zero_add, List.length_take, Nat.min_eq_left hk] at this

/-- … so the table's four fixed tests there. -/
theorem bk_at_cut {N : Numbers} {links : List ModelPart} {E : Nat → S → Bool} {ft : Nat} {c : Chain S Cl}
    (h1 : S1 N links E ft c) {s₀ : S}
    (h0 : s₀.failed = none → XK N links (c.blocksInOrder.map (·.place)) E 0 s₀ = true)
    {k : Nat} (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn} (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out)
    (hu : out.1.failed = none) :
    shapeAt links (c.blocksInOrder.map (·.place))[k]? out.1 = true ∧
      rowsHeld N (openAt links (c.blocksInOrder.map (·.place)) k) out.1 = true ∧
      membersHeld N (openAt links (c.blocksInOrder.map (·.place)) k) out.1 = true ∧
      bookAt N (c.blocksInOrder.map (·.place))[k]? out.1 = true := by
  obtain ⟨a, b, c', d, -⟩ := xk_parts (x_at_cut h1 h0 hk hf hu)
  exact ⟨a, b, c', d⟩

end IM

#print axioms IM.Hands.step
#print axioms IM.xk_along
#print axioms IM.hands_of_s1
#print axioms IM.x_at_cut
#print axioms IM.bk_at_cut
