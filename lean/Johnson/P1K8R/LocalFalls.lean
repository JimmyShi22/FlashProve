-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LocalFalls.lean: THE SMALLNESS TEST: WHICH FALLS THE MEMBERS FROM THE DRAW's ON, AND
FROM THE BATCHING's ON, CAN MEET WITH ONE ROUND's CHALLENGE AT HAND. LEMMAS; NONE OF THE LIBRARY's
GOALS. No run, no prover, no measure. Nothing on completeness, soundness or hiding.

`frontsOf` (Johnson/Desc/ProofFile/Honest/Fall.lean) lists a member only if its rounds are at hand.
So with one round it lists the member that takes it, then the members without a round behind it, and
stops in front of the next member with a round. fs: A LETTER: a list of falls, whoever has written
them. No premise is laid on it: the fall that speaks is named. l < 25. Kd := 14 l + 6, or 343 at the
head's: the member that hears the draw. K := 14 l + 9, or 347: the batching's.
  `two_rounds`   general: two members with a round each among the first i + 1 make at least two
      rounds
  `draw_member`   in the goals' scope there is a member at Kd, and it declares one round
  **`local_draw`**   where the members from Kd on meet a fall of fs, from whatever state, at rounds
      with the one challenge dr: a fall of fs is seated at the member at Kd or at a member directly
      behind it up to which no second round is asked, in front of K
  `local_draw_none`   so the event is empty IF no fall of fs is seated at such a member
  **`local_batch`**   where the members from K on meet a fall of fs from the state s', at rounds
      with the one challenge dr: (a) a fall of fs at the batching's place speaks at s' and [dr]; or
      (b) the batching block's own step says yes from s' at a round that has drawn dr, and a fall of
      fs at the place of the member without a round behind it speaks at the state that the step
      returns AND AT SOME LIST OF CHALLENGES, WHICH THE STATEMENT TIES TO NOTHING (so where a fall's
      test reads its challenges, (b) says less than "it speaks there"); the round's other fields and
      the columns are tied through that return alone; or (c) a fall of fs is seated at a member
      further behind, up to which no second round is asked, in front of the next segment's draw: (c)
      reads fs and the chain alone
By: `chainFall_at` (Johnson/P1K8R/FallByPlace.lean) · `frontsOf_rounds`, `frontsOf_place`,
`frontsOf_first`, `fallOf_mem` (Johnson/Desc/ProofFile/Honest/K8/FrontsRounds.lean) ·
`frontsOf_step` · `batch_round` (Johnson/P1K8R/FallAtRun.lean) · `batch_there`, `quiet_there`
(PlacesAtFlat.lean) · P1K8S.sitsAt_open (OrderAtSeat.lean), IM.alone_rounds
(Johnson/IMR/SeatForm.lean).
Limits. Which members behind the two have no round is not shown: by the docstring of closeKinds
(Johnson/Desc/First/Driver/Chain.lean) the member at K + 2 has none. No count and no measure is in
this file.
-/
import Johnson.P1K8R.FallByPlace
import Johnson.P1K8R.LiveAtRun
import Johnson.Desc.ProofFile.Honest.K8.FrontsRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open ProofFile.Honest (frontsOf chainFall fallOf Fall)
open ProofFile.Honest.K8 (rnds rnds_take_succ rnds_take_mono batchPlace quietPlace frontsOf_rounds
  frontsOf_place frontsOf_first frontsOf_step frontsOf_zero fallOf_mem)

/-- Two members with a round each. -/
theorem two_rounds {T Cl : Type} (L : List (Block T Cl)) {x y : Block T Cl} {g i : ℕ}
    (h0 : L[0]? = some x) (hg : L[g]? = some y) (hpos : 0 < g) (hx : x.rounds.length = 1)
    (hy : y.rounds.length = 1) (hi : g ≤ i) : 2 ≤ rnds (L.take (i + 1)) := by
  have a1 : rnds (L.take (0 + 1)) = rnds (L.take 0) + x.rounds.length := rnds_take_succ h0
  have a2 : rnds (L.take (g + 1)) = rnds (L.take g) + y.rounds.length := rnds_take_succ hg
  have a3 : rnds (L.take (0 + 1)) ≤ rnds (L.take g) := rnds_take_mono L hpos
  have a4 : rnds (L.take (g + 1)) ≤ rnds (L.take (i + 1)) := rnds_take_mono L (by omega)
  omega

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The member that hears the draw declares one round. -/
theorem draw_member (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ b8 : Block S Claim, c.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]? = some b8 ∧
      b8.rounds.length = 1 := by
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨Lk, b8, Xl, _, _, hf8, _, hL, _, _, _⟩ := P1K8S.sitsAt_open hS hR O _ hp
  refine ⟨b8, hf8, ?_⟩
  rw [IM.alone_rounds hL]
  rfl

/-- **From the draw's member on, with its one challenge.** -/
theorem local_draw (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (fs : List (Fall S)) (s' : S) (dr : Fmt.Drawn)
    (h : ∃ (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn), rs.map (·.drawn) = [dr] ∧
      (chainFall fs 0 (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2)) s'
        ⟨rs, cols⟩).isSome = true) :
    ∃ f ∈ fs, ∃ i,
      rnds ((c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2)).take (i + 1)) ≤ 1 ∧
      14 * l + (if l = 24 then 5 else 4) + 2 + i < 14 * l + (if l = 24 then 11 else 9) ∧
      (c.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2 + i]?).map (·.place) = some f.place := by
  obtain ⟨rs, cols, hrs, hc⟩ := h
  obtain ⟨⟨a, w⟩, hcw⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨i, e, hi, hpl, hfall⟩ := chainFall_at fs 0 _ s' _ a w hcw
  have hlen : rs.length = 1 := by
    have := congrArg List.length hrs
    simpa using this
  have hr : rnds ((c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2)).take (i + 1)) ≤
      rs.length := frontsOf_rounds 0 _ _ _ _ i e hi
  rw [hlen] at hr
  have hplace := frontsOf_place 0 _ _ _ _ i e hi
  rw [List.getElem?_drop] at hplace
  obtain ⟨f, hf, hfp, -⟩ := fallOf_mem fs a _ _ w hfall
  refine ⟨f, hf, i, hr, ?_, by rw [hplace, hpl, hfp]⟩
  by_contra hlt
  obtain ⟨b8, hb8, h8⟩ := draw_member hS hR O hl
  obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 (batch_there hS hR O hl)
  have hb1 := batch_round hS hR O hl b hb
  have e0 : (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2))[0]? = some b8 := by
    rw [List.getElem?_drop]
    exact hb8
  have eg : (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2))[
               (if l = 24 then 4 else 3)]? = some b := by
    rw [List.getElem?_drop, ← hb]
    congr 1
    split_ifs <;> omega
  have h2 := two_rounds _ e0 eg (by split_ifs <;> omega) h8 hb1 (i := i) (by
    split_ifs at hlt ⊢ <;> omega)
  omega

/-- The event is empty where no fall is seated at such a member. -/
theorem local_draw_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (fs : List (Fall S))
    (hfs : ∀ f ∈ fs, ∀ i,
      rnds ((c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2)).take (i + 1)) ≤ 1 →
      (c.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2 + i]?).map (·.place) ≠ some f.place)
    (s' : S) (dr : Fmt.Drawn) :
    ¬ ∃ (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn), rs.map (·.drawn) = [dr] ∧
      (chainFall fs 0 (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 2)) s'
        ⟨rs, cols⟩).isSome = true := by
  intro h
  obtain ⟨f, hf, i, h1, -, h3⟩ := local_draw hS hR O hl fs s' dr h
  exact hfs f hf i h1 h3

/-- **From the batching's member on, with its one challenge.** -/
theorem local_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    (fs : List (Fall S)) (s' : S) (dr : Fmt.Drawn)
    (h : ∃ (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn), rs.map (·.drawn) = [dr] ∧
      (chainFall fs 0 (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9))) s'
        ⟨rs, cols⟩).isSome = true) :
    (∃ f ∈ fs, f.place = batchPlace l (if l = 24 then 1 else 0) ∧
        (f.test s' [dr]).isSome = true) ∨
      (∃ f ∈ fs, f.place = quietPlace l (if l = 24 then 1 else 0) ∧
        ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : ℕ) (ds : List Fmt.Drawn),
          r.drawn = dr ∧ b.step 0 s' [r] cols = .ok (t, m) ∧ (f.test t ds).isSome = true) ∨
      ∃ f ∈ fs, ∃ i, 2 ≤ i ∧
        rnds ((c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9))).take (i + 1)) ≤ 1 ∧
        (l < 24 → 14 * l + (if l = 24 then 11 else 9) + i <
          14 * (l + 1) + (if l + 1 = 24 then 5 else 4) + 2) ∧
        (c.blocksInOrder[14 * l + (if l = 24 then 11 else 9) + i]?).map (·.place) = some f.place := by
  obtain ⟨rs, cols, hrs, hc⟩ := h
  obtain ⟨⟨a, w⟩, hcw⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨i, e, hi, hpl, hfall⟩ := chainFall_at fs 0 _ s' _ a w hcw
  obtain ⟨r, rfl, hrd⟩ : ∃ r, rs = [r] ∧ r.drawn = dr := by
    cases rs with
    | nil => simp at hrs
    | cons r t =>
      cases t with
      | nil => exact ⟨r, rfl, by simpa using hrs⟩
      | cons _ _ => simp at hrs
  have hb1 := batch_round hS hR O hl b hb
  have hplace := frontsOf_place 0 _ _ _ _ i e hi
  rw [List.getElem?_drop] at hplace
  obtain ⟨f, hf, hfp, hft⟩ := fallOf_mem fs a _ _ w hfall
  have e0 : (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)))[0]? = some b := by
    rw [List.getElem?_drop]
    exact hb
  match i, hi, hplace with
  | 0, hi, hplace =>
    left
    obtain ⟨hK, hbe⟩ := List.getElem?_eq_some_iff.1 hb
    have hd : c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) =
        b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1) := by
      rw [List.drop_eq_getElem_cons hK, hbe]
    have hi' : (frontsOf 0 (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9))) s' [r] cols)[0]? =
        some e := hi
    rw [hd] at hi'
    have he := frontsOf_first 0 b _ s' [r] cols e hi'
    rw [hb1] at he
    have hbp := batch_there hS hR O hl
    rw [Nat.add_zero, hbp] at hplace
    have ha : a = batchPlace l (if l = 24 then 1 else 0) :=
      hpl.symm.trans (Option.some.inj hplace).symm
    rw [he] at hft
    have hft' : f.test s' [r.drawn] = some w := hft
    refine ⟨f, hf, hfp.trans ha, ?_⟩
    rw [← hrd, hft']
    rfl
  | 1, hi, hplace =>
    right
    left
    obtain ⟨e₀, b₀, cols', m, g1, g2, -, g4⟩ := frontsOf_step 0 _ _ _ _ 0 e hi
    obtain rfl : b = b₀ := Option.some.inj (e0.symm.trans g2)
    have hs0 := frontsOf_zero 0 _ _ _ _ e₀ g1
    rw [hs0, hb1] at g4
    have g4' : b.step 0 s' [r] cols' = .ok (e.2.1, m) := g4
    have hq := quiet_there hS hR O hl
    rw [hq] at hplace
    have ha : a = quietPlace l (if l = 24 then 1 else 0) :=
      hpl.symm.trans (Option.some.inj hplace).symm
    refine ⟨f, hf, hfp.trans ha, r, cols', e.2.1, m, e.2.2, hrd, g4', ?_⟩
    rw [hft]
    rfl
  | i + 2, hi, hplace =>
    right
    right
    have hr : rnds ((c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9))).take (i + 2 + 1)) ≤ 1 :=
      frontsOf_rounds 0 _ _ _ _ (i + 2) e hi
    refine ⟨f, hf, i + 2, by omega, hr, fun h24 => ?_, by rw [hplace, hpl, hfp]⟩
    by_contra hge
    obtain ⟨b8, hb8, h8⟩ := draw_member hS hR O (l := l + 1) (by omega)
    have eg : (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)))[
                 (if l + 1 = 24 then 12 else 11)]? = some b8 := by
      rw [List.getElem?_drop, ← hb8]
      congr 1
      split_ifs <;> omega
    have h2 := two_rounds _ e0 eg (by split_ifs <;> omega) hb1 h8 (i := i + 2) (by
      split_ifs at hge ⊢ <;> omega)
    omega

end

end P1K8

#print axioms P1K8.two_rounds
#print axioms P1K8.draw_member
#print axioms P1K8.local_draw
#print axioms P1K8.local_draw_none
#print axioms P1K8.local_batch
