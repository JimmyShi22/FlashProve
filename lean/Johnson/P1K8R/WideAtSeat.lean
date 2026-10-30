-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WideAtSeat.lean: THE SMALLNESS TEST AT ITS SEAT IN onlineDescription's
FIRST CHAIN: FROM THE DRAW OF THE MATRIX TO THE LINK'S BATCHING NO BLOCK TURNS WHAT THE LAW'S
LETTERS READ OFF THE SMALLNESS TEST'S RECORD. A LAW ABOUT ProofFile's DESCRIPTION, NO PART OF IT. NO
SOUNDNESS.

The count of the round of the draw binds, outside the drawn matrix, the weights, the sizes and the
cut of the messages. The run that spends them, "K8.equations", is called at the link's batching,
some blocks behind the draw. `wide` (Johnson/Desc/First/K8/LawWide.lean) is the reading of the
carried record that holds all of these.
  `stretches`: WRITTEN: for each of the 25 places (l, i) the number n of entries of the flat list
    between the draw's entry and the batching's: 2; at the head's link 3.
  `leaves_of_under`: a block under a block that leaves a reading leaves it.
  `digits_leave`: K1's sending of the digits at its seat: by `k1_later`
    and `laterAt_tl` (Johnson/Desc/K1/Law/TlAtRecord.lean).
  `lookup_leaves`: the lookup on the digits at its seat: by `k3_of` and
    `theStated_leaves_wide` (Johnson/Desc/First/K8/LawWideK3.lean).
  `merge_leaves`: at the head's link the merge at its seat: by `k11_of` and
    `decide_leaves_tl` (Johnson/Top/H0/MergeLaw/LeavesTl.lean).
  `StaysAt c l i n`: the draw's entry leaves `wide`; the n entries behind it each leave EVERY
    reading of the smallness test's record that reads none of the four fields that the lookup on the
    digits lays: so also `wideM`: `wide` WITH THE DRAWN MATRIX.
  `staysAt_open`: at all 25 places.
  `batch_behind`: THE STRETCH ENDS AT THE BATCHING: the entry right behind it, 14 l + i + 3 + n, is
    the link's batching's block, handed the link's runs of claims in the link's order: by
    `k9_of`.
  `k08_wide_to_batch`: **in scope, from onlineDescription's value: at each (l, i, n) of the written list:
    wherever the fold over the draw's entry and the n entries behind it goes on, from ANY record,
    `wide` of the record that it hands on is `wide` of the record in front; and wherever the fold
    over the n entries BEHIND the draw's goes on, `wideM` stays: THE MATRIX THAT REACHES THE
    BATCHING IS THE ONE THAT WAS DRAWN.**
Limits. THE BLOCKS ALONE: the record that the fold hands on is the one that the batching's entry is
handed. Between that and the record at which the run "K8.equations" is called stand the runs of
claims ahead of it in the link's order: other files' to show. That onlineDescription returns in scope is
a premise.

-/
import Johnson.P1K8R.OrderAtSeat
import Johnson.IMR.K3Seat
import Johnson.IMR.K11Seat
import Johnson.IMR.LinkSeat
import Johnson.Desc.First.K8.LawWideK3
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Top.H0.MergeLaw.LeavesTl

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks claimsInBy)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

/-- For each place: the number of entries between the draw's and the batching's. -/
def stretches : List (ℕ × ℕ × ℕ) :=
  (List.range 25).map fun l => (l, if l = 24 then 5 else 4, if l = 24 then 3 else 2)

/-- A block under a block that leaves a reading leaves it. -/
theorem leaves_of_under {Cl' Cl'' α : Type} {c : Block S Cl'} {b : Block S Cl''} (u : c.Under b)
    {f : S → α} (h : b.Leaves f) : c.Leaves f :=
  fun s rs gs s' H => h s rs gs s' (u s rs gs s' H)

/-- An entry of a stretch of a list. -/
theorem mem_stretch {α : Type} {l : List α} {k m : ℕ} {b : α} (h : b ∈ (l.drop k).take m) :
    ∃ j, j < m ∧ l[k + j]? = some b := by
  obtain ⟨j, hj, e⟩ := List.mem_take_iff_getElem.1 h
  refine ⟨j, by omega, ?_⟩
  rw [← List.getElem?_drop]
  exact List.getElem?_eq_some_iff.2 ⟨by omega, e⟩

/-- The draw's entry leaves `wide`; the n entries behind it each leave every reading of the
smallness test's record that reads none of the four fields that the lookup on the digits lays. -/
def StaysAt (c : Chain S Cl) (l i n : ℕ) : Prop :=
  (∀ b, c.blocksInOrder[14 * l + i + 2]? = some b → b.Leaves wide) ∧
  ∀ j, j < n → ∀ b, c.blocksInOrder[14 * l + i + 3 + j]? = some b →
    ∀ (α : Type) (g : HTailF2 → α), Keeps4 g → b.Leaves (readTl g)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- K1's sending of the digits, at its seat. -/
theorem digits_leave (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl24 : l ≤ 24)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1) (hi : i = 5 ∨ i = 6) :
    ∃ b, c.blocksInOrder[14 * l + i + 2]? = some b ∧ b.Leaves S.tl? := by
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, _, hn, harm⟩ :=
    IM.k1_later O l sub hl i hk (by omega)
  have hf : c.blocksInOrder[14 * l + i + 2]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O hl24 i] at this
    exact this
  rcases harm with ⟨e, _⟩ | ⟨_, h⟩
  · exfalso
    rcases IM.numbers_pieces hn with ⟨h', -⟩ | ⟨h', -⟩ <;> omega
  · exact ⟨b, hf, leaves_of_under (alone_retype_under h)
      fun s rs gs s' H => (VerifiableInference.Desc.K1.laterAt_tl _ _ _ _ _ _ s s' rs gs H).1⟩

/-- The lookup on the digits, at its seat. -/
theorem lookup_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ b, c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b ∧
      ∀ (α : Type) (g : HTailF2 → α), Keeps4 g → b.Leaves (readTl g) := by
  obtain ⟨Lk, b, b', e1, e2, hb', h⟩ := IM.k3_of hS hR O l hl true
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l true)] at hf
  exact ⟨b, hf, fun _ _ hg => leaves_of_under (IM.alone_underR h).2 (theStated_leaves_tl hg hb')⟩

/-- The merge, at its seat in the head's link. -/
theorem merge_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[14 * 24 + 8 + 2]? = some b ∧ b.Leaves S.tl? := by
  obtain ⟨Lk, b, e1, e2, h, _⟩ := IM.k11_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 8] at hf
  exact ⟨b, hf, leaves_of_under (IM.alone_underR h).2 fun s rs gs s' H =>
    VerifiableInference.Desc.First.MergeLaw.decide_leaves_tl (K11.parOf Z Bs.G₀) H⟩

/-- The draw's own entry. -/
theorem draw_leaves {l i : ℕ} (h : SitsAt Z Bs.G₀ c l i) :
    ∃ b, c.blocksInOrder[14 * l + i + 2]? = some b ∧ b.Leaves wide := by
  obtain ⟨_, b, Xl, _, _, hf, _, _, hs, _⟩ := h
  exact ⟨b, hf, leaves_of_under hs.under (hear_leaves_wide _)⟩

/-- A block that leaves the smallness test's record whole leaves every reading of it. -/
theorem leaves_read_of_tl {Cl' α : Type} {b : Block S Cl'} (h : b.Leaves S.tl?) (g : HTailF2 → α) :
    b.Leaves (readTl g) := fun s rs gs s' H => congrArg (Option.map g) (h s rs gs s' H)

/-- **At all 25 places.** -/
theorem staysAt_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ stretches, StaysAt c x.1 x.2.1 x.2.2 := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  have hp : (l, if l = 24 then 5 else 4) ∈ places := List.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨b0, f0, w0⟩ := draw_leaves (sitsAt_open hS hR O _ hp)
  obtain ⟨b2, f2, w2⟩ := lookup_leaves hS hR O hl'
  have same : ∀ {k : ℕ} {a b : Block S Cl}, c.blocksInOrder[k]? = some a → c.blocksInOrder[k]? = some b → a = b :=
    fun e e' => Option.some.inj (e.symm.trans e')
  refine ⟨fun b hb => same f0 hb ▸ w0, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨b1, f1, w1⟩ := digits_leave hS hR O (by omega) .head
      (IM.subs_head hS hR O.pub O.blank) 6 (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
    obtain ⟨b3, f3, w3⟩ := merge_leaves hS hR O
    intro j hj b hb α g hg
    simp only [if_true] at hj hb
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · exact same f1 hb ▸ leaves_read_of_tl w1 g
    · exact same f2 hb ▸ w2 α g hg
    · exact same f3 hb ▸ leaves_read_of_tl w3 g
  · have hd : ∃ b, c.blocksInOrder[14 * l + 5 + 2]? = some b ∧ b.Leaves S.tl? := by
      by_cases he : l % 2 = 0
      · have h := IM.subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
        rw [show 2 * (l / 2) = l by omega] at h
        exact digits_leave hS hR O (by omega) .layers h 5
          (by unfold kindsBeforeBatching; cases (l == 0) <;> rfl) (Or.inl rfl)
      · have h := IM.subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
        rw [show 2 * (l / 2) + 1 = l by omega] at h
        exact digits_leave hS hR O (by omega) .attention h 5
          (by unfold kindsBeforeBatching; cases (l == 0) <;> rfl) (Or.inl rfl)
    obtain ⟨b1, f1, w1⟩ := hd
    intro j hj b hb α g hg
    simp only [h24, if_false] at hj hb
    have e6 : IM.k3Ix l true = 6 := by simp [IM.k3Ix, h24]
    rw [e6] at f2
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact same f1 hb ▸ leaves_read_of_tl w1 g
    · exact same f2 hb ▸ w2 α g hg

/-- **The stretch ends at the batching**: the entry right behind it is the link's batching's block,
handed the link's runs of claims in the link's order. -/
theorem batch_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ stretches, ∃ Lk, c.links[x.1]? = some Lk ∧
      c.blocksInOrder[14 * x.1 + x.2.1 + 3 + x.2.2]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  obtain ⟨Lk, _, _, _, e1, _, _, _, _, _, _, hf, _, _, _, _, _, hn, _⟩ := (IM.k9_of hS hR O).2 l hl'
  refine ⟨Lk, e1, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    have e9 : Lk.hear.length = 9 := hn
    rw [e9] at hf
    exact hf
  · have e7 : Lk.hear.length = 7 := by
      rw [hn]
      unfold IM.subAt
      simp only [h24, if_false]
      split <;> (unfold kindsBeforeBatching; cases (l == 0) <;> rfl)
    rw [e7] at hf
    simp only [h24, if_false]
    rw [show 14 * l + 4 + 3 + 2 = 14 * l + 7 + 2 by omega]
    exact hf

end

/-- **FROM THE DRAW TO THE BATCHING NO BLOCK TURNS WHAT THE LAW'S LETTERS READ.** -/
theorem k08_wide_to_batch {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ x ∈ stretches,
        (∃ Lk, c.links[x.1]? = some Lk ∧ c.blocksInOrder[14 * x.1 + x.2.1 + 3 + x.2.2]? =
          some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))) ∧
        ∀ (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
          (out : S × List Fmt.RoundView × List OpenedColumn),
          (foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 2)).take (x.2.2 + 1)) s rs cols =
            .ok out → wide out.1 = wide s) ∧
          (foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 3)).take x.2.2) s rs cols =
            .ok out → wideM out.1 = wideM s) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Z, Bs.G₀, c, A, B, O.pub, O.blank, O.desc, fun x hx =>
    ⟨batch_behind hS hR O x hx, fun ft s rs cols out => ⟨fun H => ?_, fun H => ?_⟩⟩⟩
  · refine foldLeavesWide ft _ s rs cols out (fun b hb => ?_) H
    obtain ⟨j, hj, e⟩ := mem_stretch hb
    cases j with
    | zero => exact (staysAt_open hS hR O x hx).1 b e
    | succ j =>
      exact (staysAt_open hS hR O x hx).2 j (by omega) b
        (by rw [show 14 * x.1 + x.2.1 + 3 + j = 14 * x.1 + x.2.1 + 2 + (j + 1) by omega]; exact e)
        _ wideOf keeps4_wideOf
  · refine VerifiableInference.Desc.foldLeaves S Cl _ wideM ft _ s rs cols out (fun b hb => ?_) H
    obtain ⟨j, hj, e⟩ := mem_stretch hb
    exact (staysAt_open hS hR O x hx).2 j hj b e _ wideMOf fun _ _ _ _ _ => rfl

end P1K8S

#print axioms P1K8S.digits_leave
#print axioms P1K8S.lookup_leaves
#print axioms P1K8S.merge_leaves
#print axioms P1K8S.staysAt_open
#print axioms P1K8S.batch_behind
#print axioms P1K8S.k08_wide_to_batch
