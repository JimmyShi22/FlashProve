-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Pull.lean: what is spent of the row claim_read_same_index (Reads/Stated.lean) on
the side of the forms, where a link's ledger is pulled back from the entries of the vector of reads
to the cells.

All of this file is a tool: it holds for all sizes, letters and values, and names no description of
the protocol.

Why. `spent` (Reads/Stated.lean) stands in front of the smallness test's round: it has that round's
relation in its hands. The end of a link's chain has not. It has the ledger with each entry of the
vector of reads replaced by a public form in the cells: `affRead` (Cb/Pv/Tail/Agree.lean) at the
read that `itU` (Cb/Pv/Tail/Places.lean) finds at the entry's place. What that end wants of the row
is said here: the form that stands for the entry at a use's place is the use's own sum of cells.

What is here.
  `atCell v`: values of the cells at plain numbers, 0 outside the sizes.
  `Meant.sumAt e w`: the sum of e's cells under e's weights, where w stands at the cells.
  `affRead_val`: the value of a read's form is the read's weights on the cells of its column.
  `pull_of_same`: where no place is named twice (`Apart`, Cb/Pv/Tail/PlacesOne.lean), at every e
    with `SameIndex`, the form of the read that `itU` finds at e's place has, at all values v of the
    cells, the value of e's sum of cells.
  `pulled`: the vector of reads with each named place below N replaced by that form's value.
  `pulled_of_same`: the same in its words.
  `pull_of_row`: what is spent. From the row, at a link and a state with closed tables, for all
    values of the cells: at every use's place the pulled vector has the use's sum of cells; and for
    every form of the link, its part in U3 at the pulled vector is the sum of what the uses of that
    form mean, each times the clause's coefficient.

Premises of `pull_of_row` that the row does not give: `Apart` at the row's sizes; every use's place
lies below N; the letters' weights are the list's.

Limits. It does not say that a link's frame writes its late entries with `itU` at these sizes. The
premise on virtual rows stands (Reads/Stated.lean, limits). Nothing is said of a ledger. `pulled` is
found by choice, as `itU` is. Nothing on soundness.


-/
import Johnson.Desc.Reads.Stated
import Cb.Pv.Tail.Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail

variable {K : Type} [Field K] {t : TSize}

/-- Values of the cells at plain numbers (matrix, column, row): 0 outside the sizes. -/
def atCell (v : JCell t.size → K) (μ c i : ℕ) : K :=
  if hμ : μ < t.NM then
    if hc : c < t.k μ then
      if hi : i < t.m μ then v ⟨⟨μ, hμ⟩, ⟨c, hc⟩, ⟨i, hi⟩⟩ else 0
    else 0
  else 0

theorem atCell_in (v : JCell t.size → K) {μ c i : ℕ} (hμ : μ < t.NM) (hc : c < t.k μ)
    (hi : i < t.m μ) : atCell v μ c i = v ⟨⟨μ, hμ⟩, ⟨c, hc⟩, ⟨i, hi⟩⟩ := by
  unfold atCell
  rw [dif_pos hμ, dif_pos hc, dif_pos hi]

/-- The sum of the cells of e under e's weights, where w stands at the cells. -/
def Meant.sumAt (e : Meant K) (w : ℕ → ℕ → ℕ → K) : K :=
  ∑ j ∈ Finset.range e.len, e.w j * w (e.cell j).1 (e.cell j).2.1 (e.cell j).2.2

/-- The value of a read's form: the read's weights on the cells of its column. -/
theorem affRead_val {s : Size} (Λ : Cb.Pv.Tail.Letters K s) (x : Λ.X) (μ : Fin s.NM)
    (r : Fin (s.nr μ)) (c : Fin (s.k μ)) (v : JCell s → K) :
    (affRead Λ x ⟨μ, r, c⟩).val v = ∑ i, Λ.w x μ r i * v ⟨μ, c, i⟩ := by
  have e1 := sum_formOf v ((List.finRange (s.m μ)).map fun i =>
    ((⟨μ, c, i⟩ : JCell s), Λ.w x μ r i))
  have e2 : (((List.finRange (s.m μ)).map fun i => ((⟨μ, c, i⟩ : JCell s), Λ.w x μ r i)).map
      fun z => z.2 * v z.1).sum = ∑ i, Λ.w x μ r i * v ⟨μ, c, i⟩ := by
    rw [List.map_map]
    exact sum_finRange _
  exact (add_zero _).trans (e1.trans e2)

/-- **The form that stands for the entry at e's place is e's sum of cells.** -/
theorem pull_of_same (Θ : TLetters K t) (x : Θ.X) (ha : Apart t) {N : ℕ} (j : JU t N)
    (e : Meant K) (h : SameIndex t (Θ.phi x) e) (hj : (j.1 : ℕ) = e.pos)
    (v : JCell t.size → K) :
    (affRead Θ.letters x (itU j)).val v = e.sumAt (atCell v) := by
  obtain ⟨n, T, c, sg, g1, g2, g3, g4, g5, g6, g7⟩ := h
  rw [itU_eq ha j g1 g2 g3 g4 (hj.trans g5)]
  have hd := t.dec_enc g1 rfl g4
  have hlen : sg * T.len + T.len ≤ t.m T.mat := by
    have h0 : 0 < T.len := by
      rcases Nat.eq_zero_or_pos T.len with h | h
      · rw [h, Nat.div_zero] at g4
        exact absurd g4 (Nat.not_lt_zero _)
      · exact h
    have h5 := (Nat.le_div_iff_mul_le h0).1 (Nat.succ_le_of_lt g4)
    rw [Nat.succ_mul] at h5
    exact h5
  have eW : ∀ i : ℕ, wOf t (Θ.phi x) T.mat (t.enc T.mat n sg) i =
      if sg * T.len ≤ i ∧ i < sg * T.len + T.len then Θ.phi x n (i - sg * T.len) else 0 := by
    intro i
    unfold wOf
    rw [hd]
  have e1 := sum_stretch (t.m T.mat) (sg * T.len) T.len hlen (Θ.phi x n)
    (fun i => atCell v T.mat c i)
  refine (affRead_val Θ.letters x ⟨T.mat, g2⟩ ⟨t.enc T.mat n sg, t.enc_lt g1 g4⟩ ⟨c, g3⟩ v).trans ?_
  unfold Meant.sumAt
  rw [g6]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (e1.trans (Finset.sum_congr rfl fun q hq => ?_))
  · show wOf t (Θ.phi x) T.mat (t.enc T.mat n sg) i * v ⟨⟨T.mat, g2⟩, ⟨c, g3⟩, i⟩ = _
    rw [eW, atCell_in v g2 g3 i.2]
  · obtain ⟨c1, c2⟩ := g7 q (Finset.mem_range.1 hq)
    rw [c1, c2]

open Classical in
/-- The vector of reads, with each named place below N replaced by the value, at the cells' values
v, of the form of the read that itU finds there; 0 elsewhere. -/
noncomputable def pulled (Θ : TLetters K t) (x : Θ.X) (N : ℕ) (v : JCell t.size → K) (p : ℕ) : K :=
  if h : p < N ∧ Named t p then
    (affRead Θ.letters x (itU (⟨⟨p, h.1⟩, h.2⟩ : JU t N))).val v
  else 0

theorem pulled_of_same (Θ : TLetters K t) (x : Θ.X) (ha : Apart t) (N : ℕ) (e : Meant K)
    (h : SameIndex t (Θ.phi x) e) (hN : e.pos < N) (v : JCell t.size → K) :
    pulled Θ x N v e.pos = e.sumAt (atCell v) := by
  unfold pulled
  rw [dif_pos ⟨hN, named_of_same h⟩]
  exact pull_of_same Θ x ha _ e h rfl v

/-- **What is spent, on the side of the forms.** -/
theorem pull_of_row (L : Letters K) (H : ClaimReadSameIndex L) {l : L.Link} (hl : l ∈ L.links)
    {s : L.State} (hs : L.AtClose l s) (Θ : TLetters K (L.size l s)) (x : Θ.X)
    (hphi : Θ.phi x = L.phi l s) (ha : Apart (L.size l s)) (N : ℕ)
    (hN : ∀ u ∈ L.uses l, L.place l u < N) (v : JCell (L.size l s).size → K) :
    (∀ u ∈ L.uses l, pulled Θ x N v (L.place l u) = (L.meant l s u).sumAt (atCell v)) ∧
      ∀ (n : ℕ) (f : OnBytes.Model.Aff), (L.forms l s)[n]? = some f →
        u3Value L.val (L.iU3 l) (L.cols l) f (pulled Θ x N v) =
          ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sumAt (atCell v)).sum := by
  obtain ⟨-, hA, hT⟩ := H l hl s hs
  have hu : ∀ u ∈ L.uses l, pulled Θ x N v (L.place l u) = (L.meant l s u).sumAt (atCell v) :=
    fun u hu => pulled_of_same Θ x ha N (L.meant l s u) (by rw [hphi]; exact hA u hu) (hN u hu) v
  refine ⟨hu, fun n f hf => ?_⟩
  rw [(hT.2 n f hf).2 (pulled Θ x N v)]
  unfold Letters.clauseValue
  refine congrArg List.sum (List.map_congr_left fun u hu' => ?_)
  show L.coef l s u * pulled Θ x N v (L.place l u) = L.coef l s u * (L.meant l s u).sumAt (atCell v)
  rw [hu u (List.mem_filter.1 hu').1]

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.atCell_in
#print axioms VerifiableInference.Reads.affRead_val
#print axioms VerifiableInference.Reads.pull_of_same
#print axioms VerifiableInference.Reads.pulled_of_same
#print axioms VerifiableInference.Reads.pull_of_row
