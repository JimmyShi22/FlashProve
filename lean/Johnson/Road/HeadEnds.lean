-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadEnds.lean: tools for the claims that three sumchecks of the output head's sub-proof
leave.

The check of the output head's sub-proof runs a sumcheck for each of three sums of products: the
squares of the residual stream, the stream times the reciprocal of the final normalisation, and the
normalised activations times the output matrix. After each, the verifier adds claims
(claimSquares, claimStream, claimLogits in OnBytes/Model/Head.lean) that say what the hidden end
values of the sumcheck are. Johnson/Road/HeadSteps.lean [not in this library] names the forms of
these claims and says what they are worth on cells. This file has the parts of that work which speak
of no claim: how the stream's limbs are read in a long table, and which weights the verifier puts on
the channels.

Main theorems: ok_map (a routine whose value is changed by a function); xb_read (a block of one limb
of the stream in a long table), stream_cells (the stream under a segment's block weights);
stream_sum (the sum that the second sumcheck is about, as one extension); hiTab_ok, squares_weight
(the weight of a channel in the claim on the squares' end value is the equality weight of the
layer's point).

What is not claimed. Nothing on which claims a routine adds or on what a claim is worth. Nothing on
when a world is true, on the points' origin, or on what a verifier's acceptance shows. The program
does not import this file.
-/
import Johnson.Road.HeadLedger

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

/-! ## Tools -/

/-- A routine whose value is changed by a function. -/
theorem ok_map {α β : Type} (f : α → β) (m : SubM α) (F G : Fork) (C D : Ctx) (b : β) :
    Ok (f <$> m) F C b G D ↔ ∃ a, Ok m F C a G D ∧ b = f a := by
  have e : (f <$> m) F C = (m F C).bind fun q => .ok ((f q.1.1, q.1.2), q.2) := rfl
  unfold Ok
  rw [e]
  cases m F C with
  | error y => simp [Except.bind]
  | ok q =>
    obtain ⟨⟨a', G'⟩, D'⟩ := q
    constructor
    · intro h
      cases h
      exact ⟨a', rfl, rfl⟩
    · rintro ⟨a, h1, rfl⟩
      cases h1
      rfl

/-- The name of the table of the matrix hr at the point of the second sumcheck. -/
theorem hr_rtN : "hr@" ++ "rt_N" = "hr@rt_N" := by decide

variable {K : Type} [Field K]

/-- A sum of two terms. -/
theorem sum_two (f : ℕ → K) : ∑ l ∈ range 2, f l = f 0 + f 1 :=
  (Finset.sum_range_succ f 1).trans (by rw [Finset.sum_range_one])

variable {ρ : Reading K} {W : World K}

/-- A block of one limb of the residual stream, read in a long table that is true of the cells c.
The limbs lie dd features apart, and a block's features divide dd. -/
theorem xb_read {R : Model.Head.Run} {K3 lt dd kh l tb : ℕ} {nm : String} {low r : ℕ → K}
    {c : ℕ → ℕ → K} (hX : LongAt W R K3 nm R.h.ls lt low r c) (hst : Starts R nm tb)
    (hd : 2 ^ R.h.ls ∣ dd) (hc : R.b.cell l 0 = dd * l)
    (hv : Valid R tb (R.b.cell l 0 / R.h.S2 + kh)) :
    rdW W R.iU3 K3 (tb + (R.b.cell l 0 / R.h.S2 + kh)) = ∑ s ∈ range (2 ^ R.h.ls),
      Blocks.eqN R.h.ls 0 low s *
        Blocks.ext lt (fun i => c (dd * l + (kh * 2 ^ R.h.ls + s)) i) r := by
  rw [hX tb hst _ hv]
  refine sum_congr rfl fun s _ => ?_
  have hS : R.h.S2 = 2 ^ R.h.ls := rfl
  have hpos : 0 < 2 ^ R.h.ls := by positivity
  obtain ⟨q, hq⟩ := hd
  have e : (R.b.cell l 0 / R.h.S2 + kh) * 2 ^ R.h.ls + s =
      dd * l + (kh * 2 ^ R.h.ls + s) := by
    rw [hS, hc, hq, Nat.mul_assoc, Nat.mul_div_cancel_left _ hpos]
    ring
  rw [e]

/-! ## The stream times the reciprocal -/

/-- The sum that the second sumcheck is about: the weighted sum of the extensions of the products
"value of the stream times reciprocal" is one extension, over the positions, of the reciprocal times
the stream's values under the weights. -/
theorem stream_sum (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (X : ℕ → ℕ → K) (Rr : ℕ → K) :
    wsum g lt u n (fun x i => X x i * Rr i) =
      Blocks.ext lt (fun i => Rr i * ∑ x ∈ range n, g x * X x i) u := by
  unfold wsum Blocks.ext
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

/-- The stream under a segment's block weights, read block by block in a long table that is true of
the cells c: the weighted sum, over the segment's entries, of the extension of the value that the
five limbs spell. -/
theorem stream_cells {R : Model.Head.Run} {K3 lt dd tb : ℕ} {nm : String} {low r : ℕ → K}
    {c : ℕ → ℕ → K} {ew wh : Array E} (hX : LongAt W R K3 nm R.h.ls lt low r c)
    (hst : Starts R nm tb) (hd : 2 ^ R.h.ls ∣ dd) (hc : ∀ l, l < 5 → R.b.cell l 0 = dd * l)
    (hv : ∀ kh, kh < wh.size → ∀ l, l < 5 → Valid R tb (R.b.cell l 0 / R.h.S2 + kh))
    (hB : Blocked ρ ew wh R.h.ls low) :
    ∑ kh ∈ range wh.size, ρ.val (wh.getD kh zeroE) * ∑ l ∈ range 5, (256 : K) ^ l *
        rdW W R.iU3 K3 (tb + (R.b.cell l 0 / R.h.S2 + kh)) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) lt r (wh.size * 2 ^ R.h.ls)
        (fun x i => ∑ l ∈ range 5, (256 : K) ^ l * c (dd * l + x) i) := by
  unfold wsum
  rw [sum_blocks]
  refine sum_congr rfl fun kh hkh => ?_
  have s1 : ∑ l ∈ range 5, (256 : K) ^ l *
        rdW W R.iU3 K3 (tb + (R.b.cell l 0 / R.h.S2 + kh)) =
      ∑ l ∈ range 5, (256 : K) ^ l * ∑ s ∈ range (2 ^ R.h.ls), Blocks.eqN R.h.ls 0 low s *
        Blocks.ext lt (fun i => c (dd * l + (kh * 2 ^ R.h.ls + s)) i) r :=
    sum_congr rfl fun l hl => by
      rw [xb_read hX hst hd (hc l (mem_range.mp hl)) (hv kh (mem_range.mp hkh) l (mem_range.mp hl))]
  rw [s1]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s hs => ?_
  rw [hB kh s (mem_range.mp hs), ← ext_limbs, mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-! ## The squares of the stream -/

/-- What the table of a long table's entries is: the point has at least la coordinates, exactly want
before the last la, and the table is the equality table of these. -/
theorem hiTab_ok {zr : Array E} {la want : ℕ} {e : Array E}
    (h : Model.hiTab zr la want = .ok e) :
    la ≤ zr.size ∧ zr.size - la = want ∧ e = Model.eqTab (zr.extract 0 (zr.size - la)) := by
  unfold Model.hiTab at h
  cases hc : Model.cutLast zr la with
  | error s =>
    rw [hc] at h
    cases h
  | ok c =>
    rw [hc] at h
    obtain ⟨c1, c2⟩ := cutLast_ok hc
    have h' : (if (c.1.size != want) = true then
        (Except.error "plan-tensor-layout" : Except String (Array E))
        else .ok (Model.eqTab c.1)) = .ok e := h
    by_cases hw : (c.1.size != want) = true
    · rw [if_pos hw] at h'
      cases h'
    · rw [if_neg hw] at h'
      have e1 : c.1.size = want := by simpa using hw
      rw [c2, Array.size_extract] at e1
      refine ⟨c1, by omega, ?_⟩
      cases h'
      rw [c2]

/-- The weight of a channel in the claim on the squares' end value is the equality weight of the
layer's point at the channel, if low holds the coordinates of the point that follow the first
want. -/
theorem squares_weight (ρ : Reading K) {zr : Array E} {la want ls : ℕ} {e : Array E}
    (h : Model.hiTab zr la want = .ok e) {low : ℕ → K}
    (hlow : ∀ j, j < ls → low j = pt ρ zr (want + j)) {kh s : ℕ} (hk : kh < 2 ^ want)
    (hs : s < 2 ^ ls) :
    Blocks.eqN (want + ls) 0 (pt ρ zr) (kh * 2 ^ ls + s) =
      ρ.val (e.getD kh zeroE) * Blocks.eqN ls 0 low s := by
  obtain ⟨h1, h2, rfl⟩ := hiTab_ok h
  have hsz : (zr.extract 0 (zr.size - la)).size = want := by
    rw [Array.size_extract]
    omega
  have a1 : Blocks.eqN want 0 (pt ρ (zr.extract 0 (zr.size - la))) kh =
      Blocks.eqN want 0 (pt ρ zr) kh := by
    refine eqN_congr' _ _ (fun j hj => ?_) kh
    have b1 : j < zr.size := by omega
    have b2 : j < zr.size - la := by omega
    have eg : (zr.extract 0 (zr.size - la)).getD j zeroE = zr.getD j zeroE := by
      simp [Array.getD, Array.size_extract, b1, b2]
    unfold pt
    rw [Nat.zero_add, eg]
  have a2 : Blocks.eqN ls want (pt ρ zr) s = Blocks.eqN ls 0 low s := by
    rw [← eqN_shift' ls want (pt ρ zr) s]
    exact eqN_congr' ls 0 (fun j hj => by rw [Nat.zero_add]; exact (hlow j hj).symm) s
  rw [Blocks.eqN_append' want ls 0 (pt ρ zr) kh hs, Nat.zero_add,
    eqTab_value ρ _ kh (by rw [hsz]; exact hk), hsz, a1, a2]

#print axioms ok_map
#print axioms xb_read
#print axioms stream_sum
#print axioms stream_cells
#print axioms hiTab_ok
#print axioms squares_weight

end OnBytes.Road.Hd
