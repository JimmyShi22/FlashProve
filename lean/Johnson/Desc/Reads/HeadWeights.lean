-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadWeights.lean: at the output head's link: the weights on the positions under
which a use's cells are summed are the weights of the relation's own clause. A clause that the
statement of Reads/HeadStated.lean lacks, stated beside it; that the statement can be met without
it; and what pays it.

Why. In the letters of Reads/HeadStated.lean a use's weights are taken from the kind's declaration.
So "each weight" in the address holds by the letters' make. The relation sums (B2) and (B3) over the
positions under the indicator rhoC of its own request, and masks (B4) and (Z) by it, position by
position (`clauses_are`). The kind's declarations weigh by `costed`, a function of the kind's
request. The two requests are two letters, `P.req` and `P.request`, and of `P.req` the statement
reads the clip C alone. So it can be met with weights on the positions that are not the clause's.

What is stated. It is to speak of the one written description at the release's plan; here it stands
over letters.
  `Use.relWeight Y g u j`: the weight of the relation's clause on cell j of the use u, at the
    relation's request Y. For (B2), (B3): rhoC at the position j. For (B4), (Z): rhoC at the
    position, times g at the position: g is the weight of the one point at which the protocol tests
    these clauses. For a block of table values the position of cell j is j % 1024.
  `WeightsAre P s`: for every use and every cell of it, the letters' weight is `relWeight` at `P.req
    s`, with g the reading of the kind's equality weight at the lookup's point zt.
  `HeadClaimW P`: `HeadClaimByDecls P`, and `WeightsAre P s` at every state with closed tables.
Ties of `relWeight` to the relation's text: `rel_sums` (by rfl), `rel_lines`.

What is shown.
  `coef_congr`, `claim_req`: the hole. `HeadClaimByDecls` reads of the relation's request the clip C
    alone: it holds of P with any other `req` that has the same C.
  `weights_of_requests`: a step: what pays the clause. Where the letter val is a reading's map, the
    kind has 1,024 positions, and the two requests have the same first position and the same end,
    `WeightsAre P s` holds. It speaks of the kind's written declarations.
  `tooth_weights`: where, at one position, rhoC of the relation's request is not the kind's
    `costed`, `WeightsAre P s` fails.
  Toys. `head_member_w`: the toy of Reads/HeadMember.lean meets `HeadClaimW`. `otherToy`: the same
    letters with the relation's request from position 5 to 6. `head_other`: it meets
    `HeadClaimByDecls`. `tooth_other`: it fails `HeadClaimW`.
  Tools. `costed_iff`, `rhoC_cast`, `val_phiC`, `weight_sum`, `weight_line`, `weight_block`,
    `first_use`.

Of OnBytes/Model/ this file names `Reading`.

Limits. g is the kind's own letter: that zt is a point drawn behind the commitments, and has all its
coordinates, is a law of the hearing and is not asked here. That the two requests agree is shown of
no description. Four forms of 35. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open Finset
open OnBytes (E mulE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (Req nT)

variable {K : Type} [CommRing K]

/-! ## 1. The clause -/

/-- The weight of the relation's clause on cell j of a use. Y: the relation's request. g: the weight
of the point at which the protocol tests the clauses that hold at each position. -/
def Use.relWeight (Y : Req) (g : ℕ → K) : Use → ℕ → K
  | .byte .B2 _ _, j => ((Y.rhoC j : ℤ) : K)
  | .byte .B3 _ _, j => ((Y.rhoC j : ℤ) : K)
  | .byte .B4 _ _, j => ((Y.rhoC j : ℤ) : K) * g j
  | .byte .Z _ _, j => ((Y.rhoC j : ℤ) : K) * g j
  | .ex _ _, j => ((Y.rhoC (j % nT) : ℤ) : K) * g (j % nT)

/-- The two sums of the relation stand under these weights. -/
theorem rel_sums (t : Inst.Model.Head.Cells K) (Y : Req) (g : ℕ → K) (x : Hid) (l : ℕ) :
    Inst.Model.Head.sB2 t Y =
      ∑ i ∈ range nT, Use.relWeight Y g (.byte .B2 x l) i *
        (Hid.c.value t i + (Y.pol.C : K) * Hid.b.value t i + Hid.u.value t i) -
        (Y.pol.theta : K) * (Y.NB : K) ∧
    Inst.Model.Head.sB3 t Y =
      ∑ i ∈ range nT, Use.relWeight Y g (.byte .B3 x l) i *
        (Hid.b.value t i + Hid.z.value t i) - (if 0 < Y.NB then (Y.pol.cap : K) else 0) :=
  ⟨rfl, rfl⟩

/-- The two clauses that hold at each position, summed under g, stand under these weights. -/
theorem rel_lines (t : Inst.Model.Head.Cells K) (Y : Req) (g : ℕ → K) (x : Hid) (l : ℕ) :
    ∑ i ∈ range nT, g i * Inst.Model.Head.dB4 t Y i =
      ∑ i ∈ range nT, Use.relWeight Y g (.byte .B4 x l) i *
        (Hid.c.value t i + Hid.k.value t i - (Y.pol.C : K)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  show g i * (((Y.rhoC i : ℤ) : K) * (Hid.c.value t i + Hid.k.value t i - (Y.pol.C : K))) =
    ((Y.rhoC i : ℤ) : K) * g i * (Hid.c.value t i + Hid.k.value t i - (Y.pol.C : K))
  ring

/-- For every use and every cell of it the letters' weight is the relation's clause's. -/
def WeightsAre (P : HeadLetters K) (s : P.State) : Prop :=
  ∀ u ∈ P.letters.uses (), ∀ j, j < (P.letters.meant () s u).len →
    (P.letters.meant () s u).w j =
      Use.relWeight (P.req s) (fun t => P.val (letI := P.points s; eq FinalNorm.zt t)) u j

/-- **The statement at the head, with the clause on the weights.** -/
def HeadClaimW (P : HeadLetters K) : Prop :=
  HeadClaimByDecls P ∧ ∀ s, P.AtClose s → WeightsAre P s

/-! ## 2. The hole -/

/-- A use's coefficient reads of the relation's request the clip alone. -/
theorem coef_congr {Y Y' : Req} (h : Y.pol.C = Y'.pol.C) (u : Use) :
    (Use.coef Y u : K) = Use.coef Y' u := by
  rcases u with ⟨cl, x, l⟩ | ⟨l, blk⟩
  · cases cl <;> cases x <;> first | rfl | (show ((Y.pol.C : ℕ) : K) * _ = _; rw [h]; rfl)
  · rfl

/-- **The statement of Reads/HeadStated.lean reads of the relation's request the clip alone.** -/
theorem claim_req (P : HeadLetters K) (req' : P.State → Req)
    (hC : ∀ s, (P.req s).pol.C = (req' s).pol.C) (H : HeadClaimByDecls P) :
    HeadClaimByDecls { P with req := req' } := by
  obtain ⟨⟨h1, h2, h3, h4⟩, hB⟩ := H
  refine ⟨⟨h1, h2, h3, h4⟩, fun l hl s hs => ?_⟩
  obtain ⟨a, b, c, d⟩ := hB l hl s hs
  refine ⟨a, b, c, d.1, fun n f hf => ⟨(d.2 n f hf).1, fun v => ((d.2 n f hf).2 v).trans ?_⟩⟩
  unfold Letters.clauseValue
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  show Use.coef (P.req s) u * _ = Use.coef (req' s) u * _
  rw [coef_congr (hC s) u]
  rfl

/-! ## 3. What pays the clause -/

section Sized
variable [iS : Head.Sizes] [iR : Head.Request]

/-- At 1,024 positions and one stretch, the kind's "has a cost" is the relation's "is counted". -/
theorem costed_iff (Y : Req) (hT : Norm.T = nT) (hr : Y.r = Head.Request.r)
    (he : Y.e = Head.Request.e) (t : ℕ) :
    Head.costed t = true ↔ (Y.r ≤ t ∧ t < min Y.e 1023) := by
  have hN : nT = 1024 := rfl
  unfold Head.costed Head.checked
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hT, hN, hr, he]
  omega

theorem rhoC_cast (Y : Req) (hT : Norm.T = nT) (hr : Y.r = Head.Request.r)
    (he : Y.e = Head.Request.e) (t : ℕ) :
    ((Y.rhoC t : ℤ) : K) = if Head.costed t = true then 1 else 0 := by
  unfold Req.rhoC
  by_cases h : Head.costed t = true
  · rw [if_pos h, if_pos ((costed_iff Y hT hr he t).1 h), Int.cast_one]
  · rw [if_neg h, if_neg (fun q => h ((costed_iff Y hT hr he t).2 q)), Int.cast_zero]

variable [iI : FinalNorm.In]

/-- The reading of the kind's weight of zt at the positions with a cost. -/
theorem val_phiC (ρ : Reading K) (Y : Req) (hT : Norm.T = nT) (hr : Y.r = Head.Request.r)
    (he : Y.e = Head.Request.e) (t : ℕ) :
    ρ.val (Head.phiC t) = ((Y.rhoC t : ℤ) : K) * ρ.val (eq FinalNorm.zt t) := by
  have h0 : ρ.val (0 : E) = 0 := (reading_ofNat ρ 0).trans Nat.cast_zero
  show ρ.val (if Head.costed t = true then eq FinalNorm.zt t else (0 : E)) = _
  rw [rhoC_cast Y hT hr he t]
  by_cases h : Head.costed t = true
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, h0]

variable [iH : Head.Heard]

/-- The declared weights of rowCount. -/
theorem weight_sum (ρ : Reading K) (S : Seat) (Y : Req) (hT : Norm.T = nT)
    (hr : Y.r = Head.Request.r) (he : Y.e = Head.Request.e) (j : ℕ) :
    ρ.val ((declOf S .rowCount).w j) = ((Y.rhoC j : ℤ) : K) := by
  have h0 : ρ.val (0 : E) = 0 := (reading_ofNat ρ 0).trans Nat.cast_zero
  have h1 : ρ.val (1 : E) = 1 := (reading_ofNat ρ 1).trans Nat.cast_one
  show ρ.val (if Head.costed j = true then (1 : E) else (0 : E)) = _
  rw [rhoC_cast Y hT hr he j]
  by_cases h : Head.costed j = true
  · rw [if_pos h, if_pos h, h1]
  · rw [if_neg h, if_neg h, h0]

/-- The declared weights of rowAtCosts. -/
theorem weight_line (ρ : Reading K) (S : Seat) (Y : Req) (hT : Norm.T = nT)
    (hr : Y.r = Head.Request.r) (he : Y.e = Head.Request.e) (j : ℕ) :
    ρ.val ((declOf S .rowAtCosts).w j) = ((Y.rhoC j : ℤ) : K) * ρ.val (eq FinalNorm.zt j) :=
  val_phiC ρ Y hT hr he j

/-- The declared weights of wideAtCosts. -/
theorem weight_block (ρ : Reading K) (S : Seat) (Y : Req) (hT : Norm.T = nT)
    (hr : Y.r = Head.Request.r) (he : Y.e = Head.Request.e) (j : ℕ) :
    ρ.val ((declOf S .wideAtCosts).w j) =
      ((Y.rhoC (j % nT) : ℤ) : K) * ρ.val (eq FinalNorm.zt (j % nT)) := by
  have h1 : ρ.val (1 : E) = 1 := (reading_ofNat ρ 1).trans Nat.cast_one
  show ρ.val (mulE (1 : E) (Head.phiC (j % Norm.T))) = _
  rw [ρ.mul, h1, one_mul, hT]
  exact val_phiC ρ Y hT hr he (j % nT)

omit iR iI iH in
/-- The low byte of paid in (B2) is a use. -/
theorem first_use : Use.byte .B2 .c 0 ∈ usesH :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨.B2, List.mem_cons.2 (Or.inl rfl),
    List.mem_flatMap.2 ⟨.c, List.mem_cons.2 (Or.inl rfl),
      List.mem_map.2 ⟨0, List.mem_range.2 (by decide), rfl⟩⟩⟩)

end Sized

/-- **What pays the clause**: a reading, 1,024 positions, and one stretch in the two requests. -/
theorem weights_of_requests (P : HeadLetters K) (s : P.State) {ρ : Reading K}
    (hval : P.val = ρ.val) (hT : (letI := P.sizes; Norm.T) = nT)
    (hr : (P.req s).r = (P.request s).r) (he : (P.req s).e = (P.request s).e) :
    WeightsAre P s := by
  intro u _ j _
  have hs := weight_sum (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iH := P.heard s)
    ρ P.seat (P.req s) hT hr he j
  have hl := weight_line (iS := P.sizes) (iR := P.request s) (iI := P.points s)
    (iH := P.heard s) ρ P.seat (P.req s) hT hr he j
  have hb := weight_block (iS := P.sizes) (iR := P.request s) (iI := P.points s)
    (iH := P.heard s) ρ P.seat (P.req s) hT hr he j
  rw [← hval] at hs hl hb
  rcases u with ⟨cl, x, l⟩ | ⟨l, blk⟩
  · cases cl
    · exact hs
    · exact hs
    · exact hl
    · exact hl
  · exact hb

/-- Where rhoC of the relation's request is not the kind's costed at one position, the clause
fails. -/
theorem tooth_weights (P : HeadLetters K) (s : P.State) {ρ : Reading K} (hval : P.val = ρ.val)
    (t : ℕ) (ht : t < nT)
    (hne : (((P.req s).rhoC t : ℤ) : K) ≠
      if (letI := P.sizes; letI := P.request s; Head.costed t) = true then 1 else 0) :
    ¬ WeightsAre P s := by
  intro H
  have h0 : ρ.val (0 : E) = 0 := (reading_ofNat ρ 0).trans Nat.cast_zero
  have h1 : ρ.val (1 : E) = 1 := (reading_ofNat ρ 1).trans Nat.cast_one
  have h := H (.byte .B2 .c 0) (first_use (iS := P.sizes)) t ht
  have h' : P.val (if (letI := P.sizes; letI := P.request s; Head.costed t) = true
      then (1 : E) else (0 : E)) = (((P.req s).rhoC t : ℤ) : K) := h
  refine hne (h'.symm.trans ?_)
  rw [hval]
  by_cases hc : (letI := P.sizes; letI := P.request s; Head.costed t) = true
  · rw [if_pos hc, if_pos hc, h1]
  · rw [if_neg hc, if_neg hc, h0]

/-! ## 4. Toys -/

/-- The toy of Reads/HeadMember.lean meets the statement with the clause on the weights. -/
theorem head_member_w : HeadClaimW memberToy :=
  ⟨head_member, fun s _ => weights_of_requests (ρ := Reading.gl) memberToy s rfl rfl rfl rfl⟩

/-- The same letters, with the relation's request from position 5 to 6. -/
noncomputable def otherToy : HeadLetters Cb.Gl.E :=
  { memberToy with req := fun _ => ⟨5, 6, fun _ => 0, ⟨128, 128, 0⟩⟩ }

/-- It meets the statement of Reads/HeadStated.lean. -/
theorem head_other : HeadClaimByDecls otherToy :=
  claim_req memberToy _ (fun _ => rfl) head_member

/-- It fails the statement with the clause on the weights: position 0 has a cost by the kind's
request and is not counted by the relation's. -/
theorem tooth_other : ¬ HeadClaimW otherToy := fun H =>
  tooth_weights (ρ := Reading.gl) otherToy () rfl 0 (by decide)
    (by
      show ((0 : ℤ) : Cb.Gl.E) ≠ 1
      rw [Int.cast_zero]
      exact zero_ne_one) (H.2 () trivial)

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.rel_sums
#print axioms VerifiableInference.Reads.AtHead.rel_lines
#print axioms VerifiableInference.Reads.AtHead.coef_congr
#print axioms VerifiableInference.Reads.AtHead.claim_req
#print axioms VerifiableInference.Reads.AtHead.costed_iff
#print axioms VerifiableInference.Reads.AtHead.rhoC_cast
#print axioms VerifiableInference.Reads.AtHead.val_phiC
#print axioms VerifiableInference.Reads.AtHead.weight_sum
#print axioms VerifiableInference.Reads.AtHead.weight_line
#print axioms VerifiableInference.Reads.AtHead.weight_block
#print axioms VerifiableInference.Reads.AtHead.first_use
#print axioms VerifiableInference.Reads.AtHead.weights_of_requests
#print axioms VerifiableInference.Reads.AtHead.tooth_weights
#print axioms VerifiableInference.Reads.AtHead.head_member_w
#print axioms VerifiableInference.Reads.AtHead.head_other
#print axioms VerifiableInference.Reads.AtHead.tooth_other
