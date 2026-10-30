-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/TieSim.lean: what the copy over the field of the program's sumcheck
(`PscF.outOf`) hands on at a step of a lookup's tie, read as linear forms on a type of entries, is
what the plain function of the flat rounds computes at that step.

The program's sumcheck computes on machine words. It has a copy of its text over the field
(`PscF.outOf`: OnBytes/Slice/KeyPscRun.lean); that the first, read in the field, is the second is
`read_run` of OnBytes/Slice/BlkPscRead.lean, which this file does not use.
OnBytes/Tie/Pv/KeyLookup/PortSim.lean reads the copy's mask forms as functions on a type J of
entries (`rdMF`), what was heard as flat rounds (`flatY`), and has the tie's two summands over the
field (`sTie1`, `sTie`) with the theorems that the program's summands read as them.
Cb/Pv/KeyLookup/TieRun.lean has the steps of the tie as plain functions of the flat rounds
(`TieR.step0`, `TieR.stepN`) and proves that at the short sumcheck (`SK₀`:
Cb/Pv/KeyLookup/Short0.lean) the verifier of the lookup's head, in the library's types, puts out
what they compute. This file holds the two against each other, step by step.

Main names:
  `tie1_out`, `tieN_out`: `PscF.outOf` at the first step (no claim comes in; target 0; summand
  `sTie1 a`; seven fresh mask entries) and at a later step (the claim on the power that was taken
  up; summand `sTie`; six fresh mask entries), at what was heard written out, field by field.
  `row_eq`, `fin_eq`: the row's mask form and the last value of the running claim, in both forms.
  `tie1_step`: the first step: the open claim is the second end, the claim on the product of all
  roots the first, plane 0's the third; the row is appended.
  `tieN_step`: a later step l: the open claim is the first end, plane l's claim the second; the row
  is appended.
Limits: there are six conditions. Four are on the places of the fresh mask entries: of the four that
bear the first polynomial's coefficients the first stands at `w (inr ())` (the constant's), the
others at `w (inl 0)`, `w (inl 1)`, `w (inl 2)`. Two are on the flat state that comes in: its open
claim has the form and the target of the claim that comes in (at the first step: the empty form and
0). What was heard has one fixed shape: one scalar, three coefficients, and three or two values. One
step each. Nothing on how the steps are joined, nothing on the program's blocks on machine words,
nothing on soundness.

-/
import OnBytes.Tie.Pv.KeyLookup.PortSim
import Cb.Pv.KeyLookup.TieRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.TieSim

open OnBytes OnBytes.Slice Lk6.PortSim Cb Cb.LdLkp

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- The two functions "c at one entry" are one. -/
theorem one_eq (i : J) (c : GE) : Parts.one i c = NoVar.one i c := rfl

/-- A form with one term. -/
theorem rdMF_one (s : Slot) (c : GE) : rdMF sl [(s, c)] = NoVar.one (sl s) c := by
  funext j
  rw [rdMF_cons, rdMF_nil, add_zero]
  rfl

/-- What the first step hands on, field by field. -/
theorem tie1_out (a : GE) (s0 s1 s2 s3 s4 s5 s6 : Slot) (mu eps q1 q2 q3 be v0 v1 v2 : GE) :
    PscF.outOf (onValue noClaim) (sTie1 a) [s0, s1, s2, s3, s4, s5, s6]
        ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩ =
      { point := []
        rowMasks := [(s0, 1), (s1, 1 * be), (s2, 1 * be * be), (s3, 1 * be * be * be)] ++
          PscF.scaleForm (eps * (0 * be + 1)) []
        rowMaps := []
        rowTarget := PscF.polyAt ((PscF.Weight.atZero 4).complete [q1, q2, q3]
          (mu + eps * 0)) be - eps * (v0 - a * v1 * v1 * v2)
        ends := [⟨[], [(s4, be)], v0⟩, ⟨[], [(s5, be)], v1⟩, ⟨[], [(s6, be)], v2⟩]
        eps := eps
        beta := some be } := rfl

/-- What a later step hands on, field by field. -/
theorem tieN_out (c : PscF.PointClaim) (s0 s1 s2 s3 s4 s5 : Slot)
    (mu eps q1 q2 q3 be v0 v1 : GE) :
    PscF.outOf (onValue c) sTie [s0, s1, s2, s3, s4, s5]
        ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩ =
      { point := []
        rowMasks := [(s0, 1), (s1, 1 * be), (s2, 1 * be * be), (s3, 1 * be * be * be)] ++
          PscF.scaleForm (eps * (0 * be + 1)) c.masks
        rowMaps := []
        rowTarget := PscF.polyAt ((PscF.Weight.atZero 4).complete [q1, q2, q3]
          (mu + eps * c.value)) be - eps * (v0 * v0 * v1)
        ends := [⟨[], [(s4, be)], v0⟩, ⟨[], [(s5, be)], v1⟩]
        eps := eps
        beta := some be } := rfl

section
variable (w : PIdx (([] : List (PFmt GE)) ++ [pDummy GE 3]) → J) (s0 s1 s2 s3 : Slot)
  (h0 : w (Sum.inr () : Fin 3 ⊕ Unit) = sl s0) (h1 : w (Sum.inl 0 : Fin 3 ⊕ Unit) = sl s1)
  (h2 : w (Sum.inl 1 : Fin 3 ⊕ Unit) = sl s2) (h3 : w (Sum.inl 2 : Fin 3 ⊕ Unit) = sl s3)

include h0 h1 h2 h3 in
/-- The row's mask form, in both forms. -/
theorem row_eq (mf : J → GE) (F : PscF.MaskForm) (hm : mf = rdMF sl F)
    (mu eps q1 q2 q3 be : GE) (vals : List GE) :
    rdMF sl ([(s0, 1), (s1, 1 * be), (s2, 1 * be * be), (s3, 1 * be * be * be)] ++
        PscF.scaleForm (eps * (0 * be + 1)) F) =
      NoVar.rowF 3 w mf (flatY ⟨mu, eps, [([q1, q2, q3], be)], vals⟩) := by
  funext j
  rw [rdMF_append, rdMF_scale, rdMF_cons, rdMF_cons, rdMF_cons, rdMF_cons, rdMF_nil]
  show _ = (∑ t : Fin 3, NoVar.one (w (Sum.inl t : Fin 3 ⊕ Unit)) (be ^ ((t : ℕ) + 1)) j) +
    NoVar.one (w (Sum.inr () : Fin 3 ⊕ Unit)) 1 j + eps * mf j
  rw [Fin.sum_univ_three, h0, h1, h2, h3, hm]
  have c1 : (1 : GE) * be = be := _root_.one_mul be
  have c2 : (1 : GE) * be * be = be ^ 2 := by ring
  have c3 : (1 : GE) * be * be * be = be ^ 3 := by ring
  have d1 : be ^ (((0 : Fin 3) : ℕ) + 1) = be := pow_one be
  have d2 : be ^ (((1 : Fin 3) : ℕ) + 1) = be ^ 2 := rfl
  have d3 : be ^ (((2 : Fin 3) : ℕ) + 1) = be ^ 3 := rfl
  rw [c3, c2, c1, d1, d2, d3]
  simp only [one_eq]
  ring

end

/-- The last value of the running claim, in both forms. -/
theorem fin_eq (tg mu eps q1 q2 q3 be : GE) (vals : List GE) :
    PscF.polyAt ((PscF.Weight.atZero 4).complete [q1, q2, q3] (mu + eps * tg)) be =
      NoVar.finF 3 tg (flatY ⟨mu, eps, [([q1, q2, q3], be)], vals⟩) := by
  show _ = mu + eps * tg +
    ∑ t : Fin 3, ([q1, q2, q3] : List GE).getD t.val 0 * be ^ ((t : ℕ) + 1)
  rw [Fin.sum_univ_three]
  show _ = mu + eps * tg + (q1 * be ^ 1 + q2 * be ^ 2 + q3 * be ^ 3)
  simp only [PscF.Weight.complete, PscF.Weight.atZero, PscF.Weight.equality, List.take_zero,
    List.drop_zero, List.nil_append, PscF.polyAt_cons, PscF.polyAt_nil, PscF.dot_cons,
    PscF.dot_nil_left, List.replicate]
  ring

/-- **The first step of the tie.** -/
theorem tie1_step (a : GE) (w : PIdx (([] : List (PFmt GE)) ++ [pDummy GE 3]) → J)
    (s0 s1 s2 s3 s4 s5 s6 : Slot) (h0 : w (Sum.inr () : Fin 3 ⊕ Unit) = sl s0)
    (h1 : w (Sum.inl 0 : Fin 3 ⊕ Unit) = sl s1) (h2 : w (Sum.inl 1 : Fin 3 ⊕ Unit) = sl s2)
    (h3 : w (Sum.inl 2 : Fin 3 ⊕ Unit) = sl s3) (mu eps q1 q2 q3 be v0 v1 v2 : GE)
    (s : TieR.TAcc GE J) (hm : s.mf = rdMF sl []) (ht : s.tg = 0) :
    let o := PscF.outOf (onValue noClaim) (sTie1 a) [s0, s1, s2, s3, s4, s5, s6]
      ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩
    TieR.step0 a w (sl s4) (sl s5) (sl s6) s
        (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩) =
      { mf := rdMF sl (o.ends.getD 1 noClaim).masks
        tg := (o.ends.getD 1 noClaim).value
        all := ⟨rdMF sl (o.ends.getD 0 noClaim).masks, (o.ends.getD 0 noClaim).value⟩
        planes := fun j => if j = 0 then
          ⟨rdMF sl (o.ends.getD 2 noClaim).masks, (o.ends.getD 2 noClaim).value⟩ else s.planes j
        rows := s.rows ++ [⟨rdMF sl o.rowMasks, o.rowTarget⟩] } := by
  intro o
  have e0 : rdMF sl (o.ends.getD 0 noClaim).masks = NoVar.one (sl s4) be := rdMF_one sl s4 be
  have e1 : rdMF sl (o.ends.getD 1 noClaim).masks = NoVar.one (sl s5) be := rdMF_one sl s5 be
  have e2 : rdMF sl (o.ends.getD 2 noClaim).masks = NoVar.one (sl s6) be := rdMF_one sl s6 be
  have er : rdMF sl o.rowMasks =
      NoVar.rowF 3 w s.mf (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩) :=
    row_eq sl w s0 s1 s2 s3 h0 h1 h2 h3 s.mf [] hm mu eps q1 q2 q3 be [v0, v1, v2]
  have et : o.rowTarget =
      NoVar.finF 3 s.tg (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1, v2]⟩) -
        eps * (v0 - a * (v1 ^ 2 * v2)) := by
    show PscF.polyAt ((PscF.Weight.atZero 4).complete [q1, q2, q3] (mu + eps * 0)) be -
      eps * (v0 - a * v1 * v1 * v2) = _
    rw [ht, ← fin_eq 0 mu eps q1 q2 q3 be [v0, v1, v2]]
    ring
  rw [e0, e1, e2, er, et]
  rfl

/-- **A later step of the tie.** -/
theorem tieN_step (c : PscF.PointClaim) (w : PIdx (([] : List (PFmt GE)) ++ [pDummy GE 3]) → J)
    (s0 s1 s2 s3 s4 s5 : Slot) (h0 : w (Sum.inr () : Fin 3 ⊕ Unit) = sl s0)
    (h1 : w (Sum.inl 0 : Fin 3 ⊕ Unit) = sl s1) (h2 : w (Sum.inl 1 : Fin 3 ⊕ Unit) = sl s2)
    (h3 : w (Sum.inl 2 : Fin 3 ⊕ Unit) = sl s3) (mu eps q1 q2 q3 be v0 v1 : GE) (l : ℕ)
    (s : TieR.TAcc GE J) (hm : s.mf = rdMF sl c.masks) (ht : s.tg = c.value) :
    let o := PscF.outOf (onValue c) sTie [s0, s1, s2, s3, s4, s5]
      ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩
    TieR.stepN w (sl s4) (sl s5) l s (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩) =
      { mf := rdMF sl (o.ends.getD 0 noClaim).masks
        tg := (o.ends.getD 0 noClaim).value
        all := s.all
        planes := fun j => if j = l then
          ⟨rdMF sl (o.ends.getD 1 noClaim).masks, (o.ends.getD 1 noClaim).value⟩ else s.planes j
        rows := s.rows ++ [⟨rdMF sl o.rowMasks, o.rowTarget⟩] } := by
  intro o
  have e0 : rdMF sl (o.ends.getD 0 noClaim).masks = NoVar.one (sl s4) be := rdMF_one sl s4 be
  have e1 : rdMF sl (o.ends.getD 1 noClaim).masks = NoVar.one (sl s5) be := rdMF_one sl s5 be
  have er : rdMF sl o.rowMasks =
      NoVar.rowF 3 w s.mf (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩) :=
    row_eq sl w s0 s1 s2 s3 h0 h1 h2 h3 s.mf c.masks hm mu eps q1 q2 q3 be [v0, v1]
  have et : o.rowTarget =
      NoVar.finF 3 s.tg (flatY ⟨mu, eps, [([q1, q2, q3], be)], [v0, v1]⟩) -
        eps * (v0 ^ 2 * v1) := by
    show PscF.polyAt ((PscF.Weight.atZero 4).complete [q1, q2, q3] (mu + eps * c.value)) be -
      eps * (v0 * v0 * v1) = _
    rw [ht, ← fin_eq c.value mu eps q1 q2 q3 be [v0, v1]]
    ring
  rw [e0, e1, er, et]
  rfl

end Lk6.TieSim

#print axioms Lk6.TieSim.tie1_out
#print axioms Lk6.TieSim.tieN_out
#print axioms Lk6.TieSim.tie1_step
#print axioms Lk6.TieSim.tieN_step
