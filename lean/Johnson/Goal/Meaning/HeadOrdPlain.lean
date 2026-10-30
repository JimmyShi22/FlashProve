-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadOrdPlain.lean: where the head's sub-proof is in order at its list of
integer matrices, the head's half holds in plain integers, at the stream that the library reads in
the head's cells.

WHY. MeansH.plain (HeadPlain, Johnson/Goal/Meaning/Row.lean) is a conclusion: it applies the integer
program's own functions to a stream and the output matrix. The library's statement on the head's
list is Hd.HeadOrdLB (Johnson/Road/HeadL5BL.lean): the entries inside the matrices' shapes are below
2^18; every key is an entry of its table; the 17 identities of the final normalisation, the cost
ledger's two lines and two sums are 0 modulo the protocol's prime; y = 0 if e is before the window's
end. This file leads from the second to the first, at public files in the goals' scope.

  small_cellsH      under SmallH the head's cells, as the verifier's rule reads them in the list,
                    are below 2^18 (by placeIn_inside, Johnson/Road/HeadPlace.lean).
  headRF_of_ord     so HeadOrdLB gives the library's relation of the head with the cost ledger
                    (Policy.LedgerHead.RF) at these cells.
  headPlain_of_ord  so, in scope, HeadPlain holds at the stream Head.xv of these cells: by the
                    library's Policy.ledger_head_noWrap at the protocol's prime, and by
                    readings_agree (Johnson/Goal/Meaning/Ties.lean) for the final normalisation's
                    numbers and the policy.
  headOrd_of_true   a guard: the premise can be met: in scope, at every index and every request that
                    is true at it under the files' policy, some list is in order (the library's
                    ordsL_of_true, Johnson/Road/Lane5TopLTrue.lean).

What is not claimed. That any sub-proof's law ends in HeadOrdLB. That the stream in the head's cells
is the stream that the last group of layers put out (HeadSeam). Head3 x is a premise; every request
of the frame has it (head3_of_req). Nothing on probabilities or on hiding. The full size alone.
-/
import Johnson.Goal.Meaning.Row
import Johnson.Goal.Meaning.LayersSay
import Johnson.Road.HeadL5BL
import Johnson.Road.Lane5TopLTrue

set_option autoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Head (HL Border)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-- **Under SmallH the head's cells are small.** -/
theorem small_cellsH {h : Model.Head.Shape} {L : HL} {b : Border} (N : Hd.NumH h L)
    (Bd : Hd.BorderH b) {Mh : Mats ℤ} (Sm : Hd.SmallH h L b Mh) :
    Head.Small (Hd.cellsH h L b Mh) := by
  intro i hi
  have hi' : i < 1024 := hi
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) hi').1 (Nat.lt_add_right 128 hφ)
    show |Hd.cellIn Mh 0 L.k (L.m / h.T) h.T φ i| < 2 ^ 18
    rw [Hd.cellIn_place, Nat.zero_add]
    exact Sm.1 _ hin.1 _ hin.2.1 _ hin.2.2
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) hi').2.1 hφ
    show |Hd.cellIn Mh h.NHf L.kD (L.mD / h.T) h.T φ i| < 2 ^ 18
    rw [Hd.cellIn_place, hin.1, Nat.add_zero]
    exact Sm.2.1 _ hin.2.1 _ hin.2.2
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) hi').2.2.1 hφ
    show |Hd.cellIn Mh (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i| < 2 ^ 18
    rw [Hd.cellIn_place, hin.1, Nat.add_zero]
    exact Sm.2.2.1 _ hin.2.1 _ hin.2.2
  · have hφ' : φ < 25600 := hφ
    have hc : b.cell (φ / h.d) (φ % h.d) < Head.nFeat .x := by
      rw [Bd.cell, N.d]
      show 5120 * (φ / 5120) + φ % 5120 < 25600
      omega
    have hin := (Hd.placeIn_inside N Bd (φ := b.cell (φ / h.d) (φ % h.d)) hi').2.2.2 hc
    show |Hd.cellIn Mh (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i| < 2 ^ 18
    rw [Hd.cellIn_place, hin.1, Nat.add_zero]
    exact Sm.2.2.2 _ hin.2.1 _ hin.2.2

/-- **The head in order at its list gives the library's relation of the head at the cells.** -/
theorem headRF_of_ord {h : Model.Head.Shape} {L : HL} {y : Model.Layer.Lay} (N : Hd.NumH h L)
    (Bd : Hd.BorderH (borderOf y)) {np : NormPar} {pol : AcceptancePolicy} {Wz : Mat} {x : Instance ppref}
    {Mh : Mats ℤ} (O : Hd.HeadOrdLB h L y np pol Wz x Mh) :
    Policy.LedgerHead.RF (F := ZMod Cb.Gl.p) np (Cm.TP.castH Cb.Gl.p Wz) (Head.Req.of pol x)
      (Hd.cellsH h L (borderOf y) Mh) :=
  ⟨small_cellsH N Bd O.1, O.2.1.1, O.2.1.2.1, O.2.1.2.2.1, O.2.1.2.2.2⟩

/-- **In scope: the head in order at its list gives the head's half in plain integers**, at the
stream that the library reads in the head's cells. -/
theorem headPlain_of_ord {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) (Mh : Mats ℤ)
    (hx : Head3 x)
    (O : Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x Mh) :
    HeadPlain pp i x fun pos j => Head.xv (Hd.cellsH X.hS X.HLy (borderOf X.y) Mh) j pos := by
  have A := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  have NH := Hd.numH_of_layout B.full B.head
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  have W := (Policy.ledger_head_noWrap Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big
    (scalesAt X).nf hs.nf i.weights.H (abs_H i.wf) (Hd.polOf X.hS) hpol x _
    (headRF_of_ord NH Bd O)).2
    (fun pos j => Head.xv (Hd.cellsH X.hS X.HLy (borderOf X.y) Mh) j pos) (fun _ _ _ _ => rfl)
  have en : pp.nf = (scalesAt X).nf := congrArg Cm.Scales.nf tS
  show SaysHead pp.nf pp.pol i.index.val.H x _
  rw [en, tP]
  exact ⟨W.1, hx, W.2⟩

/-- **The premise can be met**: in scope, at every true request some list of the head is in order.
-/
theorem headOrd_of_true {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    ∃ Mh : Mats ℤ, Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x Mh := by
  have A := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS' ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  have T' : Policy.IsTrueUnder (scalesAt X) (Hd.polOf X.hS) i x := by
    rw [← tS', ← tP]
    exact T
  obtain ⟨Zl, ZA, O⟩ : ∃ (Zl : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
        (Hd.shapeA X) i.mat x Zl ZA :=
    ⟨_, _, ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1
      E.2.2.2.2 E.2.2.1 E.2.2.2.1 hs hpol i x T'⟩
  exact ⟨_, O.head⟩

end Meaning

#print axioms Meaning.headOrd_of_true
#print axioms Meaning.small_cellsH
#print axioms Meaning.headRF_of_ord
#print axioms Meaning.headPlain_of_ord
