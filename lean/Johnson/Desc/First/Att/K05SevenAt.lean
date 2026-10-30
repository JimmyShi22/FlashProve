-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SevenAt.lean: the plain facts on letters and public numbers that the
statements on the kind K5 leave, at the caller over the committed symbols (`baseOf`,
Johnson/Desc/First/Att/K05Caller.lean) with the lookup's calls C := `callsOf` fs: from "`shapeHid`
has returned (S, fs)" and the public test `CallsFit` S fs (Johnson/Road/Lane5CallsOf.lean).

Definitions, statements and proofs.
Main names:
  `cellAt S pl`: the place of a cell among the entries of `baseOf`.
  `lT_le_16`: a position has at most 16 bits.
  `seven_at_base`: seven facts: `baseOf` reads its cells at `cellAt`; S.ls ≤ D.ln; S.cf.lmS is at
    most the ℓ of each family of planes; C.a 0 = C.a 1; the ℓ of each family of planes is at most
    its call's size; lT ≤ 2 ^ kap; there are two plane messages.
  `kfExt_at_base`: the three premises of `kfExt` (Inst/Model/Att/KeyFormsExt/All.lean), at the
    scales `sclOf` S.
Used: pure functions of public numbers and lemmas on them alone; no routine in a
context: `sizes_of_hid`, `norm_of_hid`, `shape_of_hid`, `shaped_of_hid`, `lt_le_16`, `callsFit_ok`,
`callsFit_deep`, `callsFit_a01`, `rdOf`, `IsPlane`.
Limits: that `shapeHid` returns at the numbers of a parameter file, and that `CallsFit` holds there,
is not shown in this file or in what it imports (Johnson/Road/Lane5CallsOf.lean evaluates the test
at two typed configurations). Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58Proofs
import Johnson.Road.Lane5CallsOf
import Cb.Pv.Att.End.Lin
import Johnson.Desc.First.Att.K05Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes.Road.L5 (callsOf CallsFit dimOf addrA)
open Cb.Pv.Tail (Size Syms JCell)

variable {K : Type} [Field K] [Fintype K] {X : Type} {s : Size}

/-- The place of a cell among the entries of baseOf. -/
def cellAt (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (c : AttSeg.Raw) : Option (JCell s) :=
  some (pl (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2)

section At
variable {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}

/-- A position has at most 16 bits. -/
theorem lT_le_16 (hh : Attention.shapeHid lid cf = Except.ok (S, fs)) : (dimOf S).lT ≤ 16 := by
  obtain ⟨A, hA⟩ := OnBytes.Road.L5.shape_of_hid hh
  have h16 := OnBytes.Road.Rows.lt_le_16 hA
  have N := OnBytes.Road.Rows.norm_of_hid hh
  have hc := (OnBytes.Road.L5.shaped_of_hid hh).cfg
  have e : (dimOf S).lT = S.cf.lt := N.lt.symm
  rw [e, hc]
  exact h16

/-- **The seven.** -/
theorem seven_at_base (hh : Attention.shapeHid lid cf = Except.ok (S, fs)) (hf : CallsFit S fs)
    (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → K) :
    (∀ e, (baseOf (K := K) S pl (callsOf fs) 2 zOf).rd e = rdOf (cellAt S pl) e) ∧
    S.ls ≤ (baseOf (K := K) S pl (callsOf fs) 2 zOf).D.ln ∧
    (∀ u : AttSeg.Fam, IsPlane u → S.cf.lmS ≤ u.l (baseOf (K := K) S pl (callsOf fs) 2 zOf).D) ∧
    (baseOf (K := K) S pl (callsOf fs) 2 zOf).C.a 0 = (baseOf (K := K) S pl (callsOf fs) 2 zOf).C.a 1 ∧
    (∀ u : AttSeg.Fam, IsPlane u → u.l (baseOf (K := K) S pl (callsOf fs) 2 zOf).D ≤
      (baseOf (K := K) S pl (callsOf fs) 2 zOf).C.a u.call) ∧
    (baseOf (K := K) S pl (callsOf fs) 2 zOf).D.lT ≤ 2 ^ (baseOf (K := K) S pl (callsOf fs) 2 zOf).kap ∧
    (baseOf (K := K) S pl (callsOf fs) 2 zOf).npl = 2 := by
  have Z := OnBytes.Road.Rows.sizes_of_hid hh
  have N := OnBytes.Road.Rows.norm_of_hid hh
  have hD : S.cf.lmS ≤ (dimOf S).lD := by
    have e : (dimOf S).lD = S.nD := N.nD.symm
    rw [e]
    exact Z.lmS
  have hM : (dimOf S).lD ≤ (dimOf S).lM := by
    unfold Dim.lD Dim.lM
    omega
  refine ⟨fun _ => rfl, Z.ls, fun u hu => ?_, OnBytes.Road.L5.callsFit_a01 hf,
    fun u _ => le_trans (OnBytes.Road.L5.callsFit_deep hf u) (hf.2.1 u.call), ?_, rfl⟩
  · cases u with
    | m1 => exact le_trans hD hM
    | d1 => exact hD
    | m2 => exact le_trans hD hM
    | d2 => exact hD
    | w3 => exact hu.elim
    | x3 => exact hu.elim
    | f4 => exact hu.elim
  · show (dimOf S).lT ≤ 2 ^ 4
    have := lT_le_16 hh
    omega

/-- kfExt's three premises at that caller, at the scales of the shape. -/
theorem kfExt_at_base (hf : CallsFit S fs) :
    Calls.OK (scl := OnBytes.Road.L5.sclOf S) (callsOf fs) (dimOf S) ∧
    (∀ u : AttSeg.Fam, u.l (dimOf S) ≤ (callsOf fs).Dk) ∧ (callsOf fs).a 0 = (callsOf fs).a 1 :=
  ⟨OnBytes.Road.L5.callsFit_ok hf, OnBytes.Road.L5.callsFit_deep hf, OnBytes.Road.L5.callsFit_a01 hf⟩

end At

end VerifiableInference.Desc.First.Att.P
