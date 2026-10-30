-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttKfVal.lean.
The attention sub-proof: the value of each call's key form, in every world, as a formula in the
hidden values under slots alone.

A key form of the attention sub-proof names slots and public constants, and no entry of a virtual
row. This file reads each of them, under every reading of the byte-level field and in every world.
The public constants stay as the byte-level verifier computes them, read. Each statement follows by
unfolding the form and the laws of Aff.value (OnBytes/Model/HideLaws.lean).

States:
  keyKR_value, keyKFD_value, remForm_value, indexForm_value, keyWL_value, keyIX_value, keyWH_value:
    what one unit, or one segment, adds.
  foldIf_value: a loop that adds a form for each member of a list that meets a test.
  kfKR_value, kfKFD_value, kfR16_value: the key form of a call of kind KR, KFD, R16.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a key form reads
the extension of the call's key vector.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKfAt
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Attention

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem keyKR_value (pc : PlaneClaim) :
    (keyKR pc).value ρ W =
      (W.slot pc.s0 + ρ.val (scaleNat (sumW pc.pw) 128)) +
        ρ.val (ofNat (2 ^ 20)) * (W.slot (pc.s0 + 1) + ρ.val (scaleNat (sumW pc.pw) 128)) +
        ρ.val (ofNat (2 ^ 40)) * W.slot (pc.s0 + 2) := by
  unfold keyKR
  simp only [Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst]

theorem keyKFD_value (d : ShD) (k : Score) :
    (keyKFD d k).value ρ W =
      W.slot (k.s0 + 5) - W.slot (k.s0 + 6) +
          ρ.val (if k.seg == Seg.fm then mulE (scaleNat (sumW k.pw) d.C) (onesOf k.zs)
            else mulE (scaleNat (sumW k.pw) d.Om) (subE oneE (leOf k.zj k.zi))) -
          (W.slot k.s0 + ρ.val (scaleNat (sumW k.pw) 128)) -
          ρ.val (ofNat 256) * (W.slot (k.s0 + 1) + ρ.val (scaleNat (sumW k.pw) 128)) +
        ρ.val (ofNat (2 ^ 32)) * W.slot (k.s0 + 2) +
        ρ.val (ofNat (2 ^ 33)) * (W.slot (k.s0 + 3) + ρ.val (scaleNat (sumW k.pw) 128) +
          ρ.val (ofNat 256) * W.slot (k.s0 + 4)) := by
  unfold keyKFD
  simp only [Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot, Aff.value_ofConst]

theorem remForm_value (d : Divide) :
    (remForm d).value ρ W =
      ρ.val (ofNat 2) * W.slot d.sACC + W.slot d.sZC - ρ.val (ofNat 2) * W.slot d.sZO := by
  unfold remForm
  simp only [Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot]

theorem indexForm_value (d : Divide) (lt : ℕ) :
    (indexForm d lt).value ρ W =
      ((List.range lt).map fun k => ρ.val (ofNat (2 ^ k)) * W.slot (d.sIB + k)).sum := by
  unfold indexForm
  have h : ∀ (l : List ℕ) (f : Aff),
      (l.foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (ofNat (2 ^ k))) f).value ρ W =
        f.value ρ W + (l.map fun k => ρ.val (ofNat (2 ^ k)) * W.slot (d.sIB + k)).sum := by
    intro l
    induction l with
    | nil => intro f; simp
    | cons k l ih =>
      intro f
      rw [List.foldl_cons, ih, Aff.value_addMul, Aff.value_slot, List.map_cons, List.sum_cons]
      ring
  rw [h, Aff.value_ofConst, ρ.zero, zero_add]

theorem keyWL_value (d : Divide) :
    (keyWL d).value ρ W =
      ρ.val (subE oneE d.zsl) * ((remForm d).value ρ W -
          ρ.val (ofNat 65536) * (W.slot d.sRH + ρ.val (scaleNat (sumW d.pwW) 128))) +
        ρ.val d.zsl * (ρ.val (ofNat 2) * W.slot d.sZC - ρ.val (sumW d.pwW) -
          (remForm d).value ρ W -
          ρ.val (ofNat 65536) * (W.slot d.sRHP + ρ.val (scaleNat (sumW d.pwW) 128))) := by
  unfold keyWL
  simp only [Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot, Aff.value_ofConst]

theorem keyIX_value (S : Shape) (d : Divide) :
    (keyIX S d).value ρ W =
      ρ.val (ofNat (2 ^ (16 - S.cf.lt))) *
        (ρ.val (mulE (sumW d.pwX) (idOf d.ziX)) - (indexForm d S.cf.lt).value ρ W) := by
  unfold keyIX
  simp only [Aff.value_sub, Aff.value_scale, Aff.value_ofConst]

theorem keyWH_value (d : Divide) :
    (keyWH d).value ρ W =
      (W.slot d.s5h + ρ.val (scaleNat (sumW d.pwH) 128)) +
        ρ.val (ofNat (2 ^ 20)) * (W.slot (d.s5h + 1) + ρ.val (scaleNat (sumW d.pwH) 128)) := by
  unfold keyWH
  simp only [Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst]

/-- A loop that adds a form for each member of a list that meets a test. -/
theorem foldIf_value {α : Type} (p : α → Bool) (f : α → Aff) : ∀ (l : List α) (v : Aff),
    (l.foldl (fun v x => if p x then v + f x else v) v).value ρ W =
      v.value ρ W + ((l.filter p).map fun x => (f x).value ρ W).sum
  | [], v => by simp
  | x :: l, v => by
    rw [List.foldl_cons, foldIf_value p f l]
    by_cases hp : p x = true
    · rw [if_pos hp, List.filter_cons_of_pos hp, List.map_cons, List.sum_cons, Aff.value_add]
      ring
    · rw [if_neg hp, List.filter_cons_of_neg hp]

theorem kfKR_value (h : Attention.Heard) (q : ℕ) :
    (kfKR h q).value ρ W =
      ((h.planes.toList.filter fun pc => pc.call == q).map fun pc => (keyKR pc).value ρ W).sum := by
  unfold kfKR
  rw [foldIf_value ρ W (fun pc => pc.call == q) keyKR, Aff.value_ofConst, ρ.zero, zero_add]

theorem kfKFD_value (h : Attention.Heard) (q : ℕ) (c : ACall) :
    (kfKFD h q c).value ρ W =
      ρ.val (scaleE (c.call.tauAt c.call.t0) (subE oneE (wall c (h.g.zk.getD q #[])))) +
        ((h.scores.toList.zipIdx.filter fun x => x.1.call == q).map fun x =>
          (keyKFD (h.S.shd c.sh) x.1).value ρ W).sum := by
  unfold kfKFD
  rw [foldIf_value ρ W (fun x : Score × ℕ => x.1.call == q) fun x => keyKFD (h.S.shd c.sh) x.1]
  unfold padTerm
  rw [Aff.value_ofConst]

theorem kfR16_value (h : Attention.Heard) (c : ACall) :
    (kfR16 h c).value ρ W =
      (if c.holds .wl then (keyWL h.d).value ρ W else 0) +
        (if c.holds .ix then (keyIX h.S h.d).value ρ W else 0) := by
  unfold kfR16
  by_cases h1 : c.holds .wl = true <;> by_cases h2 : c.holds .ix = true <;>
    simp [h1, h2, Aff.value_add, Aff.value_ofConst, ρ.zero]

end
end Fo
