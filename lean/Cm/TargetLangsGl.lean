-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetLangsGl.lean: a code's side and a placing over p = 2^64 - 2^32 + 1, for a configuration
whose model is the integer model of Cm/ (`targetGlP`, Cm/TargetPLangs.lean).

Definitions, statements and proofs.
Why: `Spec.target_p_props` takes a code's side Cf₀ with its conditions and a placing of the
3,076,096 · 2^18 entries of an index at different places of the layout. If there were no such pair,
the statement would range over nothing. That there is one: `target_gl_place` and
`targetGlRoom_code` state parts of this at these values; no theorem of this library states the
premises of `target_p_props` together.
In `targetGlP` the type of instances and the index set are large, and the relation reads
both: what no toy configuration has.

Main names:
  `targetGlRoom`: a code's side with room, and no proposal: the toy code of Cb/GlVal/GlToyBase.lean
    (Reed-Solomon on the subgroup of order 8, dimension 3: one message symbol, two symbols of
    randomness, distance 6), 2^40 rows, one entry a row, which is the layout; no pad, no sample,
    radius of decoding 1. Its own model is trivial and is thrown away.
  `targetGlPl`: entry (y, c) of the index stands in the row whose 40 bits write the number
    y · 2^18 + c.
  `Spec.target_gl_place`: different entries stand at different places.
  `targetGl_char`: 256 ≤ `Gl.p`.

Limits: what the head of Cm/TargetLangs.lean lists as not said is not said here either. The code's
side is a toy: rate 1/8, one entry a row; 2^40 rows; radius 1, below half the distance 6; hides two
positions; sample: `Sample.nil`. It is not the technical report's format (rows that take blocks of
columns), and no sub-protocol is given over this configuration: no object, no request. All indices
in the guards of Cm/TargetPLangs.lean are made up (Cm/RelTrue.lean).
Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.GlVal.GlToyConf
import Cb.Obj.LdObjectProofs
import Cm.TargetLangsProofs
import Cm.Rel2Guards
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Blocks Cb Cb.Ood
open Inst.Model.Layout (kRef hRef)

/-- A code's side with room for the index. -/
def targetGlRoom : LdCf Gl.F Gl.E where
  C₀ := Gl.C8
  hp := (by norm_num : (1 : ℕ) ≤ 2 + 1)
  v := 40
  J₀ := Unit
  Pd := Empty
  Lay := Unit
  lay := fun _ => ()
  plE := Gl.plE8
  Z := Sample.nil Gl.E (Unit ⊕ Empty)
  eM := 1
  rank := fun _ => 0
  I := Unit
  Xm := Unit
  Cells := Unit
  Ryes := fun _ _ _ => True
  Rno := fun _ _ _ => True
  trace := fun _ _ => ()
  cells0 := ()
  body := fun _ _ => 0
  heldB := fun _ => some ()

/-- the number of an entry -/
def targetGlNum (q : TargetEnt) : ℕ := q.1.val * 262144 + q.2.val

/-- the row of an entry: the 40 bits of its number -/
def targetGlPl : TargetEnt → targetGlRoom.Row × targetGlRoom.Lay := fun q =>
  (fun t => (targetGlNum q).testBit t.val, ())

/-- the last position of a prompt -/
def targetLast : Fin ppref.T := ⟨1023, by decide⟩

namespace Spec

def target_gl_place : Prop := Function.Injective (targetAt targetGlRoom targetGlPl)

end Spec

/-- two numbers below 2^40 with the same 40 bits are equal -/
theorem targetBits_inj (a b : ℕ) (ha : a < 2 ^ 40) (hb : b < 2 ^ 40)
    (h : ∀ t : Fin 40, a.testBit t.val = b.testBit t.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 40
  · exact h ⟨j, hj⟩
  · have hle : 2 ^ 40 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hj)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem targetGlNum_lt (q : TargetEnt) : targetGlNum q < 2 ^ 40 := by
  have a1 : q.1.val < 3076096 := q.1.isLt
  have a2 : q.2.val < 2 ^ 18 := q.2.isLt
  unfold targetGlNum
  norm_num at a2 ⊢
  omega

theorem targetGlNum_inj : Function.Injective targetGlNum := by
  intro q q' h
  have a2 : q.2.val < 2 ^ 18 := q.2.isLt
  have b2 : q'.2.val < 2 ^ 18 := q'.2.isLt
  unfold targetGlNum at h
  norm_num at a2 b2
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem target_gl_place : Spec.target_gl_place := by
  intro q q' h
  have h1 : (fun t : Fin 40 => (targetGlNum q).testBit t.val) =
      fun t : Fin 40 => (targetGlNum q').testBit t.val :=
    congrArg Prod.fst h
  exact targetGlNum_inj
    (targetBits_inj _ _ (targetGlNum_lt q) (targetGlNum_lt q') fun t => congrFun h1 t)

theorem targetGlRoom_code : targetGlRoom.CodeOK 1 :=
  ⟨Gl.core8,
    (by norm_num : 1 < 6),
    ldCm_list_unique Gl.F Gl.E targetGlRoom Gl.dist8 (by norm_num : 2 * 1 < 6),
    Gl.smp8 Gl.ToyMo8.all⟩

theorem targetGl_char : 256 ≤ Gl.p := by
  show 256 ≤ Code.pGold
  rw [Code.pGold_eq]
  norm_num

end Cm
