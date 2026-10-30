-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/TestSc3.lean: tests of the sumcheck of products (Cb/Pv/Att/Sc3.lean) and of the files
under it.

 1. The axioms that the statements rest on are printed.
 2. The walk of Cb/G6/WalkCmd.lean: no premise's type of the four statements on knowledge soundness
    reaches an honest prover or the exact relation of a joint. The walk looks at premises alone,
    never at a conclusion.
 3. A closed toy over the integers modulo 97: one variable, one pair of maps, four entries that the
    maps read and eight that serve as masks. A_0 reads the entries 0 and 1 as its values at the two
    corners, B_0 the entries 2 and 3; the weight is 1. toy_holds: at the entries (2, 3, 5, 7) and
    masks 0 the sum claim with the target 2 · 5 + 3 · 7 = 31 holds. toy_fails: after one entry of
    the witness is turned (7 to 8) it fails. in_holds, in_fails: the same of the relaxed relation of
    the block's input joint (rideNIn) without further scalars, where the joint that is carried along
    and the caller's condition are always true. So after one entry of the witness is turned the
    input's relation fails while all that rides holds: it is not hollow at the toy. Not tried: the
    output claims; an incoming form other than 0; masks other than 0; further scalars; a weight
    other than 1; more than one pair.

-/
import Cb.Pv.Att.Sc3
import Cb.G6.WalkCmd
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

#print axioms Cb.Pv.Att.rideN_doomed
#print axioms Cb.Pv.Att.rideN_knowAt
#print axioms Cb.Pv.Att.rideN_nums
#print axioms Cb.Pv.Att.plain_knowAt
#print axioms Cb.Pv.Att.plain_nums
#print axioms Cb.Pv.Att.plain_sum
#print axioms Cb.Pv.Att.plain_fix
#print axioms Cb.Pv.Att.sc3_ok
#print axioms Cb.Pv.Att.sc3_knowAt
#print axioms Cb.Pv.Att.sc3_know
#print axioms Cb.Pv.Att.sc3_nums
#print axioms Cb.Pv.Att.sc3_sum
#print axioms Cb.Pv.Att.sc3_fix

#tw_premises Cb.Pv.Att.rideN_knowAt clean
#tw_premises Cb.Pv.Att.plain_knowAt clean
#tw_premises Cb.Pv.Att.sc3_knowAt clean
#tw_premises Cb.Pv.Att.sc3_know clean

namespace Cb.Pv.Att.TestSc3
open Iop Prob Cb TWhole

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
abbrev K := ZMod 97

/-- the value at x of the map with the values p, q at the corners 0, 1 -/
def lin1 (p q x : K) : K := (1 - x) * p + x * q

theorem deg_lin1 (p q : K) : Alg.DegLE (fun _ : Fin 1 => 1) fun x : Fin 1 → K => lin1 p q (x 0) :=
  (((Alg.DegLE.const _ 1).sub (Alg.DegLE.coord 0)).mul_const p).add
    ((Alg.DegLE.coord 0).mul_const q)

/-- The toy. The entries: Sum.inl i, i < 4: what the maps read; Sum.inr: masks. -/
noncomputable def toy : Sc3 K where
  nv := 1
  nb := 1
  St := Unit
  J := Fin 4 ⊕ (PIdx (ldPartFmt K 1 (fun _ => 3) ++ [pDummy K 2]) ⊕ (Fin 1 × Bool))
  finJ := by
    have : Fintype (PIdx (ldPartFmt K 1 (fun _ => 3) ++ [pDummy K 2])) :=
      inferInstanceAs (Fintype (Fin 3 ⊕ (Fin 2 ⊕ Unit)))
    infer_instance
  W := fun _ _ _ => 1
  map := fun _ m a x =>
    if a.2 = false then lin1 (m (.inl 0)) (m (.inl 1)) (x 0)
    else lin1 (m (.inl 2)) (m (.inl 3)) (x 0)
  inc := fun _ _ => 0
  wAt := fun i => .inr (.inl i)
  cAt := fun a => .inr (.inr a)
  degW := fun _ _ => Alg.DegLE.const _ 1
  degM := fun _ m a => by
    by_cases ha : a.2 = false
    · simpa [ha] using deg_lin1 (m (.inl 0)) (m (.inl 1))
    · simpa [ha] using deg_lin1 (m (.inl 2)) (m (.inl 3))

/-- the entries: (2, 3, 5, z), masks 0 -/
def ent (z : K) : toy.J → K
  | .inl i => ![2, 3, 5, z] i
  | .inr _ => 0

theorem toy_sum (z t : K) : toy.plain.our.par.SumHolds (t, ()) (ent z) ↔ 10 + 3 * z = t := by
  rw [sc3_sum]
  have h0 : ∑ j, toy.inc () j * ent z j = 0 := Finset.sum_eq_zero fun j _ => zero_mul _
  have h1 : ∀ f : (Fin 1 → Bool) → K, ∑ c, f c = f (fun _ => true) + f (fun _ => false) :=
    fun f => by
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
    rfl
  show ∑ c : Fin 1 → Bool, ∑ b : Fin 1, toy.W () b (Alg.corner c) *
      toy.map () (ent z) (b, false) (Alg.corner c) * toy.map () (ent z) (b, true) (Alg.corner c) +
    ∑ j, toy.inc () j * ent z j = t ↔ _
  rw [h0, h1, add_zero]
  simp only [Fin.sum_univ_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    simp [toy, lin1, ent, Alg.corner]
    ring
  · rw [← h]
    simp [toy, lin1, ent, Alg.corner]
    ring

theorem toy_holds : toy.plain.our.par.SumHolds (31, ()) (ent 7) := (toy_sum 7 31).2 (by decide)
theorem toy_fails : ¬ toy.plain.our.par.SumHolds (31, ()) (ent 8) := fun h =>
  absurd ((toy_sum 8 31).1 h) (by decide)

/-- the joint that is always true -/
def top : IOR.Rels Unit Unit extNone ((toy.J → K) × Unit) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

/-- the block's input joint: no further scalar; the claim's target is 31; the messages are the
witness's first part -/
noncomputable def inJ : IOR.Rels Unit Unit extNone ((toy.J → K) × Unit) :=
  rideNIn toy.plain.our.par 0 (fun _ _ => ((31 : K), ())) extNone top (fun m => m) fun _ _ _ => True

theorem in_holds : inJ.relR ((), ()) (ent 7, ()) :=
  ⟨trivial, fun i => i.elim0, trivial, toy_holds⟩
theorem in_fails : ¬ inJ.relR ((), ()) (ent 8, ()) := fun h => by
  obtain ⟨_, _, _, hs⟩ := h
  exact toy_fails hs

end Cb.Pv.Att.TestSc3

#print axioms Cb.Pv.Att.TestSc3.toy_holds
#print axioms Cb.Pv.Att.TestSc3.toy_fails
#print axioms Cb.Pv.Att.TestSc3.in_holds
#print axioms Cb.Pv.Att.TestSc3.in_fails
