-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Step18Ends.lean: the maps of step 18 (Cb/Pv/Att/Step18.lean) at a point are the scalars
that the library's own description names KC and IBP.

Behind the block of step 18 stand claims on the values of its maps at the point of the challenges
(`scd_val`, Cb/Pv/Att/ScdProofs.lean). The description names these values itself, in another form
(Inst/Model/Att/KeyForms.lean): `AttSeg.rvKC`, a contraction of the keys with three equality
vectors, and `AttSeg.rvIBP`, a contraction of a bit of the index with two. This file proves that the
two forms agree, at every point.

Main names:
  `ext_two`: an extension in a + b variables of a vector that is read at (X / 2 ^ b, X % 2 ^ b) is a
    double sum under two equality vectors.
  `step18_KC`: the map KC_l of `step18` at z is `AttSeg.rvKC` at the point `Blocks.nat z`.
  `step18_IB`: the map IB_(b,t) of `step18` at z is `AttSeg.rvIBP` at that point.
  `step18_val`: so the claim on an end value behind the block is: the description's scalar at the
    point of the challenges, plus the map's own mask entry times the challenge of the further
    variable, is the end value.

Limits: as in Cb/Pv/Att/Step18.lean. In that file rd, which says how the cells' content is read off
the entries, is a parameter as free as the incoming form and the places of the mask entries.
-/
import Cb.Pv.Att.Step18
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Inst.Model Finset

section Ext
variable {E : Type} [Field E]

theorem ext_two (a b : ℕ) (u : ℕ → ℕ → E) (pt : ℕ → E) :
    Blocks.ext (a + b) (fun X => u (X / 2 ^ b) (X % 2 ^ b)) pt =
      ∑ g ∈ range (2 ^ a), ∑ j ∈ range (2 ^ b),
        Blocks.eqN a 0 pt g * Blocks.eqN b a pt j * u g j := by
  unfold Blocks.ext
  rw [pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun g _ => sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ b := mem_range.1 hj
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  have e1 : (g * 2 ^ b + j) / 2 ^ b = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hj', Nat.zero_add]
  have e2 : (g * 2 ^ b + j) % 2 ^ b = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
  rw [Blocks.eqN_append' a b 0 pt g hj', Nat.zero_add]
  simp only [e1, e2]

/-- An equality vector reads its own coordinates of the point alone. -/
theorem eqN_read (m off off' : ℕ) (x y : ℕ → E) (h : ∀ t < m, x (off + t) = y (off' + t)) (z : ℕ) :
    Blocks.eqN m off x z = Blocks.eqN m off' y z := by
  rw [Blocks.eqN_eq, Blocks.eqN_eq]
  congr 1
  funext t
  exact h t.1 t.2

end Ext

variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) {J : Type} [Fintype J]
  (rd : (J → E) → AttSeg.Raw → E) (inc : AttSeg.Pub E → J → E)
  (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J)
  (cAt : (size18 D).A → J)

theorem step18_KC (p : AttSeg.Pub E) (m : J → E) (l : Fin (size18 D).Lam)
    (z : Fin (size18 D).k → E) :
    (step18 D rd inc wAt cAt).map p m (.inl l) z = AttSeg.rvKC D p (rd m) (Blocks.nat z) l.1 := by
  show Blocks.ext (D.lg + D.lT) (AttSeg.kc D p (rd m) l.1)
    (AttSeg.cat D.lg (AttSeg.sh (Blocks.nat z) D.lT) (Blocks.nat z)) = _
  have e : AttSeg.kc D p (rd m) l.1 = fun X =>
      AttSeg.conN D p.fn fun n => AttSeg.keyV (rd m) l.1 (X / 2 ^ D.lT) (X % 2 ^ D.lT) n := by
    funext X
    unfold AttSeg.kc
    rw [D.T_eq]
  rw [e, ext_two D.lg D.lT fun g j => AttSeg.conN D p.fn fun n => AttSeg.keyV (rd m) l.1 g j n]
  unfold AttSeg.rvKC AttSeg.rd3 AttSeg.eqT AttSeg.conN AttSeg.Dim.nG
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun j _ => ?_
  rw [eqN_read D.lg 0 0 _ (AttSeg.sh (Blocks.nat z) D.lT) (fun t ht => by
      simp [AttSeg.cat, ht]) g,
    eqN_read D.lT D.lg 0 _ (Blocks.nat z) (fun t _ => by simp [AttSeg.cat]) j, mul_sum]
  exact sum_congr rfl fun n _ => by ring

theorem step18_IB (p : AttSeg.Pub E) (m : J → E) (b : Fin (size18 D).pairs)
    (t : Fin (size18 D).lt) (z : Fin (size18 D).k → E) :
    (step18 D rd inc wAt cAt).map p m (.inr (b, t)) z =
      AttSeg.rvIBP D (rd m) (Blocks.nat z) b.1 t.1 := by
  show Blocks.ext (D.lg + D.lT) (fun X => AttSeg.ibV (rd m) t.1 b.1 (X / D.T) (X % D.T))
    (AttSeg.sh (Blocks.nat z) D.lT) = _
  rw [D.T_eq, ext_two D.lg D.lT (fun g i => AttSeg.ibV (rd m) t.1 b.1 g i)]
  unfold AttSeg.rvIBP AttSeg.rd2 AttSeg.eqT AttSeg.Dim.nG
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [eqN_read D.lT D.lg 0 (AttSeg.sh (Blocks.nat z) D.lT)
    (AttSeg.sh (Blocks.nat z) (D.lT + D.lg)) (fun t _ => by
      simp [AttSeg.sh, Nat.add_assoc]) i]

/-- the description's scalar for an end value, at a point -/
def rv18 (p : AttSeg.Pub E) (t : AttSeg.Raw → E) (pt : ℕ → E) : (size18 D).A → E
  | .inl l => AttSeg.rvKC D p t pt l.1
  | .inr x => AttSeg.rvIBP D t pt x.1.1 x.2.1

/-- The claim on an end value behind the block of step 18. -/
theorem step18_val (o : (step18 D rd inc wAt cAt).plain.our.par.Out) (m : J → E)
    (a : (size18 D).A) :
    (step18 D rd inc wAt cAt).plain.our.par.EHolds o m a ↔
      rv18 D o.st (rd m)
          (Blocks.nat
            (ldPartIni (size18 D).k (size18 D).deg (pDummy E ((size18 D).lt + 1)) o.pt)) a +
        m (cAt a) * ldPartLast (size18 D).k (size18 D).deg (pDummy E ((size18 D).lt + 1)) o.pt =
      o.vals a := by
  rw [scd_val]
  cases a with
  | inl l => rw [step18_KC]; rfl
  | inr x => obtain ⟨b, t⟩ := x; rw [step18_IB]; rfl

end Cb.Pv.Att

#print axioms Cb.Pv.Att.step18_KC
#print axioms Cb.Pv.Att.step18_IB
#print axioms Cb.Pv.Att.step18_val
