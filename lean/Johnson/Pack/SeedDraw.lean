-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Pack/SeedDraw.lean: a sending whose family is made of public data (sigOf, seedsOf): its
joint seed, its answers and a stage's positions, as what the two rounds' entries count.

The condition SendLocFits (OnBytes/Tie/Pv/Switch/SendLocShape.lean) says of the joint seed, of the
answers and of the positions that "there is a bijection". Here each is made, with code, and its law
is stated.
Main names:
  eS   the joint seed as a draw: the coordinates, in their order, then the factor, which is not 0.
       eS_coord, eS_factor: its law, by rfl. The number of coordinates is bMax cs l.
  eA   the answers of all members: member i's one answer stands at i. eA_apply: by rfl. Each member
       has one answer by type: the sample map portZ has one sample, whatever the shape's own field
       says.
  ePs  a stage's positions are the numbers below 2 ^ a: the identity.
  member_place   a family that is not empty has a native position.
Limits: definitions and their laws alone. Nothing is said of how seeds are distributed, and nothing
of soundness.

-/
import Johnson.Pack.PortS
import OnBytes.G4.RoundIsAll
import OnBytes.Slice.Stage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb OnBytes.Slice OnBytes.G4

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

/-- The joint seed as a draw: the coordinates, then the factor. -/
noncomputable def eS : (seedsOf cs l).D ≃ DrawSet GE (1 * bMax cs l) 1 0 0 0 where
  toFun x := (fun i => x.1 (Fin.cast (Nat.one_mul _) i), fun _ => ⟨x.2.val, x.2.ne_zero⟩,
    fun i => i.elim0, fun i => i.elim0)
  invFun d := (fun i => d.1 (Fin.cast (Nat.one_mul _).symm i), Units.mk0 (d.2.1 0).1 (d.2.1 0).2)
  left_inv x := by
    refine Prod.ext (funext fun i => ?_) (Units.ext ?_)
    · rfl
    · rfl
  right_inv d := by
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_)
      (Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0)))
    · rfl
    · exact Subtype.ext (by rw [Subsingleton.elim j 0]; rfl)

/-- The law of eS: coordinate i of the draw is coordinate i of the seed. -/
theorem eS_coord (z : Fin (bMax cs l) → GE) (β : GEˣ) (i : Fin (1 * bMax cs l)) :
    (eS cs l (z, β)).1 i = z (Fin.cast (Nat.one_mul _) i) := rfl

/-- The law of eS: the one element that is not 0 is the seed's factor. -/
theorem eS_factor (z : Fin (bMax cs l) → GE) (β : GEˣ) (j : Fin 1) :
    ((eS cs l (z, β)).2.1 j).1 = β.val := rfl

/-- The answers of all members: member i's one answer at i. -/
noncomputable def eA : (sigOf cs l).Answ ≃ (Fin l.length → GE) where
  toFun f := fun i => f i ()
  invFun g := fun i _ => g i
  left_inv _ := rfl
  right_inv _ := rfl

theorem eA_apply (f : (sigOf cs l).Answ) (i : Fin l.length) : eA cs l f i = f i () := rfl

/-- A stage's positions. -/
def ePs (s : Sg) : s.Ps ≃ Fin (2 ^ s.C.a) := Equiv.refl _

/-- A member has a native position. -/
theorem member_place (hl : l ≠ []) : Nonempty (Σ a, ((sigOf cs l).om a).C.NP) :=
  ⟨⟨⟨0, List.length_pos_iff.2 hl⟩, Sum.inr ⟨0, Nat.two_pow_pos _⟩⟩⟩

end Johnson.Pack

#print axioms Johnson.Pack.eS
#print axioms Johnson.Pack.eA
#print axioms Johnson.Pack.member_place
