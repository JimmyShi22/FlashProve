-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Shape.lean: the rounds of the plain sumcheck with n further scalars, against a
list of entries of a plan.

The block of Cb/Pv/Att/Ride.lean at the parameters of Cb/Pv/Att/Plain.lean has these rounds: a first
message of n + 1 scalars and a challenge from all of E; for each variable a message of as many
scalars as its degree and a challenge from all of E; for the further variable a message of DY
scalars and a challenge that is not 0; the values, one scalar for each map, and no challenge. This
file says so in the terms of OnBytes/G4/RoundIs.lean: ShapeIs E shape entries holds if the shape's
rounds send and draw, one by one, what the entries say in the three numbers msg, drawE and drawNZ.

Definitions. pscEntries w n degs DY vals: the entries of a masked sumcheck in closed form: "PSC
epsilon" with 24 (n + 1) bytes; "PSC round" with 24 d bytes for each d of degs; "PSC Y" with 24 DY
bytes and a challenge that is not 0; "PSC values" with 24 vals bytes. w is the work of a round;
ShapeIs does not read it, nor the names.

Statements. ride_shape: for every Y : PscPar whose formats are cube variables of the degrees deg
followed by the further variable of degree DY, the shape of the block is pscEntries. plain_shape: so
for every PlainSc. sc3_shape: for the sumcheck of products: nv rounds of 3 scalars, 2 for the
further variable, 2 nb values.

The statements hold for every finite field E; at Cb.Gl.E they are in the form that
OnBytes/G4/RoundIs.lean asks for. Limits. ShapeIs counts. It does not say which scalar of a message
is which, in which order further scalars and the sumcheck's own scalar stand, which coefficient a
round leaves out, or which variable a round binds. That pscEntries is what the port's planner writes
is stated in OnBytes/Tie/Pv/Att/PlanJoin.lean.
-/
import Cb.Pv.Att.Sc3
import OnBytes.G4.RoundIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att TWhole Johnson.L5.Layers OnBytes.G4

/-- The entries of a masked sumcheck with n further scalars in its first message. -/
def pscEntries (w n : ℕ) (degs : List ℕ) (DY vals : ℕ) : List Fmt.Entry :=
  [{ name := "PSC epsilon", work := w, msg := 24 * n + 24, drawE := 1 }] ++
    degs.map (fun d => { name := "PSC round", work := w, msg := 24 * d, drawE := 1 }) ++
    [{ name := "PSC Y", work := w, msg := 24 * DY, drawE := 1, drawNZ := 1 },
     { name := "PSC values", msg := 24 * vals }]

variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
/-- a challenge from all of E -/
theorem chal_all : Nonempty (E ≃ drawT E 1 0) := ⟨(Equiv.funUnique (Fin 1) E).symm⟩

theorem roundIs_first (n : ℕ) : RoundIs E (rRoundN E n) ⟨n + 1, 1, 0⟩ :=
  ⟨⟨(Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (n + 1) => E)⟩, chal_all,
    inferInstanceAs (IsEmpty Empty)⟩

theorem roundIs_cube (d : ℕ) : RoundIs E (Johnson.L5.Layers.sRound (pfCube E d)) ⟨d, 1, 0⟩ :=
  ⟨⟨Equiv.refl _⟩, chal_all, inferInstanceAs (IsEmpty Empty)⟩

theorem roundIs_dummy (D : ℕ) : RoundIs E (Johnson.L5.Layers.sRound (pDummy E D)) ⟨D, 1, 1⟩ :=
  ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty)⟩

omit [Fintype E] in
theorem roundIs_values (A : Type) [Fintype A] : RoundIs E (pRoundV E A) ⟨Fintype.card A, 0, 0⟩ :=
  ⟨⟨Equiv.arrowCongr (Fintype.equivFin A) (Equiv.refl E)⟩,
    ⟨({ toFun := fun _ i => i.elim0, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun _ => funext fun i => i.elim0 } : Unit ≃ (Fin 0 → E))⟩,
    inferInstanceAs (IsEmpty Empty)⟩

/-- the variables' rounds -/
theorem shape_cubes (w : ℕ) : ∀ (k : ℕ) (deg : Fin k → ℕ),
    ShapeIs E (sRounds (ldPartFmt E k deg))
      ((List.ofFn deg).map fun d => { name := "PSC round", work := w, msg := 24 * d, drawE := 1 })
  | 0, _ => List.Forall₂.nil
  | k + 1, deg => by
    rw [List.ofFn_succ]
    exact List.Forall₂.cons ⟨⟨deg 0, 1, 0⟩, roundIs_cube (deg 0), rfl, rfl, rfl⟩
      (shape_cubes w k fun i => deg i.succ)

/-- The shape of the block, for every general sumcheck over these formats. -/
theorem ride_shape (Y : PscPar E) [Fintype Y.A] (w n k : ℕ) (deg : Fin k → ℕ) (DY : ℕ)
    (hf : Y.fmt = ldPartFmt E k deg ++ [pDummy E DY]) :
    ShapeIs E (shapeRN Y n) (pscEntries w n (List.ofFn deg) DY (Fintype.card Y.A)) := by
  show List.Forall₂ (EntryIs E) (rRoundN E n :: (sRounds Y.fmt ++ [pRoundV E Y.A])) _
  rw [hf]
  show List.Forall₂ (EntryIs E)
    (rRoundN E n ::
      ((ldPartFmt E k deg ++ [pDummy E DY]).map Johnson.L5.Layers.sRound ++ [pRoundV E Y.A])) _
  rw [List.map_append]
  refine List.Forall₂.cons
    ⟨⟨n + 1, 1, 0⟩, roundIs_first n, by show 24 * n + 24 = 24 * (n + 1); ring, rfl, rfl⟩ ?_
  rw [List.append_assoc]
  refine List.rel_append (shape_cubes w k deg) ?_
  exact List.Forall₂.cons ⟨⟨DY, 1, 1⟩, roundIs_dummy DY, rfl, rfl, rfl⟩
    (List.Forall₂.cons ⟨⟨Fintype.card Y.A, 0, 0⟩, roundIs_values Y.A, rfl, rfl, rfl⟩
      List.Forall₂.nil)

/-- The plain sumcheck. -/
theorem plain_shape (T : PlainSc E) (w n : ℕ) :
    ShapeIs E (shapeRN T.our.par n) (pscEntries w n (List.ofFn T.deg) T.DY (Fintype.card T.A)) :=
  @ride_shape E _ _ T.our.par T.finA w n T.nv T.deg T.DY rfl

/-- The sumcheck of products. -/
theorem sc3_shape (T : Sc3 E) (w n : ℕ) :
    ShapeIs E (shapeRN T.plain.our.par n)
      (pscEntries w n (List.replicate T.nv 3) 2 (2 * T.nb)) := by
  have h := plain_shape T.plain w n
  have e1 : List.ofFn T.plain.deg = List.replicate T.nv 3 := List.ofFn_const T.nv 3
  have e2 : Fintype.card T.plain.A = 2 * T.nb := by
    show Fintype.card (Fin T.nb × Bool) = 2 * T.nb
    simp [Nat.mul_comm]
  rw [e1, e2] at h
  exact h

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.ride_shape
#print axioms OnBytes.Tie.Pv.Att.plain_shape
#print axioms OnBytes.Tie.Pv.Att.sc3_shape
