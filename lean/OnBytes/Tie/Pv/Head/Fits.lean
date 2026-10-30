-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Head/Fits.lean: when a round of a typed protocol fits an entry of a plan, and that
the rounds of a masked sumcheck with short messages fit the planner's entries for a sumcheck.

A round of a typed protocol (Iop.Round) is made of types: what the prover sends in the clear, what
it sends as an oracle, what the verifier draws. An entry of a plan (Fmt.Entry) is a name and eleven
numbers. Fits E r e says, of the round r and the entry e:
  the entry's bytes are 24 times a number k, and the round's plain part is k elements of E;
  the round's draws are drawE elements of E, or, if drawE = drawNZ = 1, one element other than 0;
  the round has no oracle position;
  the entry counts one round, and no root, sample answer, position or matrix entry.
It does not read the entry's name, its work, its rows or logN.

Statements. fits_draw, fits_bat, fits_point: a round in which the verifier alone speaks.
fits_scalars: a round in which n scalars are sent and one element is drawn. fits_eps,
fits_epsRide, fits_round, fits_y, fits_vals: the rounds of a sumcheck. fits_psc, fits_pscRide: all
rounds of the short sumcheck (shapeS) and of the short sumcheck with its target riding in round 0
(shapeR), for parameters with g cube variables of degree 2 and the further variable, against the
closed list lPsc of the planner's entries.

Under: nothing assumed, but for the two equations on the parameters that fits_psc names.

Not claimed. That lists of rounds agree says nothing on start forms, on the order of the variables,
on which coefficient is left out or on the order of the scalars inside a message.

-/
import Cb.G6.Johnson.Layers.Ride
import Cb.Part.LdPartVars
import Ior.Draw
import OnBytes.Tie.Pv.Lay.PlanList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Head
open Iop Prob Cb Johnson.L5.Layers
open OnBytes.Tie.Pv.Lay (eDraw eBat lPsc)

/-- The set C of draws is dE elements of E, or one element other than 0. -/
def DrawIs (E : Type) [Zero E] (C : Type) (dE dNZ : ℕ) : Prop :=
  (dNZ = 0 ∧ Nonempty (C ≃ (Fin dE → E))) ∨
    (dE = 1 ∧ dNZ = 1 ∧ Nonempty (C ≃ {x : E // x ≠ 0}))

/-- The round r fits the entry e. -/
structure Fits (E : Type) [Zero E] (r : Round) (e : Fmt.Entry) : Prop where
  plain : ∃ k, e.msg = 24 * k ∧ Nonempty (r.Plain ≃ (Fin k → E))
  draw : DrawIs E r.Chal e.drawE e.drawNZ
  noPos : IsEmpty r.Pos
  one : e.count = 1
  none : e.roots = 0 ∧ e.answers = 0 ∧ e.poss = 0 ∧ e.trits = 0

section
variable {E : Type}

/-- no element, as a function on the empty set -/
def unitEquiv : Unit ≃ (Fin 0 → E) :=
  ⟨fun _ i => i.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim0⟩

variable [Field E] [Fintype E]

omit [Fintype E] in
theorem draw_one : DrawIs E E 1 0 := Or.inl ⟨rfl, ⟨(Equiv.funUnique (Fin 1) E).symm⟩⟩
omit [Fintype E] in
theorem draw_none : DrawIs E Unit 0 0 := Or.inl ⟨rfl, ⟨unitEquiv⟩⟩
omit [Fintype E] in
theorem draw_nz : DrawIs E {x : E // x ≠ 0} 1 1 := Or.inr ⟨rfl, rfl, ⟨Equiv.refl _⟩⟩
omit [Fintype E] in
theorem draw_pt (n : ℕ) : DrawIs E (Fin n → E) n 0 := Or.inl ⟨rfl, ⟨Equiv.refl _⟩⟩

/-- the verifier draws one element; nothing is sent -/
theorem fits_draw (name : String) (w : ℕ) : Fits E (IOR.drawRound E) (eDraw name w 0 1) :=
  ⟨⟨0, rfl, ⟨unitEquiv⟩⟩, draw_one, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

theorem fits_bat (w rows : ℕ) : Fits E (IOR.drawRound E) (eBat w 0 rows) :=
  ⟨⟨0, rfl, ⟨unitEquiv⟩⟩, draw_one, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

/-- the verifier draws a point of n coordinates; nothing is sent -/
theorem fits_point (name : String) (w n : ℕ) :
    Fits E (IOR.drawRound (Fin n → E)) (eDraw name w 0 n) :=
  ⟨⟨0, rfl, ⟨unitEquiv⟩⟩, draw_pt n, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype E] in
/-- n scalars are sent, then the element is drawn that batches rows -/
theorem fits_scalars (r : Round) (w n rows : ℕ) (hP : r.Plain = (Fin n → E)) (hC : r.Chal = E)
    (hE : IsEmpty r.Pos) : Fits E r (eBat w (24 * n) rows) :=
  ⟨⟨n, rfl, ⟨Equiv.cast hP⟩⟩,
    Or.inl ⟨rfl, ⟨(Equiv.cast hC).trans (Equiv.funUnique (Fin 1) E).symm⟩⟩,
    hE, rfl, rfl, rfl, rfl, rfl⟩

theorem fits_eps (w : ℕ) : Fits E (pRound0 E) (eDraw "PSC epsilon" w (0 + 24) 1) :=
  ⟨⟨1, rfl, ⟨(Equiv.funUnique (Fin 1) E).symm⟩⟩, draw_one, inferInstanceAs (IsEmpty Empty), rfl,
    rfl, rfl, rfl, rfl⟩

theorem fits_epsRide (w : ℕ) : Fits E (rRound0 E) (eDraw "PSC epsilon" w (24 + 24) 1) :=
  ⟨⟨2, rfl, ⟨(finTwoArrowEquiv E).symm⟩⟩, draw_one, inferInstanceAs (IsEmpty Empty), rfl,
    rfl, rfl, rfl, rfl⟩

theorem fits_round (w : ℕ) : Fits E (sRound (pfCube E 2)) (eDraw "PSC round" w 48 1) :=
  ⟨⟨2, rfl, ⟨Equiv.refl _⟩⟩, draw_one, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

theorem fits_y (w dy : ℕ) : Fits E (sRound (pDummy E dy))
    { name := "PSC Y", work := w, msg := 24 * dy, drawE := 1, drawNZ := 1 } :=
  ⟨⟨dy, rfl, ⟨Equiv.refl _⟩⟩, draw_nz, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype E] in
theorem fits_vals (A : Type) [Fintype A] (vals : ℕ) (h : Fintype.card A = vals) :
    Fits E (pRoundV E A) { name := "PSC values", msg := 24 * vals } := by
  subst h
  exact ⟨⟨_, rfl, ⟨Equiv.arrowCongr (Fintype.equivFin A) (Equiv.refl E)⟩⟩, draw_none,
    inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl⟩

theorem fits_rounds (w : ℕ) : ∀ (g : ℕ) (t : Shape) (lt : List Fmt.Entry),
    List.Forall₂ (Fits E) t lt →
    List.Forall₂ (Fits E) (sRounds (ldPartFmt E g fun _ => 2) ++ t)
      (List.replicate g (eDraw "PSC round" w 48 1) ++ lt)
  | 0, _, _, h => h
  | g + 1, t, lt, h => List.Forall₂.cons (fits_round w) (fits_rounds w g t lt h)

theorem lPsc_eq (w b n dy vals : ℕ) :
    lPsc w b n dy vals = eDraw "PSC epsilon" w (b + 24) 1 ::
      (List.replicate n (eDraw "PSC round" w 48 1) ++
        [{ name := "PSC Y", work := w, msg := 24 * dy, drawE := 1, drawNZ := 1 },
          { name := "PSC values", msg := 24 * vals }]) := by
  simp [lPsc]

/-- the rounds behind round 0 -/
theorem fits_tail (Y : PscPar E) (w g dy vals : ℕ)
    (hf : Y.fmt = ldPartFmt E g (fun _ => 2) ++ [pDummy E dy]) (hA : Fintype.card Y.A = vals) :
    List.Forall₂ (Fits E) (sRounds Y.fmt ++ [pRoundV E Y.A])
      (List.replicate g (eDraw "PSC round" w 48 1) ++
        [{ name := "PSC Y", work := w, msg := 24 * dy, drawE := 1, drawNZ := 1 },
          { name := "PSC values", msg := 24 * vals }]) := by
  rw [hf]
  have e : sRounds (ldPartFmt E g (fun _ => 2) ++ [pDummy E dy]) ++ [pRoundV E Y.A] =
      sRounds (ldPartFmt E g fun _ => 2) ++ [sRound (pDummy E dy), pRoundV E Y.A] := by
    simp [sRounds]
  rw [e]
  exact fits_rounds w g _ _ (List.Forall₂.cons (fits_y w dy)
    (List.Forall₂.cons (fits_vals Y.A vals hA) List.Forall₂.nil))

/-- The short sumcheck's rounds fit the planner's entries for a sumcheck. -/
theorem fits_psc (Y : PscPar E) (w g dy vals : ℕ)
    (hf : Y.fmt = ldPartFmt E g (fun _ => 2) ++ [pDummy E dy]) (hA : Fintype.card Y.A = vals) :
    List.Forall₂ (Fits E) (shapeS Y) (lPsc w 0 g dy vals) := by
  rw [lPsc_eq]
  exact List.Forall₂.cons (fits_eps w) (fits_tail Y w g dy vals hf hA)

/-- The same with the target riding in round 0. -/
theorem fits_pscRide (Y : PscPar E) (w g dy vals : ℕ)
    (hf : Y.fmt = ldPartFmt E g (fun _ => 2) ++ [pDummy E dy]) (hA : Fintype.card Y.A = vals) :
    List.Forall₂ (Fits E) (shapeR Y) (lPsc w 24 g dy vals) := by
  rw [lPsc_eq]
  exact List.Forall₂.cons (fits_epsRide w) (fits_tail Y w g dy vals hf hA)

end

end OnBytes.Tie.Pv.Head

#print axioms OnBytes.Tie.Pv.Head.fits_psc
#print axioms OnBytes.Tie.Pv.Head.fits_pscRide
