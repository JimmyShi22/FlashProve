-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFewToy.lean: `FallGood` HAS A MEMBER, AND `batFall_few` BITES: at
the made-up segment of Honest/K9/Toy.lean: the real type of states `First.S`, K9's own batching, the frame's
own gatherer (`claimsInBy`). Statements and proofs. No goal is stated.

  `gathered_toy`   at every x the draw and the gatherer return: the ledger in front of the adding holds
                   x, is empty and has two coefficients; the claims are the toy's two
  `good`           **all premises of `batFall_few` hold together at the toy's state**: n = 2, no merge,
                   d = 1, the polynomials 1 and X - 1
  `count_le`       so at most 2 elements of the field are readings of a chi at which K9's share speaks
  `count_pos`      and at least one is: chi = 1
A TOY. NOT SHOWN: a claim that hangs on x; a challenge at which the gatherer refuses; a merge; a claim
under a higher power. Nothing on a segment of the protocol. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFew
import Johnson.Desc.ProofFile.Honest.K9.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace ProofFile.Honest.K9.Toy
open Polynomial
open OnBytes OnBytes.Model
open VerifiableInference.Desc (claimsInBy Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (batch mergeOf atS drawAlone drawnClean drawn ledgerEmpty)
open VerifiableInference.Desc.K9L (expo)
open VerifiableInference.Desc.K9H (SlotsGood slotCoef slotPoly unitAt)

abbrev GE : Type := Cb.Gl.E
abbrev ρ : Reading GE := Reading.gl

/-- The frame's own gatherer at the toy's segment. -/
def gat : S → Except String (List Claim × S) := claimsInBy lk.each lk.hear lk.order

/-- The member at the batching's place is K9's batching at that gatherer. -/
theorem at2 : at_ 2 = batch atS pw gat := rfl

/-- The ledger in front of the adding, where x is drawn. -/
def Fx (x : E) : Fork :=
  { t2FillL (FD held) LD.list with
    theta := x, thetaDrawnF := true, kapMapF := Array.replicate 2 false }

/-- K9's part of the toy's state in front of the draw. -/
def part0 : VerifiableInference.Desc.K9.Part :=
  { owed := none, used := 2, laid := some 0, L := LD, F := FD held,
    d := { st := stD, book := (sD held).book, roots := (sD held).roots, opened := [], loc := () } }

theorem clean_toy (x : E) : drawnClean 2 x none 2 LD (FD held) =
    .ok ⟨some 2, { LD with list := { LD.list with used := 2 }, handed := true }, Fx x⟩ := by
  have hE : ledgerEmpty (FD held) = true := by decide +kernel
  have hd : drawn 2 x none 2 LD (FD held) =
      .ok ⟨some 2, { LD with list := { LD.list with used := 2 }, handed := true }, Fx x⟩ := rfl
  unfold drawnClean
  rw [hd, hE]
  rfl

theorem gathered_toy (x : E) :
    (gathered pw gat (sD held) x).map (fun y => (y.2.1.F, y.2.2, mergeOf y.1)) =
      some (Fx x, [cl0, cl1], none) := by
  have h1 : (drawAlone (Cl := Claim) atS pw).decide (sD held) [⟨[], drawnOne x⟩] [] =
      (drawnClean 2 x none 2 LD (FD held)).bind fun o =>
        .ok (atS.set (sD held) { part0 with owed := o.owed, L := o.L, F := o.F }) := rfl
  unfold gathered
  rw [h1, clean_toy]
  rfl

theorem ledger_toy (x : E) : ((gathered pw gat (sD held) x).map (·.2.1.F)).getD {} = Fx x := by
  have h := gathered_toy x
  cases hq : gathered pw gat (sD held) x with
  | none => rw [hq] at h; exact nomatch h
  | some y => rw [hq] at h; exact congrArg (·.1) (Option.some.inj h)

theorem claims_toy (x : E) : ((gathered pw gat (sD held) x).map (·.2.2)).getD [] = [cl0, cl1] := by
  have h := gathered_toy x
  cases hq : gathered pw gat (sD held) x with
  | none => rw [hq] at h; exact nomatch h
  | some y => rw [hq] at h; exact congrArg (·.2.1) (Option.some.inj h)

theorem slots0 : cl0.form.slots.toList = [(0, oneE), (1, mulE oneE (subE zeroE oneE))] := rfl
theorem slots1 : cl1.form.slots.toList = [(1, oneE)] := rfl

theorem c00 : slotCoef ρ cl0 0 = 1 := by
  simp [slotCoef, slots0, slotValue, unitAt, Reading.gl.one]
theorem c01 : slotCoef ρ cl0 1 = -1 := by
  simp [slotCoef, slots0, slotValue, unitAt, Reading.gl.one, Reading.gl.zero, Reading.gl.sub,
    Reading.gl.mul]
theorem c10 : slotCoef ρ cl1 0 = 0 := by
  simp [slotCoef, slots1, slotValue, unitAt]
theorem c11 : slotCoef ρ cl1 1 = 1 := by
  simp [slotCoef, slots1, slotValue, unitAt, Reading.gl.one]

/-- The two polynomials: the claims' own. -/
noncomputable def P (j : Nat) : GE[X] := slotPoly ρ 2 0 [cl0, cl1] j

theorem P0 : P 0 = monomial 0 1 := by
  show monomial (expo 2 0 cl0) (slotCoef ρ cl0 0) + (monomial (expo 2 1 cl1) (slotCoef ρ cl1 0) + 0)
    = _
  rw [c00, c10, map_zero, add_zero, add_zero]
  rfl

theorem P1 : P 1 = monomial 0 (-1) + monomial 1 1 := by
  show monomial (expo 2 0 cl0) (slotCoef ρ cl0 1) + (monomial (expo 2 1 cl1) (slotCoef ρ cl1 1) + 0)
    = _
  rw [c01, c11, add_zero]
  rfl

theorem live0 : P 0 ≠ 0 ∧ (P 0).natDegree ≤ 1 := by
  rw [P0]
  exact ⟨by simp, le_trans (natDegree_monomial_le _) (Nat.zero_le _)⟩

theorem live1 : P 1 ≠ 0 ∧ (P 1).natDegree ≤ 1 := by
  rw [P1]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 : (monomial 0 (-1 : GE) + monomial 1 1).coeff 1 = 0 := by rw [h]; rfl
    rw [coeff_add, coeff_monomial, coeff_monomial] at h1
    simp at h1
  · exact le_trans (natDegree_add_le _ _)
      (max_le (le_trans (natDegree_monomial_le _) (Nat.zero_le _)) (natDegree_monomial_le _))

theorem emptyX (x : E) (j : Nat) : (Fx x).LS.getD j zeroE = zeroE := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- **A member**: all premises of `batFall_few` together, at the toy's state. -/
theorem good : FallGood pw gat (sD held) 2 none 1 P where
  slots :=
    { chi := fun x _ => by rw [ledger_toy]; rfl
      sized := fun x _ => by rw [ledger_toy]; rfl
      empty := fun x _ j => by rw [ledger_toy]; exact emptyX x j
      fixed := fun x _ _ _ _ => by rw [ledger_toy, claims_toy]; rfl
      live := fun j hj _ => by
        match j, hj with
        | 0, _ => exact live0
        | 1, _ => exact live1
      unnamed := fun _ _ _ _ h => nomatch h }
  merge := fun x y hy => by
    have h := gathered_toy x
    rw [hy] at h
    exact congrArg (·.2.2) (Option.some.inj h)

/-- The set that `batFall_few` counts, at the toy's state. -/
def Speaks (y : GE) : Prop :=
  ∃ x : E, ρ.val x = y ∧
    (batFallTest (batch atS pw gat) 2 (fun _ _ => none) (fun _ => none) (sD held)
      [drawnOne x]).isSome = true

theorem count_le : Prob.cnt Speaks ≤ 2 * 1 := batFall_few pw gat (sD held) 2 none 1 P good

theorem speaks_at_one :
    (batFallTest (batch atS pw gat) 2 (fun _ _ => none) (fun _ => none) (sD held)
      [drawnOne oneE]).isSome = true := by decide +kernel

/-- **It bites**: the counted set is not empty. -/
theorem count_pos : 0 < Prob.cnt Speaks := by
  haveI : Nonempty {y : GE // Speaks y} := ⟨⟨ρ.val oneE, oneE, rfl, speaks_at_one⟩⟩
  exact Nat.card_pos

end ProofFile.Honest.K9.Toy

#print axioms ProofFile.Honest.K9.Toy.at2
#print axioms ProofFile.Honest.K9.Toy.gathered_toy
#print axioms ProofFile.Honest.K9.Toy.good
#print axioms ProofFile.Honest.K9.Toy.count_le
#print axioms ProofFile.Honest.K9.Toy.speaks_at_one
#print axioms ProofFile.Honest.K9.Toy.count_pos
#print axioms ProofFile.Honest.K9.Toy.GE
#print axioms ProofFile.Honest.K9.Toy.ρ
#print axioms ProofFile.Honest.K9.Toy.gat
#print axioms ProofFile.Honest.K9.Toy.Fx
#print axioms ProofFile.Honest.K9.Toy.part0
#print axioms ProofFile.Honest.K9.Toy.clean_toy
#print axioms ProofFile.Honest.K9.Toy.ledger_toy
#print axioms ProofFile.Honest.K9.Toy.claims_toy
#print axioms ProofFile.Honest.K9.Toy.slots0
#print axioms ProofFile.Honest.K9.Toy.slots1
#print axioms ProofFile.Honest.K9.Toy.c00
#print axioms ProofFile.Honest.K9.Toy.c01
#print axioms ProofFile.Honest.K9.Toy.c10
#print axioms ProofFile.Honest.K9.Toy.c11
#print axioms ProofFile.Honest.K9.Toy.P
#print axioms ProofFile.Honest.K9.Toy.P0
#print axioms ProofFile.Honest.K9.Toy.P1
#print axioms ProofFile.Honest.K9.Toy.live0
#print axioms ProofFile.Honest.K9.Toy.live1
#print axioms ProofFile.Honest.K9.Toy.emptyX
#print axioms ProofFile.Honest.K9.Toy.Speaks
