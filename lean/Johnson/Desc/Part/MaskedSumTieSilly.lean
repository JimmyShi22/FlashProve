-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumTieSilly.lean: THE TWO SILLY MEMBERS, AS LEAN. A rider: a statement is tried
against a part that says yes to all and one that says no to all: if either meets it, it is the wrong statement.
  HearLawOf aft   : PartHearLaw with any fold aft in the place of «after». HearLawOf after IS PartHearLaw (Iff.rfl).
  silly_fixed     : a fold that hands back one fixed element, whatever it hears, does NOT meet it.
  ReturnsOf hr    : PartReturns with any hearing hr in the place of «hear». ReturnsOf hear IS PartReturns (Iff.rfl).
  silly_never     : a hearing that never returns does NOT meet it. So PartReturns's premises can be met together.
NOT TRIED HERE: PartRowLaw against a silly row (its premises name a typed sumcheck's W, inc and S: a kind's file can meet them).

-/
import Johnson.Desc.Part.MaskedSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-- PartHearLaw with any fold in the place of «after». -/
def HearLawOf (aft : List Var → List (List E × E) → E → E) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (T : PlainSc K) (st : T.St) (t mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : T.A → K),
    (∀ i, 1 ≤ T.deg i) → rs.map (·.1.length) = List.ofFn T.deg → sentY.length = T.DY →
    (plainOut ρ T st t mu eps rs sentY beta hβ vals).fin =
      ρ.val (aft (varsOf (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) (addE mu (mulE eps t)))

theorem hearLawOf_after : HearLawOf after ↔ PartHearLaw := Iff.rfl

/-- The smallest plain sumcheck: no variable, degree 0 in Y, no map. -/
def tiny (K : Type) [Field K] [Fintype K] : PlainSc K where
  nv := 0
  deg := fun i => i.elim0
  A := Empty
  DY := 0
  St := Unit
  J := Unit
  map := fun _ _ a _ => a.elim
  S := fun _ _ _ => 0
  inc := fun _ _ => 0
  wAt := fun _ => ()
  cAt := fun a => a.elim

theorem tiny_after {K : Type} [CommRing K] (ρ : Reading K) (c : E) :
    ρ.val (after (varsOf [] 0) ([] ++ [([], oneE)]) c) = ρ.val c := by
  show ρ.val (addE (mulE zeroE oneE) (subE c (mulE zeroE (total [])))) = ρ.val c
  simp only [ρ.add, ρ.mul, ρ.sub, ρ.zero]
  ring

/-- **A fold that hands back one fixed element does not meet the law.** -/
theorem silly_fixed (x : E) : ¬ HearLawOf (fun _ _ _ => x) := by
  intro H
  have hβ : Reading.gl.val oneE ≠ 0 := by
    rw [Reading.gl.one]
    exact one_ne_zero
  have hl : ([] : List (List E × E)).map (·.1.length) = List.ofFn (tiny Cb.Gl.E).deg := by simp [tiny]
  have A : ∀ mu : E, Reading.gl.val x = Reading.gl.val (addE mu (mulE zeroE zeroE)) := by
    intro mu
    have a1 := H Cb.Gl.E Reading.gl (tiny Cb.Gl.E) () zeroE mu zeroE [] [] oneE hβ (fun a => a.elim)
      (fun i => i.elim0) hl rfl
    have a2 := partHearLaw Cb.Gl.E Reading.gl (tiny Cb.Gl.E) () zeroE mu zeroE [] [] oneE hβ (fun a => a.elim)
      (fun i => i.elim0) hl rfl
    rw [← hl] at a2
    exact (a1.symm.trans a2).trans (tiny_after Reading.gl _)
  have h0 := A zeroE
  have h1 := A oneE
  rw [h0] at h1
  simp only [Reading.gl.add, Reading.gl.mul, Reading.gl.zero, Reading.gl.one] at h1
  simp at h1

/-- PartReturns with any hearing in the place of «hear». -/
def ReturnsOf (hr : Aff → Call → Fork → List Fmt.RoundView → Option (Heard × Fork)) : Prop :=
  ∀ (C : Aff) (lead : Nat) (vs : List Var) (e : Ends) (F : Fork) (rs : List Fmt.RoundView),
    shapeOk ⟨lead, vs, some e⟩ = true → Fits (entries ⟨lead, vs, some e⟩) rs → (F.publicPart C).isSome →
    Free F (F.next + ownSlots (vs ++ [.point zeroE (e.dY + 1)])) e.n →
    (hr C ⟨lead, vs, some e⟩ F rs).isSome

theorem returnsOf_hear : ReturnsOf hear ↔ PartReturns := Iff.rfl

/-- A round of one scalar and k drawn elements, all 0. -/
def toyRound (k : Nat) : Fmt.RoundView := ⟨[.e (0, 0, 0)], ⟨List.replicate k (0, 0, 0), [], [], none⟩⟩

theorem toy_fit (name : String) (k nz : Nat) : Fit (entry name 1 k nz) (toyRound k) :=
  ⟨⟨[E.ofTriple (0, 0, 0)], rfl, rfl⟩, by simp [toyRound, entry]⟩

theorem toy_free : Free (({} : Fork).slots 3)
    ((({} : Fork).slots 3).next + ownSlots (([] : List Var) ++ [.point zeroE (1 + 1)])) 1 := by
  refine ⟨by simp [Fork.slots], by decide, ?_⟩
  intro j a b
  have a' : 2 ≤ j := a
  have b' : j < 3 := b
  have e : j = 2 := by omega
  subst e
  rfl

/-- **A hearing that never returns does not meet the law.** -/
theorem silly_never : ¬ ReturnsOf (fun _ _ _ _ => none) := by
  intro H
  have h := H {} 0 [] ⟨1, 1⟩ (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] rfl
    ⟨toy_fit _ 1 0, toy_fit _ 1 1, toy_fit _ 0 0, trivial⟩ rfl toy_free
  simp at h

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.silly_fixed
#print axioms VerifiableInference.Desc.Part.MaskedSum.silly_never
