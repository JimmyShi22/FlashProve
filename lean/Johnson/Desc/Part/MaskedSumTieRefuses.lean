--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumTieRefuses.lean: THE REFUSING HALF OF THE HEARING, AS A NAMED STATEMENT, AND THREE MORE SILLY MEMBERS, NONE OF THEM A NAMED TEXT.
WHY. None of PartHearLaw, PartRowLaw, PartReturns (Johnson/Desc/Part/MaskedSumLaw.lean) has «hear» left of an arrow. So a
hearing that lets rounds through which do not fit, and then folds as the text does, meets all three.
  PartRefuses     : where «hear» returns at a call with ends: the plan's tests have passed; THE ROUNDS ARE THE CALL's ENTRIES,
                    entry for entry; the start form's public part is there; what each round holds; every field of the record;
                    what is written to the ledger.
  partRefuses     : it holds: from MaskedSumShape.lean's hear_spec, readAll_spec, readAll_fits.
  RefusesOf hr    : the same with any hearing hr in the text's place. RefusesOf hear IS PartRefuses (Iff.rfl).
  silly_yes       : a hearing that says yes to all and hands back one fixed pair does NOT meet it.
  returns_is_not_refuses : there is a hearing that meets PartReturns's form and does NOT meet this one: it drops the rounds
                    behind the call's entries unseen and then hears as the text does.
  silly_deaf      : a fold that hears no round at all (it hands back the claim that it was given) does NOT meet PartHearLaw's
                    form, at a call with no variable but Y and degree 1 in Y: a shape that the text takes.
ONE DIRECTION: from a return. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumTieSilly
import Johnson.Desc.Part.MaskedSumTieMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-- The refusing half, with any hearing in the place of «hear». -/
def RefusesOf (hr : Aff → Call → Fork → List Fmt.RoundView → Option (Heard × Fork)) : Prop :=
  ∀ (C : Aff) (lead : Nat) (vs : List Var) (e : Ends) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard),
    hr C ⟨lead, vs, some e⟩ F rs = some (h, G) →
    shapeOk ⟨lead, vs, some e⟩ = true ∧ Fits (entries ⟨lead, vs, some e⟩) rs ∧
    ∃ (T : E) (R : Read) (r0 : Fmt.RoundView) (used : List Fmt.RoundView) (rv : Fmt.RoundView) (front : List E),
      F.publicPart C = some T ∧
      rs = r0 :: (used ++ [rv]) ∧ Sent r0 (lead + 1) 1 (front ++ [R.mu]) [R.eps] ∧ front.length = lead ∧
      VarsRead (vs ++ [.point zeroE (e.dY + 1)]) used R.rounds ∧ Sent rv e.n 0 R.values [] ∧
      h = { start := C, target := T, eps := R.eps,
            claim := after (Call.all ⟨lead, vs, some e⟩) R.rounds (addE R.mu (mulE R.eps T)),
            first := F.next, vars := Call.all ⟨lead, vs, some e⟩, r := R.rounds.map (·.2),
            sEnd := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) } ∧
      ({ F with next := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + R.values.length } : Fork).hideRun
        (F.next + ownSlots (Call.all ⟨lead, vs, some e⟩)) R.values.toArray
        ((R.rounds.map (·.2)).getLastD zeroE) = some G

/-- **Where the hearing returns.** -/
def PartRefuses : Prop := RefusesOf hear

theorem partRefuses : PartRefuses := by
  intro C lead vs e F G rs h hh
  obtain ⟨hs, T, R, hT, hR, he, hG⟩ := hear_spec hh
  obtain ⟨r0, used, rv, front, a1, a2, a3, a4, a5⟩ := readAll_spec hR
  exact ⟨hs, readAll_fits hR, T, R, r0, used, rv, front, hT, a1, a2, a3, a4, a5, he, hG⟩

/-- **A hearing that says yes to all does not meet it.** -/
theorem silly_yes (x : Heard × Fork) : ¬ RefusesOf (fun _ _ _ _ => some x) := by
  intro H
  exact (H {} 0 [] ⟨1, 1⟩ {} x.2 [] x.1 rfl).2.1.elim

theorem toy_returns : (hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 3)
    [toyRound 1, toyRound 1, toyRound 0]).isSome :=
  partReturns {} 0 [] ⟨1, 1⟩ (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] rfl
    ⟨toy_fit _ 1 0, toy_fit _ 1 1, toy_fit _ 0 0, trivial⟩ rfl toy_free

/-- **Returning is not refusing.** A hearing that drops the rounds behind the call's entries unseen, and then hears as the text
does, returns wherever the text returns, and does not meet the refusing half. -/
theorem returns_is_not_refuses : ∃ hr, ReturnsOf hr ∧ ¬ RefusesOf hr := by
  refine ⟨fun C k F rs => hear C k F (rs.take (entries k).length), ?_, ?_⟩
  · intro C lead vs e F rs hs hfit hpub hfree
    have hl : rs.take (entries ⟨lead, vs, some e⟩).length = rs := by
      rw [← Fits.length hfit]
      exact List.take_length
    show (hear C ⟨lead, vs, some e⟩ F (rs.take (entries ⟨lead, vs, some e⟩).length)).isSome
    rw [hl]
    exact partReturns C lead vs e F rs hs hfit hpub hfree
  · intro H
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 toy_returns
    have h := (H {} 0 [] ⟨1, 1⟩ (({} : Fork).slots 3) y.2 [toyRound 1, toyRound 1, toyRound 0, toyRound 0] y.1 hy).2.1
    exact absurd (Fits.length h) (by simp [entries])

theorem one_after {K : Type} [CommRing K] (ρ : Reading K) (c : E) :
    ρ.val (after (varsOf [] 1) ([] ++ [([oneE], oneE)]) c) = 1 + ρ.val c := by
  show ρ.val (addE (mulE (addE (mulE zeroE oneE) oneE) oneE) (subE c (mulE zeroE (total [oneE])))) = _
  simp only [ρ.add, ρ.mul, ρ.sub, ρ.zero, ρ.one]
  ring

/-- **A fold that hears no round does not meet PartHearLaw's form.** -/
theorem silly_deaf : ¬ HearLawOf (fun _ _ c => c) := by
  intro H
  have hβ : Reading.gl.val oneE ≠ 0 := by
    rw [Reading.gl.one]
    exact one_ne_zero
  have hl : ([] : List (List E × E)).map (·.1.length) =
      List.ofFn (flat Cb.Gl.E 0 (fun i => i.elim0) 1).deg := by simp [flat]
  have a1 := H Cb.Gl.E Reading.gl (flat Cb.Gl.E 0 (fun i => i.elim0) 1) () zeroE zeroE zeroE [] [oneE] oneE hβ
    (fun a => a.elim) (fun i => i.elim0) hl rfl
  have a2 := partHearLaw Cb.Gl.E Reading.gl (flat Cb.Gl.E 0 (fun i => i.elim0) 1) () zeroE zeroE zeroE [] [oneE] oneE hβ
    (fun a => a.elim) (fun i => i.elim0) hl rfl
  rw [← hl] at a2
  have e : Reading.gl.val (addE zeroE (mulE zeroE zeroE)) = 1 + Reading.gl.val (addE zeroE (mulE zeroE zeroE)) :=
    (a1.symm.trans a2).trans (one_after Reading.gl _)
  have z : (1 : Cb.Gl.E) = 0 := by linear_combination (-1 : Cb.Gl.E) * e
  exact one_ne_zero z

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.partRefuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.silly_yes
#print axioms VerifiableInference.Desc.Part.MaskedSum.returns_is_not_refuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.silly_deaf
