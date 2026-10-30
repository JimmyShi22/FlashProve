-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RidersG.lean: TWO PUBLIC ITEMS ARE RIDERS AT THE FIRST SEGMENT's OPENING
(`RiderG`, Johnson/Desc/K13/Law/FillGFromSentences.lean): "K13.weightsOk" and "K13.oneRow".
Statements with their proofs.
  `openingZero_noRows`: behind a yes of that block, where no row was pending in front, no row lies
  on the table.
  `riderG_weights`: "K13.weightsOk": the test runs over the rows on the table: of no row it holds.
  It spends "none sent" in front (no row is pending there).
  `riderG_oneRow`: "K13.oneRow": behind the block the chain stands inside the first segment, not at
  its end: there the item says nothing (`oneRowC_of_stand`, PileWithin.lean). It spends nothing in
  front.
What is not claimed. What Mg says at the items (premises). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillGFromSentences
import Johnson.Desc.K13.Law.PileWithin
import Johnson.Desc.K13.Law.FillM3Paid
import Johnson.Desc.First.Pend.WeightsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)

section
variable {Pp W Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
  {fvs : List Bool} {kCol : ℕ}

/-- Behind the opening, where no row was pending in front, no row lies on the table. -/
theorem openingZero_noRows {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : s.out.pending.isEmpty = true) : t.rows = [] := by
  obtain ⟨hstand, _, _, _, _, ho, _⟩ := K1.openingZero_rec h
  have hp : t.out.pending = [] := by
    rw [ho]
    exact List.isEmpty_iff.1 h0
  unfold S.rows
  cases hh : t.here with
  | mem a => simp [First.standOf, hh] at hstand
  | _ => exact hp

variable {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub} {p : Option Place}

/-- "K13.weightsOk" is a rider at the first segment's opening. -/
theorem riderG_weights (hm : Pub.noneSent ∈ Q) (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hP : ∀ x, Mg.pubP weightsItem x) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p weightsItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hNS, noneSentC_eq, Bool.and_eq_true] at h0
  refine ⟨?_, fun _ => hP x'⟩
  rw [hW]
  unfold First.weightsB
  rw [openingZero_noRows hd h0.2]
  rfl

/-- "K13.oneRow" is a rider at the first segment's opening. -/
theorem riderG_oneRow (hM : ∀ x, Mg.pub oneRowItem x = oneRowC x.2)
    (hP : ∀ x, Mg.pubP oneRowItem x) : RiderG Cl q gp nm X fvs kCol N Mg Q p oneRowItem :=
  fun x x' h _ _ => by
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    refine ⟨?_, fun _ => hP x'⟩
    rw [hM]
    refine oneRowC_of_stand ?_
    rw [(K1.openingZero_rec hd).1]
    exact fun e => nomatch e

end

end VerifiableInference.Desc.K13.Law
