-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotKindFirst.lean: a term for the letter `kind₁` of the key file's first thread (`LaterFill.kind₁`, E2E/FirstHFill.lean) at
the three members where the thread's clause `keeps` IS that letter: 4 and 10 (the two lookups' own sub-protocols) and 15 (the
ranges' proximity test).

  `kindFirst`: THE TERM: 4 | 10: the lookups' `AtPublicFiles.Lookup.Key.LookupKeeps` (∃ heard ledger, s' = lookupSeat.put s heard ledger) ·
    15: IOP's `RngYes Xs N` (the test's own step says yes from s to s') · elsewhere True.
  `kindFirst_four`, `kindFirst_ten`, `kindFirst_fifteen`: the three arms, by unfolding.
  `kind_of_yes`, `kept_of_kind`: AT 15, THE TWO IMPLICATIONS that part 5's law at the side asks of the kind: the step's yes gives
    it; it gives that the sampled messages stay (`SmpStay`) and the lookups' record is kept.
  `LotKindFirst`: AT 4 AND 10, THE TEST OF THE TERM: at every Q whose kind₁ is `LookupKeeps` there: at `Th` (E2E/FirstHSeat.lean), at
    every letter Said: BehindS and RidesPastS. `LotKindFirstLaid`: the same at { Q with kind₁ := kindFirst Xs N }.

WHERE. `LookupKeeps`, `lookupBehindAtTheKey`, `lookupRidesPastAtTheKey`:
E2E/Lookup/Key/LookupBehindAndRidesPastAtTheKey.lean · `RngYes`, `rng_keeps`:
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesRides.lean. Here: the term and calls. THE DEBTS AT 15
ARE NOT HERE; that the term serves them is not shown here.

WHICH ARMS ARE EVER READ. `keeps` is `eq₁ … kind₁` (E2E/KeyKeepsEq.lean), which has its own text at 2, 3, 5 to 9, 11 to 14 and 18;
`fillH` lays kind₁ itself at 0, 1, 16, 17. So Q.kind₁ b is read at 4, 10, 15, and at b ≥ 19, where the chain has no member and
`OwesS` asks nothing. The last arm is read by no debt.

Limits.
- A PROPOSAL FOR A LETTER OF A STRUCTURE OF ANOTHER FILE: nothing here lays it into `fillH`.
- `ThrS` in front, the premise inside each debt, is met by nothing here. PlaysS, ExchangeS, AcceptedS at 4, 10 are not here.
- RngYes is NOT shown to give `StaysK` (`OlderStay`: shape, mark and sample rows at EVERY older message).
- The written sizes alone: in scope, at a sourced description.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotLetters
import E2E.FirstHSeat
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesRides
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows1 (ReadsL)
open AtPublicFiles.KeyThread (one₀)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.Lookup.Key (LookupKeeps lookupBehindAtTheKey lookupRidesPastAtTheKey)
open ProofFile.Honest.K12.AtKey (RngYes rng_keeps)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

theorem kindFirst_four (Xs : Source) (N : H2U.PlaceNums) : kindFirst Xs N 4 = LookupKeeps := rfl
theorem kindFirst_ten (Xs : Source) (N : H2U.PlaceNums) : kindFirst Xs N 10 = LookupKeeps := rfl
theorem kindFirst_fifteen (Xs : Source) (N : H2U.PlaceNums) : kindFirst Xs N 15 = RngYes Xs N := rfl

/-- **At 15 the step's own yes gives the kind.** -/
theorem kind_of_yes {Xs : Source} {N : H2U.PlaceNums} {s s' : FirstState} (h : RngYes Xs N s s') :
    kindFirst Xs N 15 s s' := h

/-- **At 15 the kind keeps the sampled messages and the lookups' record.** -/
theorem kept_of_kind {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) {s s' : FirstState} (h : kindFirst Xs N 15 s s') :
    VerifiableInference.Desc.K1.SmpStay s.d.st s'.d.st ∧ s'.base = s.base :=
  rng_keeps hs h

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **The test of the term at 4 and 10**, at every Q whose letter has the value there. -/
def LotKindFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true →
    Q.kind₁ 4 = LookupKeeps → Q.kind₁ 10 = LookupKeeps →
    ∀ (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop), ∀ b ∈ [4, 10],
      BehindS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b

/-- **The same at the term.** -/
def LotKindFirstLaid : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true →
    ∀ (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop), ∀ b ∈ [4, 10],
      BehindS (Th Xs N Pl K f { Q with kind₁ := kindFirst Xs N } w₀ rc x) Said b ∧
        RidesPastS (Th Xs N Pl K f { Q with kind₁ := kindFirst Xs N } w₀ rc x) Said b

theorem lotKindFirst : LotKindFirst Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope h4 h10 Said b hb
  have hG : ReadsL (fillH Xs N Pl K f Q x).base.h₁ :=
    Johnson.RunOne.KeyRows1.readsL_h₁ (baseH (one₀ Xs)) fun _ _ _ _ => rfl
  exact ⟨lookupBehindAtTheKey Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope ⟨h4, h10⟩ Said b hb,
    lookupRidesPastAtTheKey Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hG ⟨h4, h10⟩ Said b hb⟩

theorem lotKindFirstLaid : LotKindFirstLaid Xs N Pl K f Q w₀ rc x := fun hs scope Said =>
  lotKindFirst Xs N Pl K f { Q with kind₁ := kindFirst Xs N } w₀ rc x hs scope rfl rfl Said

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.kindFirst_four
#print axioms AtPublicFiles.FirstH.Lots.kindFirst_ten
#print axioms AtPublicFiles.FirstH.Lots.kindFirst_fifteen
#print axioms AtPublicFiles.FirstH.Lots.kind_of_yes
#print axioms AtPublicFiles.FirstH.Lots.kept_of_kind
#print axioms AtPublicFiles.FirstH.Lots.lotKindFirst
#print axioms AtPublicFiles.FirstH.Lots.lotKindFirstLaid
