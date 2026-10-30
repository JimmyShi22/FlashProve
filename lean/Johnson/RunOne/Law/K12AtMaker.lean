-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtMaker.lean: AT THE MAKER's OWN NUMBERS THE SHARED CHAIN's TWO PROXIMITY TESTS COUNT THEIR TREES FROM 0. Two statements with proofs: the maker's text, unfolded.
OBJECT. Key.testFirsts · Key.laterPlaces (Johnson/Desc/Key/Places.lean). USER. The premise hft of Johnson/RunOne/Law/K12FwdAt.lean's fwd_29_at | fwd_210_at (no test of the description asks it).
LETTERS. m Fs P: free. Premise: the maker's yes.
  firsts_zero: what the maker lays as the two places' first trees' numbers. later_zero: at the places' numbers.
Limits. Of the own test's place nothing is said here (there the maker lays the first chain's trees and one). Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Key.Places
import Johnson.Desc.K12.Law.FoldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12AtMaker
open OnBytes OnBytes.Params Johnson.G.OfPlan H2U
open VerifiableInference.Desc.Key
open H2K.FoldLaw (bind_ok)

theorem firsts_zero {m : Made} {Fs : TestFirsts} (h : testFirsts m = .ok Fs) : Fs.U.2 = 0 ∧ ∀ o, Fs.O = some o → o.2 = 0 := by
  unfold testFirsts at h
  dsimp only at h
  obtain ⟨t0, _, h⟩ := bind_ok h
  obtain ⟨t1, _, h⟩ := bind_ok h
  obtain ⟨t2, _, h⟩ := bind_ok h
  obtain ⟨u, _, h⟩ := bind_ok h
  obtain ⟨w, _, h⟩ := bind_ok h
  cases h
  refine ⟨rfl, fun o ho => ?_⟩
  dsimp only at ho
  split at ho
  · obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 ho
    rfl
  · cases ho

/-- **At the maker's numbers the shared chain's two tests count their trees from 0.** -/
theorem later_zero {m : Made} {P : LaterPlaces} (h : laterPlaces m = .ok P) : P.U.nums.firstTree = 0 ∧ ∀ nO, P.O = some nO → nO.nums.firstTree = 0 := by
  unfold laterPlaces at h
  dsimp only at h
  obtain ⟨Fs, hF, h⟩ := bind_ok h
  obtain ⟨tU, _, h⟩ := bind_ok h
  obtain ⟨tW, _, h⟩ := bind_ok h
  cases h
  obtain ⟨z1, z2⟩ := firsts_zero hF
  refine ⟨z1, fun nO hO => ?_⟩
  dsimp only at hO
  split at hO
  · rename_i tO fO _ e
    cases hO
    exact z2 fO e
  · cases hO

end Johnson.RunOne.Law.K12AtMaker

#print axioms Johnson.RunOne.Law.K12AtMaker.firsts_zero
#print axioms Johnson.RunOne.Law.K12AtMaker.later_zero
