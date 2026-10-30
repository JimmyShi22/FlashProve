-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15G.lean: SIX OF THE SEVEN CLAUSES THAT THE COMPOSITION OF THE PROXIMITY TEST's LAW ASKS OF THE GROUP (GroupFacts, Johnson/Desc/Sound/SeamMembers.lean: its second to its seventh, in their order), AT THE RANGES' TEST's SEAT, FROM THE SEAT's OWN YES AND TWO TESTS ON THE PLAN. Statements with proofs: calls alone. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. rangesTest laid back N at any state and any type of claims. USER. Whoever lays GroupFacts at the key file's first proximity test.
LETTERS. As Johnson/RunOne/Law/K12Facts15Y.lean's.

  kind_yes: the seat's yes holds a yes of the kind's own decision, at the state that the seat enters the test with.
  six_of_yes: the statement: four_of_yes (K12Facts15Y.lean) and found_of_decide (Johnson/Desc/K12/Coin/CoreAtYes.lean).
Limits. The first clause (the codes) is not here. It closes no row. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15Y
import Johnson.Desc.K12.Coin.CoreAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Key
open H2K.Pub (sgOf johOk)
open H2K.First (Plain)

variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}

/-- The seat's yes holds a yes of the kind's own decision. -/
theorem kind_yes {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rangesTest laid back N : Block σ Cl).decide s rs gs = .ok s') {t : T12}
    (ht : enterAndAsk laid (rangesParams N) s = .ok t) :
    ∃ tE, (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide t rs gs = .ok tE := by
  obtain ⟨t0, tE, h1, h2, h3, _⟩ := RngAsked.decide_ok h
  obtain rfl := record_is ht h1 h2
  refine ⟨tE, ?_⟩
  rw [(RngAnyCl.same_k12 (A := Unit) (B := Cl) guardedProximityTestParts (rangesParams N)).decide]
  exact h3

/-- **Six clauses on the group, from the seat's own yes.** -/
theorem six_of_yes (r : Fmt.M1.Stage → ℕ) (joh : johOk (rangesParams N) r = true)
    (hp : (rangesTest laid back N : Block σ Cl).planOk = true) {s s' : σ} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rangesTest laid back N : Block σ Cl).decide s rs gs = .ok s')
    {t : T12} (ht : enterAndAsk laid (rangesParams N) s = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes (rangesParams N) t a rest G0 Ly D) :
    (sgOf a).StageJ (r (sgOf a).st) ∧
      combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
      Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
      (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  obtain ⟨h1, h2, h3, h4⟩ := four_of_yes r joh hp h ht a rest G0 Ly D hf
  obtain ⟨tE, hd⟩ := kind_yes h ht
  obtain ⟨h5, h6⟩ := found_of_decide (rangesParams N) t tE rs gs hd a rest G0 Ly D hf
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.kind_yes
#print axioms Johnson.RunOne.Law.K12Facts15.six_of_yes
