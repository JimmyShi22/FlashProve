-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15Y.lean: FOUR CLAUSES THAT THE COMPOSITION OF THE PROXIMITY TEST's LAW ASKS OF THE GROUP (GroupFacts, Johnson/Desc/Sound/SeamMembers.lean: the facts on codes at the first radius · every row that the batching takes lies on the group's tables · the layout's k and h), AT THE RANGES' TEST's SEAT, FROM THE SEAT's OWN YES AND TWO TESTS ON THE PLAN. One statement with its proof: calls alone. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. rangesTest laid back N at any state and any type of claims. USER. Whoever lays GroupFacts at the key file's first proximity test.
LETTERS. All free. Premises: the test below the Johnson radius says yes at the radii r · the seat's test on the plan says yes · the seat's decision says yes at s · t is the test's own state that the seat makes of s · what that state fixes.

  record_is: the state that the seat enters the test with is the one at which the kind's decision runs.
  four_of_yes: the statement.
BY: the seat's yes taken apart (Johnson/RunOne/Law/RngAsked.lean: decide_ok) · the kind's block is the same at every type of claims (RngAnyCl.lean: same_k12) · ONE CALL of yes_facts (Johnson/Desc/K12/Coin/YesFacts.lean).
Limits. It closes no row. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Coin.YesFacts
import Johnson.RunOne.Law.PlanPays

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

/-- The state that the seat enters the test with is the one that it makes of the chain's state, where what it asks of it is met. -/
theorem record_is {s : σ} {t t0 : T12} (ht : enterAndAsk laid (rangesParams N) s = .ok t)
    (h1 : rangesRecord laid s = .ok t0) (h2 : asksOnRecord (rangesParams N) t0 = .ok ()) : t = t0 := by
  have e : enterAndAsk laid (rangesParams N) s = .ok t0 := by
    unfold enterAndAsk
    rw [h1]
    show (asksOnRecord (rangesParams N) t0).map (fun _ => t0) = .ok t0
    rw [h2]
    rfl
  exact Except.ok.inj (ht.symm.trans e)

/-- **The four clauses on the group, from the seat's own yes.** -/
theorem four_of_yes (r : Fmt.M1.Stage → ℕ) (joh : johOk (rangesParams N) r = true)
    (hp : (rangesTest laid back N : Block σ Cl).planOk = true) {s s' : σ} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rangesTest laid back N : Block σ Cl).decide s rs gs = .ok s')
    {t : T12} (ht : enterAndAsk laid (rangesParams N) s = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes (rangesParams N) t a rest G0 Ly D) :
    (sgOf a).StageJ (r (sgOf a).st) ∧
      combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
      Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h := by
  obtain ⟨t0, tE, h1, h2, h3, _⟩ := RngAsked.decide_ok h
  obtain rfl := record_is ht h1 h2
  have hd : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide t rs gs = .ok tE := by
    rw [(RngAnyCl.same_k12 (A := Unit) (B := Cl) guardedProximityTestParts (rangesParams N)).decide]
    exact h3
  exact yes_facts (rangesParams N) r (fun s => r s.st) (fun _ => rfl) joh (PlanPays.rng_pays hp).1
    (PlanPays.rng_pays hp).2.2.1 t tE rs gs hd a rest G0 Ly D hf

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.record_is
#print axioms Johnson.RunOne.Law.K12Facts15.four_of_yes
