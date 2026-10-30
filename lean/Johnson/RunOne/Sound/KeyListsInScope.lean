-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyListsInScope.lean: THE KEY
FILE's DESCRIPTION's THREE WHOLE LISTS OF ROUNDS AS CLOSED NUMERALS, IN SCOPE: the join of
`desc_rounds` (Johnson/RunOne/Sound/KeyListsAtFK.lean: at every X N P the lists are the tables',
functions of the source) with the source's equations in scope
(Johnson/RunOne/Law/KeyInScope.lean: `five_in_scope`, `shared_lin_in_scope`) and an evaluation of
the tables at the written value `keyFull` by the kernel.

What is said.
  `L₁`, `L₂`, `L₃`: three written lists of 19, 12 and 4 numbers.
  `first_full`, `shared_full`, `second_full`: the tables' numbers of rounds at `keyFull`'s ranges
    and shape are these lists: by evaluation in the kernel. `first_full_no`, `shared_full_no`: two
    controls: with one numeral turned the equation is refuted.
  `rounds_in_scope`: in scope, at an X that reads the parameter file, at any digest: where the maker
    and the source return and the tests on the plan and `wantedOk` say yes:
    `(Key.descriptionFromSource X N P).first | shared | second.blocksInOrder.map (·.rounds.length) = L₁ | L₂ | L₃`.
  `laid_rounds_in_scope`: the same from the yes of `publicOfO o` and then `Key.keyDataAndDecisionAtFixedDigest`, at every
    o.

Limits. Numbers of rounds, in order; not the rounds; what a block at a place does no list says.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Sound

open OnBytes VerifiableInference.Desc
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

/-- The first chain's blocks' numbers of rounds, at the full size. -/
def L₁ : List ℕ := [2, 2, 0, 0, 9581, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1]

/-- The shared chain's. -/
def L₂ : List ℕ := [0, 1, 2, 0, 1, 2, 0, 1, 1, 35, 24, 1]

/-- The last chain's. -/
def L₃ : List ℕ := [0, 0, 30, 0]

/-- The first chain's table reads the one-time chain's ranges and shape alone. -/
theorem wantedFirst_congr (one one' : Params.OneTime) (hr : one.ranges = one'.ranges)
    (hl : one.lin = one'.lin) : Key.wantedFirst one = Key.wantedFirst one' := by
  unfold Key.wantedFirst
  rw [hr, hl]

/-- **The first chain's table at the written value**: by evaluation in the kernel. -/
theorem first_full (one : Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) : (Key.wantedFirst one).map (·.2) = L₁ := by
  unfold Key.wantedFirst
  rw [hr, hl]
  decide +kernel

/-- The shared chain's. -/
theorem shared_full : (Key.wantedShared keyFull.once.shape).map (·.2) = L₂ := by
  decide +kernel

/-- The last chain's. -/
theorem second_full : (Key.wantedSecond keyFull.once.shape).map (·.2) = L₃ := by
  decide +kernel

/-- A control: with one numeral turned the first equation is refuted. -/
theorem first_full_no (one : Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) : (Key.wantedFirst one).map (·.2) ≠
      [2, 2, 0, 0, 9582, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1] := by
  unfold Key.wantedFirst
  rw [hr, hl]
  decide +kernel

/-- A control: the same of the second. -/
theorem shared_full_no : (Key.wantedShared keyFull.once.shape).map (·.2) ≠
    [0, 1, 2, 0, 1, 2, 0, 1, 1, 35, 25, 1] := by
  decide +kernel

/-- **The three whole lists as closed numerals, in scope, at any digest.** -/
theorem rounds_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums}
    {P : Key.LaterPlaces} (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hw : (Key.descriptionFromSource X N P).wantedOk = true) :
    (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = L₁ ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder.map (·.rounds.length) = L₂ ∧
      (Key.descriptionFromSource X N P).second.blocksInOrder.map (·.rounds.length) = L₃ := by
  obtain ⟨h₁, h₂, h₃⟩ := desc_rounds X N P hp hw
  obtain ⟨-, hr, hl, -, -⟩ := five_in_scope hZ hP hm hX hp
  have hs := shared_lin_in_scope hZ hP hm hX hp
  refine ⟨h₁.trans (first_full _ hr hl), ?_, ?_⟩
  · rw [h₂, hs]
    exact shared_full
  · rw [h₃, hs]
    exact second_full

/-- **The same from the yes of the two in a row**, at every o. -/
theorem laid_rounds_in_scope {o : Nat → ByteArray → ByteArray} {Zp : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Zp = true) {D : Maker.WholeD} {r : Key.KeyRun}
    (h : ((VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z =>
      Key.keyDataAndDecisionAtFixedDigest Z Zp.lay) = .ok (D, r)) :
    ∃ X N P, r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧
      (Key.descriptionFromSource X N P).data "key file" = .ok D ∧
      (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = L₁ ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder.map (·.rounds.length) = L₂ ∧
      (Key.descriptionFromSource X N P).second.blocksInOrder.map (·.rounds.length) = L₃ := by
  cases hZ' : VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay) with
  | error e =>
    rw [hZ'] at h
    cases h
  | ok Z =>
    rw [hZ'] at h
    obtain ⟨m, X, N, P, hm, hX, -, -, -, hp, hw, -, -, hd, hr⟩ :=
      Key.laidFixed_is Z Zp.lay D r h
    exact ⟨X, N, P, hr, hd, rounds_in_scope hZ
      (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hZ') hm hX hp hw⟩

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.first_full
#print axioms Johnson.RunOne.Sound.shared_full
#print axioms Johnson.RunOne.Sound.second_full
#print axioms Johnson.RunOne.Sound.first_full_no
#print axioms Johnson.RunOne.Sound.shared_full_no
#print axioms Johnson.RunOne.Sound.rounds_in_scope
#print axioms Johnson.RunOne.Sound.laid_rounds_in_scope
