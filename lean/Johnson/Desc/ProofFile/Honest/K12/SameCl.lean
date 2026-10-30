-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SameCl.lean: the proximity test's block is the same at every type
of claims in five of its fields: name, place, rounds, oracle messages, decision. A block
(`Block S Cl`, Johnson/Desc/Block.lean) is a sub-protocol at one place: S is the type of the state
that it carries on, Cl the type of a claim. The test's block is `proximityTestKind X p`
(Johnson/Desc/K12/Frame.lean). It is general in the type of claims, which none of its parts (`Part`,
`Parts`) names. Theorems of this folder such as `saysYes_k12` (SaysYesK12.lean) are stated at the
type `Unit`, and a file's chain places the test at its own type: the key file's first chain at
`Claim` (`firstChain`, Johnson/Desc/Key/Chain1.lean, by `rangesTest`, Johnson/Desc/Key/Ranges.lean).
`seatOf_inside` (SaysYesSeat.lean in this folder) calls `same_k12` to pass from any type of claims
to `Unit`. The five fields are what a step reads of a block: `Block.step` (Johnson/Desc/Block.lean)
reads `rounds` and `decide`; `chainSteps` in the frame (Johnson/Desc/ProofFile/Honest/Frame.lean)
reads `name`, `place`, `rounds` and `oracles`. General in the state's type T, the parts X, the
numbers p of the place and both types of claims; `same_k12` has no hypothesis. Definitions and
theorems.

  `same_k12`: `SameB` holds of `proximityTestKind X p` at the type Cl and `proximityTestKind X p` at the type Cl', also where
    `proximityTestKind` returns its block whose test on the plan fails (the place has no stage, or
    `H2U.roundsOfNums` or `H2U.testOracles` returns `none` at the numbers of the place)
  `SameB B B'`: a definition: for a block B at the type Cl and a block B' at the type Cl', over one
    type of state, five equations: `name`, `place`, `rounds`, `oracles` and `decide` are equal
  `SameB.openings`: under `SameB B B'` the two blocks have the same number of groups of columns
    (`Block.openings`)
  `same_at`, `same_asks`: `SameB` holds of a part at its rounds (`Part.at`) at two types of claims,
    and of a block without a round whose decision is one test on the state (`asks`)
  `same_andThen`: if `SameB p p'` and `SameB q q'`, then `SameB` holds of the two pairs, each joined
    into one block by `Block.andThen` under the same name
  `same_stagesFrom`: `SameB` holds of `stagesFrom X p j cur rest l`, the block of the stages from
    number j on, at two types of claims, for every list of later stages
  `inner X p first rest rs`: a definition: the four blocks that `proximityTestKind` joins by `Block.andThen` (the
    front, the batching, the test that the group is the first stage's, the stages), before `proximityTestKind`
    sets `name`, `place`, `before` and `planOk` anew
  `same_inner`: `SameB` holds of `inner` at two types of claims

By what. No lemma of another file. `same_at` and `same_asks` hold by `rfl`. `same_andThen` unfolds
`Block.andThen` (Johnson/Desc/Block.lean) and rewrites by the hypotheses' equations and by
`SameB.openings`. `same_stagesFrom` goes by recursion on the list of later stages, along
`stagesFrom` (Johnson/Desc/K12/Frame.lean). `same_k12` unfolds `proximityTestKind` and splits into the cases of
its match: in the three cases of the failing block all five equations hold by `rfl`; in the fourth,
name and place hold by `rfl`, and rounds, oracle messages and decision are those of `same_inner`.

Limits. `SameB` has no clause on the four other fields of a block: `planOk` (the test on the plan),
`before`, `claims` and `after`. So nothing is stated on the test on the plan. The blocks that
`Block.inside` and `Block.retype` (Johnson/Desc/Block.lean) make of a block b have a test on the
plan that reads the list `b.claims`. Nothing on a decision's value, on completeness, on soundness or
on what is hidden.
-/
import Johnson.Desc.K12.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12

variable {T Cl Cl' : Type}

/-- Two blocks at two types of claims, over one type of state, are equal in the five fields that a
step reads (`Block.step`; the frame's `chainSteps`). No clause on `planOk`, `before`, `claims` or
`after`. -/
structure SameB (B : Block T Cl) (B' : Block T Cl') : Prop where
  name : B.name = B'.name
  place : B.place = B'.place
  rounds : B.rounds = B'.rounds
  oracles : B.oracles = B'.oracles
  decide : B.decide = B'.decide

theorem SameB.openings {B : Block T Cl} {B' : Block T Cl'} (h : SameB B B') :
    B.openings = B'.openings := by
  unfold Block.openings
  rw [h.rounds]

theorem same_at (x : Part T) (name : String) (place : Place) (l : Laid) :
    SameB (x.at name place l : Block T Cl) (x.at name place l : Block T Cl') :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem same_asks (name : String) (place : Place) (ok : T → Bool) :
    SameB (asks name place ok : Block T Cl) (asks name place ok : Block T Cl') :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem same_andThen (name : String) {p q : Block T Cl} {p' q' : Block T Cl'} (hp : SameB p p')
    (hq : SameB q q') : SameB (p.andThen name q) (p'.andThen name q') := by
  refine ⟨rfl, hp.place, ?_, ?_, ?_⟩
  · show p.rounds ++ q.rounds = p'.rounds ++ q'.rounds
    rw [hp.rounds, hq.rounds]
  · show p.oracles ++ q.oracles = p'.oracles ++ q'.oracles
    rw [hp.oracles, hq.oracles]
  · funext s rs gs
    show (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s' =>
        q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)) =
      (p'.decide s (rs.take p'.rounds.length) (gs.take p'.openings)).bind fun s' =>
        q'.decide s' (rs.drop p'.rounds.length) (gs.drop p'.openings)
    rw [hp.decide, hq.decide, hp.rounds, hp.openings]

theorem same_stagesFrom (X : Parts T) (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : Nat)
    (cur : Fmt.M1.Stage) (l : Laid),
    SameB (stagesFrom X p j cur rest l : Block T Cl) (stagesFrom X p j cur rest l : Block T Cl')
  | [], _, _, _ => same_at _ _ _ _
  | _ :: rest, j, _, l =>
    same_andThen _ (same_andThen _ (same_andThen _ (same_andThen _ (same_at _ _ _ _)
      (same_at _ _ _ _)) (same_at _ _ _ _)) (same_asks _ _ _))
      (same_stagesFrom X p rest (j + 1) _ _)

/-- The four blocks that `proximityTestKind` joins by `Block.andThen`: the front, the batching, the test that the
group is the first stage's, and the stages. It is `proximityTestKind`'s block before `proximityTestKind` sets the fields `name`,
`place`, `before` and `planOk` anew. rs: the declared rounds, which `proximityTestKind` takes from
`H2U.roundsOfNums p.nums`. -/
def inner (X : Parts T) (p : P12) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (rs : List Fmt.DeclaredRound) : Block T Cl :=
  ((((X.front p).at "the front" p.place []).andThen "the front"
    ((X.bat p (((rs.zip p.oracles).take 1).map (·.1))).at "the batching" p.place
      ((rs.zip p.oracles).take 1))).andThen "the batching"
    (asks "the group is not the first stage's" p.place fun t =>
      (X.group t).any (firstFits first))).andThen "the test"
    (stagesFrom X p 0 first rest ((rs.zip p.oracles).drop 1))

theorem same_inner (X : Parts T) (p : P12) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (rs : List Fmt.DeclaredRound) :
    SameB (inner X p first rest rs : Block T Cl) (inner X p first rest rs : Block T Cl') :=
  same_andThen _ (same_andThen _ (same_andThen _ (same_at _ _ _ _) (same_at _ _ _ _))
    (same_asks _ _ _)) (same_stagesFrom X p rest 0 first _)

/-- **`SameB` holds of the proximity test's block `proximityTestKind X p` at two types of claims.** -/
theorem same_k12 (X : Parts T) (p : P12) :
    SameB (proximityTestKind X p : Block T Cl) (proximityTestKind X p : Block T Cl') := by
  unfold proximityTestKind
  cases p.nums.stages with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons first rest =>
    cases H2U.roundsOfNums p.nums with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | some rs =>
      cases H2U.testOracles p.nums with
      | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | some os =>
        have h := same_inner (Cl := Cl) (Cl' := Cl') X p first rest rs
        exact ⟨rfl, rfl, h.rounds, h.oracles, h.decide⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.SameB.openings
#print axioms ProofFile.Honest.K12.same_at
#print axioms ProofFile.Honest.K12.same_asks
#print axioms ProofFile.Honest.K12.same_andThen
#print axioms ProofFile.Honest.K12.same_stagesFrom
#print axioms ProofFile.Honest.K12.same_inner
#print axioms ProofFile.Honest.K12.same_k12
#print axioms ProofFile.Honest.K12.SameB
#print axioms ProofFile.Honest.K12.inner
