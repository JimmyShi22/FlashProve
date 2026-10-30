-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Model/LinkRoundsList.lean: the rounds of the model's sub-proofs, link by link and moment by
moment, as lists; and with them the plans of a proof's three chains from a yes of `configure`.

`linkRounds` (OnBytes/Model/VerifySubproofs.lean) says by a link's number which sub-proof's rounds
are planned: for each group of layers the layers' and, if the proof covers attention, attention's;
last the head's. `linkList` says the same of the lists of OnBytes/Params/PlanListsSub.lean, at the
same records of numbers. So the model's sub-proofs are as `Plan.SubRuns` asks
(OnBytes/Plan/PlanListsReq.lean), and `configure_proof_is` (OnBytes/Plan/PlanListsProof.lean) holds
for them without that hypothesis: `configure_proof_model`. With it the rounds of the plans of a
proof's three chains are, in their order, the rounds of lists that are written down in variables, as
`configure_key_is` (OnBytes/Plan/PlanListsConfigure.lean) has it for a key.

Main definition: `linkList`.
Main theorems: `runs_linkRounds`, `subRuns_subproofsWith`, `shapesWith_sub`,
`configure_proof_model`.
What is not claimed: that `shapesWith` or `configure` says yes: both are hypotheses. Where the plan
of a number's group is missing the list is written as empty; the plan of the chain is then refused.
A yes of `shapesWith` has tested that no plan of a link is missing and that the links are as many as
the model's sub-proofs; of that yes only `shapesWith_sub` is kept here. That the records of numbers
(`layerNumbers`, `Head.HPlanH2.own`, `Attention.Plan.own`) are those of the sub-proofs that the
verifier runs. What OnBytes/Params/PlanListsSub.lean, OnBytes/Plan/PlanListsReq.lean and
OnBytes/Plan/PlanListsProof.lean do not claim is not claimed here. No list is evaluated here, and no
number of rounds is stated. For proofs only; the program, that is the Lean port built from OnBytes/,
does not import this file.
-/
import OnBytes.Model.VerifySubproofs
import OnBytes.Params.PlanListsSub
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params

/-- The rounds of a link's sub-proof that follow the sending of the oracle messages of one moment,
in the order of `linkRounds`. Written as empty where the plan of the number's group is missing
(`X.G`, `X.A`); the plan of the chain is then refused. -/
def linkList (s : Setting) (c : Scope) (X : Public) (link moment : Nat) : List RoundSpec :=
  if link == (if X.p4 then 2 else 1) * X.NGr then
    headList s c (forestSize X.HLy.fs) (X.H.own X.hS) (smallSize X.H.tl) moment
  else if link % (if X.p4 then 2 else 1) == 0 then
    match X.G[link / (if X.p4 then 2 else 1)]? with
    | some hp =>
      layerList s c (forestSize X.y.fo)
        (layerNumbers X.layers hp (link / (if X.p4 then 2 else 1))) (smallSize hp.tl) hp.nBatched
        moment
    | none => []
  else
    match X.A[link / (if X.p4 then 2 else 1)]? with
    | some a => attentionList s c (forestSize a.fs) a.own (smallSize a.seam.tl) moment
    | none => []

/-- The routine of a link's sub-proof after a moment adds the rounds of `linkList`. -/
theorem runs_linkRounds {s : Setting} {c : Scope} (X : Public) (link moment : Nat) :
    Runs s c 0 0 0 (linkRounds X link moment) () (linkList s c X link moment) 0 0 0 := by
  unfold linkRounds linkList
  dsimp only
  by_cases h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = true
  · rw [if_pos h1, if_pos h1]
    exact runs_headRounds _ _ _ _
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (link % (if X.p4 then 2 else 1) == 0) = true
    · rw [if_pos h2, if_pos h2]
      cases X.G[link / (if X.p4 then 2 else 1)]? with
      | some hp => exact runs_layerRounds _ _ _ _ _
      | none => exact runs_needs _ _ 0 0 0
    · rw [if_neg h2, if_neg h2]
      cases X.A[link / (if X.p4 then 2 else 1)]? with
      | some a => exact runs_attentionRounds _ _ _ _
      | none => exact runs_needs _ _ 0 0 0

/-- **The model's sub-proofs are as `Plan.SubRuns` asks**, with the lists `linkList` and nothing
after the links. -/
theorem subRuns_subproofsWith (s : Setting) (X : Public) (links : List ReqLink) :
    Plan.SubRuns s (subproofsWith X links) (linkList s .request X) [] :=
  ⟨fun l m => runs_linkRounds X l m, runs_pure () 0 0 0⟩

/-- What `shapesWith` returns has the model's sub-proofs. -/
theorem shapesWith_sub {X : Public} {links : List ReqLink} {layout : ReqLayout}
    {identifiers : List Nat} {x : Shapes} (h : shapesWith X links layout identifiers = .ok x) :
    x.sub = subproofsWith X links := by
  unfold shapesWith at h
  extract_lets at h
  obtain ⟨rc, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  obtain ⟨ranges, _, h⟩ := exc_bind h
  cases h
  rfl

/-- **From `configure`'s yes at the shapes that the verifier's own plans hand over: the plans of a
proof's three chains against their lists**, with no hypothesis on the sub-proofs: the first chain's
list has `linkList` between the frame's rounds and nothing after the links. The list reads the
setting and all sizes from `made.sized.proof`: what these are is kept by `configure_proof_sizes`
(OnBytes/Plan/PlanListsProof.lean), and `x.sub` by `shapesWith_sub`. -/
theorem configure_proof_model {X : Public} {links : List ReqLink} {layout : ReqLayout}
    {identifiers : List Nat} {x : Shapes} (hx : shapesWith X links layout identifiers = .ok x)
    {l : Lines} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) :
    ∃ F S2 S3 Ls, made.proof = [F, S2, S3] ∧
      linSizeOf made.sized.proof.codes made.sized.proof.batch = some Ls ∧
      PlanIs F (settingOf l) .request
        (Plan.firstChainList made.sized.proof x.sub (linkList (settingOf l) .request X) []) ∧
      PlanIs S2 (settingOf l) .shared
        (linSharedTests (settingOf l) .shared made.sized.proof.batch Ls ++ [sealRound]) ∧
      PlanIs S3 (settingOf l) .request
        (secondChainList (settingOf l) .request made.sized.proof.batch) := by
  have S : Plan.SubRuns (settingOf l) x.sub (linkList (settingOf l) .request X) [] := by
    rw [shapesWith_sub hx]
    exact subRuns_subproofsWith _ X links
  obtain ⟨_, _, F, S2, S3, Ls, h1, h2, _, p1, p2, p3⟩ := configure_proof_is h S
  exact ⟨F, S2, S3, Ls, h1, h2, p1, p2, p3⟩

end OnBytes.Model.Verify
