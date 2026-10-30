-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/PlannerRequestHas25Links.lean: AT FILES IN THE GOALS' SCOPE, WHERE THE PLANNER
(OnBytes.Model.Verify.planned) RETURNS, ITS REQUEST HAS 25 LINKS. From the scope alone: no pin, and
not the premise on the stored layout file's group lines (LayoutGroupsAre; proved in AtFullSide/).
A law file; no running text imports it.

Why. The code switch's typed table (K2Caller.tableOf) reads the three public files anew, by the
planner; it has at most as many rows as that planner's request has links (TableRows.lean).

  older_links   InScope Z · Verify.planned Z.pol Z.KL (some Z.lay) = .ok p ⟹
                p.chains.made.sized.proof.request.link.length = 25.
  plain_links   the same of the proof file's plain planner (ProofFile.Plain.planned, at every letter for
                the second hash function): by plain_parts (ProofSizesAtPlain.lean).
  pub_links     so of the public part that ProofFile.pubPlain makes: Zp.p's request has 25 links.
The road, each step a theorem of other files: the planner's run taken apart (chainsOf_parts ·
Fo.shapesOf_cut · shapesWith_count: the frame's links are (2 or 1) · NGr + 1) · in scope the public
part is the full size's (publicO_at_scope, at the second hash function by publicOfO_older) ·
configure's yes gives proofSized's (configure_proof_sizes) · proofSized lays request.link :=
fillLinks sub.links (proofSized_request) · the sub-proofs' links are withReply of the frame's
(subproofsWith) · fillLinks and withReply keep the length.
Spent by: SpotsOfRows.lean's spots_core (older_links) · SpotsAtName.lean's spotsB_at_name
(pub_links).
Limits. NOTHING SAYS THAT THE PLANNER RETURNS. The full size alone. Nothing on soundness.

-/
import Johnson.Goal.Numbers.ProofLinksAtScope
import OnBytes.Tie.Pv.Lookup.Ends.FoSizedLink
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Tie
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)
open H2K.Sizes H2K.Member Lk6.AtPlan Johnson.G VerifierAndGoals.Sizes

/-- **In scope the request of verify-on-bytes's planner has 25 links.** -/
theorem older_links {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.request.link.length = 25 := by
  unfold Verify.planned at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  dsimp only at hp
  obtain ⟨chains, hch, hp⟩ := exc_bind hp
  obtain ⟨built, hbu, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨links, shapes, hs, hc, -, -⟩ := chainsOf_parts hch
  obtain ⟨rl, lay, _, declared, file, _, _, hf, hr, hw⟩ := Fo.shapesOf_cut hs
  obtain ⟨hn0, he⟩ := shapesWith_count hw
  have hX' : publicOfO secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X := by
    rw [publicOfO_older]
    exact hX
  obtain ⟨-, -, h4, hN⟩ := publicO_at_scope hZ hX'
  have hn : rl.length = 25 := by simp [hn0, h4, hN]
  obtain ⟨-, -, r3, -⟩ := proofSized_request (configure_proof_sizes hc).1
  rw [r3, he]
  show (fillLinks (withReply rl)).length = 25
  unfold fillLinks
  rw [List.length_map, TwLaw.withReply_length, hn]

/-- The same of the plain planner. -/
theorem plain_links {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.request.link.length = 25 := by
  obtain ⟨X, shapes, rl, lay', declared, file, hX, hc, he, hr, hn0, hf⟩ := plain_parts hp
  obtain ⟨-, -, h4, hN⟩ := publicO_at_scope hZ hX
  have hn : rl.length = 25 := by simp [hn0, h4, hN]
  obtain ⟨-, -, r3, -⟩ := proofSized_request (configure_proof_sizes hc).1
  rw [r3, he]
  show (fillLinks (withReply rl)).length = 25
  unfold fillLinks
  rw [List.length_map, TwLaw.withReply_length, hn]

/-- So of the public part. -/
theorem pub_links {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) :
    Zp.p.chains.made.sized.proof.request.link.length = 25 :=
  plain_links hZ (ProofFile.Law.pub_planned h)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.older_links
#print axioms VerifiableInference.Desc.First.K2Caller.pub_links
