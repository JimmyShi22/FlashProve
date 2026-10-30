-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/BlockCall.lean: the first chain's block of a proof file at a call of the shipped
Lean verifier
(Where this and lean/THEOREM.md differ, the page
holds.), and eight facts on the request and the proof file at that block that follow from an
accepting run.

The program makes a plan p from the three public files. From the words of the request file and of
the reply file it then computes, at that plan, the request's and the reply's own values, what the
request covers, and the links' checks. From these it builds the block of the proof file's first
chain, before it checks the proof file.
  CallFacts p R Q so cov links: at the plan p, the request's words R and the reply's words Q, the
    three computations return so, cov, links. CallFacts.unique: p, R and Q determine the three.
  firstBlockOf p links y: the block as the program's check builds it from these values.
  yes_plan: an accepting run gives a plan of the three public files.
  yes_chains: from what the exit code 0 hands on (K.PortYesAt), at the call's own files F and at the
    plan of its three public files: the eight facts, among them the flat record of the three chains
    at firstBlockOf. Its docstring lists them.

What is not claimed. K.PortYesAt holds more than these eight. "An accepting run" stands here for the
proposition `K.PortYesAt` (OnBytes/K/Top.lean), which is weaker than the exit code 0; that a run
with exit code 0 gives it is that file's, not shown here. No typed instance is spoken of here
(Johnson/Maker/Page/BlockFlat.lean). Nothing on soundness or on hiding.

-/
import OnBytes.TieK.Good

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Proof OnBytes.TieK

/-- At the plan p and the words of a request and of a reply, the program's three computations return
these values. -/
structure CallFacts (p : Model.Verify.Planned) (R Q : Array UInt32) (so : Model.Head.StOwn)
    (cov : Model.Head.Covered) (links : Array Model.Stages.LinkH) : Prop where
  /-- the request's and the reply's own values -/
  own : Model.Head.stFromCall R Q p.X.T = .ok so
  /-- what the request covers -/
  covered : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov
  /-- the links' checks -/
  links : Model.Verify.linksOf p.X cov = .ok links

/-- The three values are functions of the plan and the words. -/
theorem CallFacts.unique {p : Model.Verify.Planned} {R Q : Array UInt32}
    {so so' : Model.Head.StOwn} {cov cov' : Model.Head.Covered}
    {links links' : Array Model.Stages.LinkH} (h : CallFacts p R Q so cov links)
    (h' : CallFacts p R Q so' cov' links') : so = so' ∧ cov = cov' ∧ links = links' := by
  obtain rfl : so = so' := Except.ok.inj (h.own.symm.trans h'.own)
  obtain rfl : cov = cov' := Except.ok.inj (h.covered.symm.trans h'.covered)
  obtain rfl : links = links' := Except.ok.inj (h.links.symm.trans h'.links)
  exact ⟨rfl, rfl, rfl⟩

/-- The first chain's block as the program's check builds it: the links as built, each with the
check of the link of linksOf at its place, and the reply. -/
@[reducible] def firstBlockOf (p : Model.Verify.Planned) (links : Array Model.Stages.LinkH)
    (y : ℕ) : Blk FirstEnd :=
  firstBlock p.chains.proof.first
    (Model.Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
      p.chains.proof.first p.X.layers.wsLay) (Model.ofNat y)

/-- Eight facts on the call's request and proof file, at the program's block, from an accepting run.
At the call's own files F and at any p with the planner's equation hp, there are values with:
CallFacts at the words of F.request and F.y (hence so, cov and links are functions of p and of the
two files' words); the request's item (the equation of Proof.requestItem); the place i behind the
proof file's head (the equation of readProofHead at F.proof); the fixed reading of the proof file
returns the further table and data d (the equation of readProofChains at F's files); the first
chain's description; the flat record of the three chains (TieK.ThreeChains) at firstBlockOf, at
F.proof and d's values, with its two real ends real, real2; the facts on the binding tree's leaf;
the stored copy's number. It is TieK.readProofChains_of behind TieK.port_entry and
TieK.port_proof_chains, with no clause of its conclusion dropped. -/
theorem yes_chains {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) :
    ∃ so cov item links i d real real2,
      CallFacts p (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) so cov links ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, i) ∧
      readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      p.chains.proof.first.describe further F.entry item F.request d.rounds1 = some d.S1 ∧
      ThreeChains (tailPublic p.chains.proof further) (firstBlockOf p links so.y)
        (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SlotFacts (tailPublic p.chains.proof further).binding
        (tailPublic p.chains.proof further).shared.given.cfg d.seal1 F.proof d.r.first.next
        d.r.place d.salt d.path ∧
      d.copy = F.entry := by
  obtain ⟨p', so, cov, item, links, i, d, real, real2, hp', h1, h2, h3, h4, hh, hd, hs, T, sf,
    hc⟩ := readProofChains_of F table further (port_entry F id table further h)
      (port_proof_chains F id table further h)
  obtain rfl : p' = p := Except.ok.inj (hp'.symm.trans hp)
  exact ⟨so, cov, item, links, i, d, real, real2, ⟨h1, h2, h4⟩, h3, hh, hd, hs, T, sf, hc⟩

/-- An accepting run (K.PortYesAt) gives a plan of the three public files. -/
theorem yes_plan {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) :
    ∃ p, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p := by
  obtain ⟨p, hp, -⟩ := port_entry F id table further h
  exact ⟨p, hp⟩

end Johnson.Session

#print axioms Johnson.Session.CallFacts.unique
#print axioms Johnson.Session.yes_chains
#print axioms Johnson.Session.yes_plan
