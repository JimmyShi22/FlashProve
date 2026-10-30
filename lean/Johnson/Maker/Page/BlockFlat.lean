-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/BlockFlat.lean: for a call at which `K.PortYesAt` holds and a typed instance i
whose words are those of the call's request and reply files, under hypotheses on i and on the sizes
P that are not proved here, the first chain's block in the flat description of a proof file's
protocol is `firstBlockOf`: the block as the program's check builds it
(Johnson/Maker/Page/BlockCall.lean).

The protocol takes that block as a parameter block : X → Blk FirstEnd. The flat description sets it
to (pubOf p P hV).block (OnBytes/Flat/BigOf.lean, Johnson/Flat/PubOf.lean), p the plan of the three
public files: the links' block at the words that encode the instance, and the instance's reply. The
plan is fixed; the instance gives words alone.
  links_at: where CallFacts holds (Johnson/Maker/Page/BlockCall.lean), linksAtWords returns the
    links' run of which firstBlockOf is made.
  pubOf_block_at: for an instance x with r < e (and y = 0 if e is before the window's end), where
    0 < P.V, P.T is the plan's window, P.T < 2 ^ 32, P.V ≤ 2 ^ 32, and CallFacts holds at the words
    that encode x: (pubOf p P hV).block x = firstBlockOf p links so.y.
  yes_block_flat: all clauses of yes_chains (BlockCall.lean), with the flat record of the three
    chains at the block (pubOf p P hV).block i. So the flat record of the three chains stands at the
    description's block at i: the two blocks are equal. Its hypotheses on i and P are not proved
    here: its docstring lists them.

What is not claimed. The theorem speaks of the instance of the call. The description's plain data
are made by a dry run at another, fixed instance (pubOf's x₀ is firstInstance): that the dry run's
rounds at that instance are those at the call's is not said here. Nothing on soundness or hiding.

-/
import Johnson.Maker.Page.BlockCall
import Johnson.Flat.PubOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Proof OnBytes.TieK OnBytes.Flat Inst.Model

/-- Where the three computations return, linksAtWords returns the links' run. -/
theorem links_at {p : Model.Verify.Planned} {R Q : Array UInt32} {so : Model.Head.StOwn}
    {cov : Model.Head.Covered} {links : Array Model.Stages.LinkH}
    (h : CallFacts p R Q so cov links) :
    linksAtWords p R Q =
      .ok (Model.Stages.runLinksH
        (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
        p.chains.proof.first p.X.layers.wsLay) := by
  unfold linksAtWords
  simp only [h.own, h.covered, h.links, bind, Except.bind, pure, Except.pure]

/-- The flat description's block at an instance x with r < e (and y = 0 if e is before the window's
end), under the hypotheses hV, hP, hT, hV' on P and CallFacts at the words that encode x, is
`firstBlockOf`. -/
theorem pubOf_block_at (p : Model.Verify.Planned) (P : Params) (hV : 0 < P.V) (x : Instance' P)
    (hP : P.T = p.X.T) (hT : P.T < 2 ^ 32) (hV' : P.V ≤ 2 ^ 32) (hre : x.r < x.e)
    (hy : x.e < P.T → x.y.val = 0) {so : Model.Head.StOwn} {cov : Model.Head.Covered}
    {links : Array Model.Stages.LinkH}
    (h : CallFacts p (requestWordsOf x) (replyWordsOf x) so cov links) :
    (pubOf p P hV).block x = firstBlockOf p links so.y := by
  have e : Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) p.X.T =
      .ok { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val } := by
    rw [← hP]
    exact stFromCall_wordsOf x hT hV' hre hy
  have hso : so = { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val } :=
    Except.ok.inj (h.own.symm.trans e)
  have hyv : so.y = x.y.val := by rw [hso]
  rw [pubOf_block, linksOf_eq p x (links_at h), hyv]
  rfl

/-- The eight facts of yes_chains, from `K.PortYesAt`, with the flat description's block at the
typed instance of the call in the place of firstBlockOf, and the equation of the two blocks. p is
any plan with the planner's equation hp. The hypotheses on i and P: the two equations on words, r <
e, y = 0 if e is before the window's end, and that P.T is the plan's window; beside them 0 < P.V,
P.T < 2 ^ 32 and P.V ≤ 2 ^ 32. They are not proved here. They are meant for i := the instance built
from the call's request and reply and P := the sizes read off the parameter file; a theorem that
proves them there has a hypothesis of its own: that the sizes can be read off the parameter file,
which is refused for every file whose acceptance policy is not exact match. -/
theorem yes_block_flat {F : K.Files} {id : String} {table further : OnBytes.Params.TableName}
    (h : K.PortYesAt F id table further) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (P : Params) (hV : 0 < P.V)
    (i : Instance' P) (hP : P.T = p.X.T) (hT : P.T < 2 ^ 32) (hV' : P.V ≤ 2 ^ 32)
    (hR : requestWordsOf i = Model.Verify.words32 F.request)
    (hQ : replyWordsOf i = Model.Verify.words32 F.y) (hre : i.r < i.e)
    (hy : i.e < P.T → i.y.val = 0) :
    ∃ so cov item links j d real real2,
      CallFacts p (requestWordsOf i) (replyWordsOf i) so cov links ∧
      (pubOf p P hV).block i = firstBlockOf p links so.y ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, j) ∧
      readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      p.chains.proof.first.describe further F.entry item F.request d.rounds1 = some d.S1 ∧
      ThreeChains (tailPublic p.chains.proof further) ((pubOf p P hV).block i)
        (firstStart p.chains.proof.first) F.proof j d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SlotFacts (tailPublic p.chains.proof further).binding
        (tailPublic p.chains.proof further).shared.given.cfg d.seal1 F.proof d.r.first.next
        d.r.place d.salt d.path ∧
      d.copy = F.entry := by
  obtain ⟨so, cov, item, links, j, d, real, real2, hf, h3, hh, hd, hs, T, sf, hc⟩ :=
    yes_chains h hp
  rw [← hR, ← hQ] at hf
  have hb := pubOf_block_at p P hV i hP hT hV' hre hy hf
  refine ⟨so, cov, item, links, j, d, real, real2, hf, hb, h3, hh, hd, hs, ?_, sf, hc⟩
  rw [hb]
  exact T

end Johnson.Session

#print axioms Johnson.Session.links_at
#print axioms Johnson.Session.pubOf_block_at
#print axioms Johnson.Session.yes_block_flat
