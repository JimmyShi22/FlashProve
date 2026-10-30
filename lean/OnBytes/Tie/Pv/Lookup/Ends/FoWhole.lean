-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoWhole.lean.
From a passing result of the whole call to the run of every link.

The library's `Verify.wholeCall_passed` (OnBytes/Model/VerifyLawsWhole.lean) says what a passing
result of the whole call rests on; its last clause but one is a yes of the checker of the proof
file, with the links as built, each with the check that knows the request. That yes is the premise
of `accepted_ran` (OnBytes/Tie/Pv/Lookup/Ends/FoAccepted.lean) and `accepted_at`
(OnBytes/Tie/Pv/Lookup/Ends/FoLinksEach.lean).

 * `passed_at`: if the whole call on the files with the entry returns a passing result, then there
   are the common beginning C of the stages, the covered positions cov of the request and the links
   of `Verify.linksOf C.X cov`, as that law names them, such that at each place i: the chain's first
   call for link i has returned, to (k', c1); `Clean c1`; and the routine of the sub-proof that
   stands at place i of these links, at C.X's own arguments, has run from the link's state made of
   k' and i, from the planned state of the record built at place i, and from c1 (`RanAt`).

 * `passed_ran`: the same premise; the chain itself: the proof file was read, to rd; the chain's
   calls have started from `viewStart` of the first chain's view of rd; `LinksRan` behind that
   start.

Of the law's other clauses those are handed on that name C, cov and the links. What `accepted_at`
leaves unsaid is unsaid here too.
Not tied in `passed_ran`: the table's name `further` and the request's item `item`, under which the
proof file is read to rd. They stand under "there is", and the law's clauses that fix them
(`Entry.check`, `Proof.requestItem`) are not handed on.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksEach
import OnBytes.Model.VerifyLawsWhole

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify

/-- Place by place. A corollary: q and c0 stand under the ∃, so c1 is tied here to nothing of the
proof file. Whoever needs that this run reads this file's rounds takes `passed_ran`. -/
theorem passed_at {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (C : Common) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH),
      readCall o f = .ok r ∧ commonOfCall r = .ok C ∧
      Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      linksOf C.X cov = .ok links ∧
      ∀ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size),
        ∃ (q q' : ChainCheck) (c0 c1 c2 : Ctx) (D : LinkCtx) (F : Fork),
          q.first c0 = .ok (q', c1) ∧ Clean c1 ∧
          RanAt C.X cov (links[i]) (C.built.links[i]).Fp
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf,
              list := (C.built.links[i]).Tp } c1 D F c2 := by
  obtain ⟨r, ent, p, C, table, further, h1, _, _, _, h5, _, _, _,
    ⟨so, cov, item, links, a1, a2, _, a4, a5⟩, _⟩ := wholeCall_passed hk h
  exact ⟨r, C, so, cov, links, h1, h5, a1, a2, a4, fun i hb hi =>
    accepted_at C.X cov links C.built.links a4 _ _ _ _ _ _ _ _ a5 i hb hi⟩

/-- The chain. The proof file was read, to rd; the chain's calls have started from the context in
which a run on the first chain's view of rd begins; behind that start the links have run, each from
where the link before ended. -/
theorem passed_ran {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (p : Planned) (C : Common) (further : Params.TableName) (so : Head.StOwn)
      (cov : Head.Covered) (item : ByteArray) (links : Array Stages.LinkH) (rd : Proof.ProofRead)
      (x : Proof.LinksResult × Ctx) (check check2 : ChainCheck) (c1 c2 : Ctx),
      readCall o f = .ok r ∧ planned r.pol r.KL r.layout = .ok p ∧ commonOfCall r = .ok C ∧
      Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      linksOf C.X cov = .ok links ∧
      (Proof.readProof p.chains.proof further k item r.request
        (Proof.firstBlock p.chains.proof.first
          (Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) (ofNat so.y)) r.proof).fromStart = .ok rd ∧
      ChainCheck.start p.chains.proof.first.shape p.chains.proof.first.layout
        (viewStart (Proof.firstStart p.chains.proof.first) rd.first.view) = .ok (check, c1) ∧
      LinksRan (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
        p.chains.proof.first C.X.layers.wsLay
        (C.built.links.zipWith (fun b l => { b with run := l.run }) links).toList 0 check {} c1
        ((check2, x.1), c2) ∧
      check2.finish c2 = .ok ((), x.2) := by
  obtain ⟨r, ent, p, C, table, further, h1, _, _, h4, h5, _, _, _,
    ⟨so, cov, item, links, a1, a2, _, a4, a5⟩, _⟩ := wholeCall_passed hk h
  obtain ⟨rd, x, q, q2, c1, c2, b1, b2, b3, b4⟩ :=
    accepted_ran C.X cov links C.built.links a4 _ _ _ _ _ _ _ _ a5
  exact ⟨r, p, C, further, so, cov, item, links, rd, x, q, q2, c1, c2, h1, h4, h5, a1, a2, a4,
    b1, b2, b3, b4⟩

end Fo
