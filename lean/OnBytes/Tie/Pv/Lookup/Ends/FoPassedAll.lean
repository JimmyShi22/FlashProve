-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPassedAll.lean.
From a passing result of the whole call to the run of each sub-proof's routine, with the chain of
links around it.

`accepted_ran` (OnBytes/Tie/Pv/Lookup/Ends/FoAccepted.lean) ties the chain of the links to the proof
file. `cut_at`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaces.lean) takes the link at a place out of that chain and keeps the
chain. Here both are said
on one set of witnesses.

 * `PassedRan`: under one name, the clauses of the library's `Verify.wholeCall_passed` that name the
   call's own objects, and those of `accepted_ran` (OnBytes/Tie/Pv/Lookup/Ends/FoAccepted.lean) on
     them: the files were read,
   to r, in which the proof names the entry k; the entry ent was there; `planned` returned p and the
   common beginning of the stages C, which holds p's chains; the checkers of the key file and of the
   entry file returned table and further; the statement's item; the request's own record so and its
   covered positions cov; the links of `Verify.linksOf C.X cov`; the proof file was read, to rd; the
   chain's calls have started from `viewStart` of the first chain's view of rd, to (check, c1);
   `LinksRan` from there, of the links as the verifier runs them, to ((check2, x.1), c2); the
   chain's last call from there.
 * `passed_all`: if the tests before the entry is read returned the number k (`entryNumber`) and
   the whole call on the same files with the entry returns a passing result, then there are such
   witnesses, with `publicOf r.pol r.KL r.layout = .ok C.X`, and on these witnesses:
   - for each group g with a plan hp for its layers there is a place i at which `CutAt` holds and
   the layers' routine, at the public record with the request's tokens, at hp and g, has run from
   the link's state made of q', i, the names of the arrays of the record built at place i and
   `hp.Tp`, from `hp.Fp` and from d1;
   - if the proof covers attention: the like for each group g with a plan hp for its layers and a
   plan a for its attention, from `a.seam.Tp` and `a.seam.Fp`;
   - the like for the output head, at the last place, at C.X's own records, from `C.X.H.Tp` and
   `C.X.H.Fp`.
   In `CutAt`: the links before place i have run from (check, c1) to mid; the chain's first call for
   link i has run from mid, to (q', d1); `Clean d1`; `runLinkH` from mid to nxt; the links behind
   place i from nxt to the chain's end. So every state, record and list among the witnesses is fixed
   by a run equation, or a chain of them, that begins at the files. The place i alone is not: it is
   some place, tied to the group through the run
   (OnBytes/Tie/Pv/Lookup/Ends/FoPassedPlaces.lean says which link stands there).

Not said: the number of the place at which a group's link stands; what `runLinkH` does behind the
routine; what the rest of the first chain's block and the later chains do with what the links
return. Dropped, though `Verify.wholeCall_passed` has them: the checker's yes on the proof file as
such, and that the call asked for no fewer bits than the threshold.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaces
import OnBytes.Tie.Pv.Lookup.Ends.FoPassedHead

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify OnBytes.Model.Stages

/-- The clauses of the library's `Verify.wholeCall_passed` that name the call's own objects, and
those of `accepted_ran` on them. -/
def PassedRan (o : Options) (f : Files) (k : Nat) (entry : FileIn) (r : Read) (ent : ByteArray)
    (p : Planned) (C : Common) (table further : Params.TableName) (so : Head.StOwn)
    (cov : Head.Covered) (item : ByteArray) (links : Array LinkH) (rd : Proof.ProofRead)
    (x : Proof.LinksResult × Ctx) (check check2 : ChainCheck) (c1 c2 : Ctx) : Prop :=
  readCall o f = .ok r ∧ r.entry = k ∧ entry = some ent ∧
  planned r.pol r.KL r.layout = .ok p ∧ commonOfCall r = .ok C ∧ C.chains = p.chains ∧
  Key.check p.chains.key r.key = .ok table ∧
  Entry.check (p.chains.bytes .link) table ent = .ok further ∧
  Proof.requestItem r.pol r.KL r.request = some item ∧
  Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
  Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
  linksOf C.X cov = .ok links ∧
  (Proof.readProof p.chains.proof further k item r.request (Proof.firstBlock p.chains.proof.first
    (runLinksH (asRun C.built.links links) p.chains.proof.first C.X.layers.wsLay)
    (ofNat so.y)) r.proof).fromStart = .ok rd ∧
  ChainCheck.start p.chains.proof.first.shape p.chains.proof.first.layout
    (viewStart (Proof.firstStart p.chains.proof.first) rd.first.view) = .ok (check, c1) ∧
  LinksRan (asRun C.built.links links) p.chains.proof.first C.X.layers.wsLay
    (asRun C.built.links links).toList 0 check {} c1 ((check2, x.1), c2) ∧
  check2.finish c2 = .ok ((), x.2)

theorem passed_all {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (ent : ByteArray) (p : Planned) (C : Common) (table further : Params.TableName)
      (so : Head.StOwn) (cov : Head.Covered) (item : ByteArray) (links : Array LinkH)
      (rd : Proof.ProofRead) (x : Proof.LinksResult × Ctx) (check check2 : ChainCheck)
      (c1 c2 : Ctx),
      PassedRan o f k entry r ent p C table further so cov item links rd x check check2 c1 c2 ∧
      publicOf r.pol r.KL r.layout = .ok C.X ∧
      (∀ (g : Nat) (hp : Layer.HPlan2), C.X.G[g]? = some hp →
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          Layer.runForkHidG2 { C.X.layers with tokv := cov.tokv } hp g
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 = .ok (((w, D), F), d2)) ∧
      (C.X.p4 = true → ∀ (g : Nat) (hp : Layer.HPlan2) (a : Attention.Plan),
        C.X.G[g]? = some hp → C.X.A[g]? = some a →
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          Attention.run a
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := a.seam.Tp }
            a.seam.Fp d1 = .ok ((((), D), F), d2)) ∧
      (∃ (hb : links.size - 1 < C.built.links.size) (hi : links.size - 1 < links.size)
          (q' : ChainCheck) (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) (links.size - 1) hb hi q' d1 d2 D F ∧
          Head.runForkHidH2 C.X.hS C.X.HLy (borderOf C.X.y) C.X.H C.X.owner cov C.X.layers.wsLay
            { check := q', link := links.size - 1,
              arrayOf := (C.built.links[links.size - 1]).arrayOf, list := C.X.H.Tp }
            C.X.H.Fp d1 = .ok (((w, D), F), d2)) := by
  obtain ⟨r, ent, p, C, table, further, a1, b1, b2, a2, a3, b3, b4, b5,
    ⟨so, cov, item, links, a4, a5, b6, a6, hacc⟩, _⟩ := wholeCall_passed hk h
  obtain ⟨rd, x, check, check2, c1, c2, a7, a8, a9, a10⟩ :=
    accepted_ran C.X cov links C.built.links a6 _ _ _ _ _ _ _ _ hacc
  obtain ⟨hX, hB⟩ := common_public a3
  have sb := built_bare hB a6
  have cut := cut_at C.X cov links C.built.links a6 sb p.chains.proof.first C.X.layers.wsLay
    check c1 ((check2, x.1), c2) a9
  refine ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2,
    ⟨a1, b1, b2, a2, a3, b3, b4, b5, b6, a4, a5, a6, a7, a8, a9, a10⟩, hX, ?_, ?_, ?_⟩
  · intro g hp hg
    obtain ⟨i, hi, ei⟩ := layer_place C.X cov links a6 g hp hg
    have hb : i < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut i hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    obtain ⟨w, hw⟩ := ranAt_layer C.X cov g hp hg _ _ _ _ _ _ _ _ _ hr
    exact ⟨i, hb, hi, q', d1, d2, D, F, w, hc, hw⟩
  · intro h4 g hp a hg ha
    obtain ⟨i, hi, ei⟩ := att_place C.X cov links a6 h4 g hp hg a ha
    have hb : i < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut i hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    exact ⟨i, hb, hi, q', d1, d2, D, F, hc, ranAt_att C.X cov g a ha _ _ _ _ _ _ _ _ _ hr⟩
  · obtain ⟨hi, ei⟩ := linksOf_last C.X cov links a6
    have hb : links.size - 1 < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut (links.size - 1) hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    obtain ⟨w, hw⟩ := ranAt_head C.X cov _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨hb, hi, q', d1, d2, D, F, w, hc, hw⟩

end Fo
