-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPassedHead.lean.
From a passing result of the whole call to the run of the output head's routine.

`passed_at` (OnBytes/Tie/Pv/Lookup/Ends/FoWhole.lean) speaks of every place of the links. Here the
head's place is named: the
last.

 * `common_public`: what the common beginning of the stages holds: its public record is `publicOf`'s
   on the configuration files, and its built links are `builtOf`'s on that record and its chains.
 * `passed_head`: if the whole call on the files with the entry returns a passing result, then, with
   r, C, so, cov and links as the library's `Verify.wholeCall_passed` names them: `publicOf r.pol
   r.KL r.layout = .ok C.X`; `Head.coveredOf so C.X.T C.X.P.h.V = .ok cov`; the built links and the
   links are equally many; and at the last place the chain's first call has returned, to (q', c1),
   `Clean c1`, and the output head's routine, at C.X's own arguments, has run from the link's state
   made of q', the place, the names of the arrays of the record built at that place and the head's
   own list of arrays, from the head's own planned state `C.X.H.Fp`, and from c1.

A corollary of `passed_at`: q and c0 stand under the ∃, so c1 is tied here to nothing of the proof
file; whoever needs that takes `passed_ran`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoWhole
import OnBytes.Tie.Pv.Lookup.Ends.FoBare

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify

theorem common_public {r : Read} {C : Common} (h : commonOfCall r = .ok C) :
    publicOf r.pol r.KL r.layout = .ok C.X ∧ builtOf C.X C.chains = .ok C.built := by
  obtain ⟨p, hp, e1, e2, e3⟩ := common_built h
  obtain ⟨a1, a2⟩ := planned_built hp
  rw [e1, e2, e3]
  exact ⟨a1, a2⟩

theorem passed_head {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (C : Common) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH) (hb : links.size - 1 < C.built.links.size)
      (q q' : ChainCheck) (c0 c1 c2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
      readCall o f = .ok r ∧ commonOfCall r = .ok C ∧
      publicOf r.pol r.KL r.layout = .ok C.X ∧
      Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      linksOf C.X cov = .ok links ∧ C.built.links.size = links.size ∧
      q.first c0 = .ok (q', c1) ∧ Clean c1 ∧
      Head.runForkHidH2 C.X.hS C.X.HLy (borderOf C.X.y) C.X.H C.X.owner cov C.X.layers.wsLay
        { check := q', link := links.size - 1,
          arrayOf := (C.built.links[links.size - 1]).arrayOf, list := C.X.H.Tp }
        C.X.H.Fp c1 = .ok (((w, D), F), c2) := by
  obtain ⟨r, C, so, cov, links, h1, h2, h3, h4, h5, hat⟩ := passed_at hk h
  obtain ⟨hX, hB⟩ := common_public h2
  have sb := built_bare hB h5
  obtain ⟨hs, hlast⟩ := linksOf_last C.X cov links h5
  have hb : links.size - 1 < C.built.links.size := by
    rw [sb.size]
    exact hs
  obtain ⟨q, q', c0, c1, c2, D, F, e0, e1, e2⟩ := hat (links.size - 1) hb hs
  obtain ⟨_, _, f3, f4⟩ := bare_fields (sb.at (links.size - 1) hb hs)
  rw [f3, f4, hlast] at e2
  rcases e2 with ⟨hk0, _⟩ | ⟨hk1, _⟩ | ⟨_, w, hw⟩
  · have e : (2 : Nat) = 0 := hk0
    cases e
  · have e : (2 : Nat) = 1 := hk1
    cases e
  · exact ⟨r, C, so, cov, links, hb, q, q', c0, c1, c2, D, F, w, h1, h2, hX, h3, h4, h5, sb.size,
      e0, e1, hw⟩

end Fo
