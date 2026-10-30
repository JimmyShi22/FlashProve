-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawProof.lean: law 2 ("blind") at the whole decision on a proof file
(OnBytes/Proof/File.lean: `proofRefusal`) and at the block that the program passes to it
(`firstBlock` over `runLinksH`).

Main names.
  `proofRefusal_blind`   for a first chain's block that carries law 2's relation: the decision on
                         the three views of a proof file is one and the same, refusal's name and
                         all, at two readings whose three views are equal but for the digests drawn,
                         whose keys are equal, and whose first chains have as many roots
  `carries_firstBlock_links`   the program's own block, firstBlock p (runLinksH links p wsLay)
                         reply, carries the relation, if each link's check does (`SameL`)
  `carries_programBlock` the same at the links that the program passes to Proof.check, from the yes
                         of linksOf alone
  `proofRefusal_blind_links`   the two together

Not claimed. Nothing on `readProof`. That the number of roots read is the description's.

-/
import OnBytes.TypedOracleCompiler.Laws.LawModel
import OnBytes.TypedOracleCompiler.Laws.LawDry

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Proof OnBytes.Model

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

theorem firstStart_alike (p : Params.First) : StartAlike G (firstStart p) (firstStart p) :=
  ⟨rfl, rfl, rfl, rfl, ⟨ArrAlike.empty _, rfl⟩⟩

/-- Law 2 at the decision on a proof file. -/
theorem proofRefusal_blind (c : Params.ProofChains) (table : Params.TableName)
    {block : Blk FirstEnd}
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) block block) (r r' : ProofRead)
    (h1 : ViewAlike r.first.view r'.first.view) (hk : r.key = r'.key)
    (h2 : ViewAlike r.shared.view r'.shared.view) (h3 : ViewAlike r.second.view r'.second.view)
    (hn : r.first.roots.length = r'.first.roots.length) :
    proofRefusal c table block r = proofRefusal c table block r' := by
  rw [proofRefusal_eq, proofRefusal_eq]
  rcases judge_alike hb (firstStart_alike c.first) h1 "first-chain-" with
    ⟨why, e1, e2⟩ | ⟨x, y, e1, e2, q⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact tailRefusal_blind _ q r r' hk h2 h3 hn

theorem carries_firstBlock_links (p : Params.First) (links : Array Stages.LinkH) (wsLay : WsLay)
    (h : ∀ X ∈ links.toList, SameL (Alike G d) X.run) (reply : E) :
    Carries (Alike G d) (FirstEndAlike G) (firstBlock p (Stages.runLinksH links p wsLay) reply)
      (firstBlock p (Stages.runLinksH links p wsLay) reply) :=
  carries_firstBlock p (same_runLinksH links p wsLay h) reply

/-- The program's own block carries the relation, in one lemma: the links as built, each
with the check of the link of linksOf at its place. -/
theorem carries_programBlock (X : Verify.Public) {cov : Head.Covered} {ls : Array Stages.LinkH}
    (e : Verify.linksOf X cov = .ok ls) (built : Array Stages.LinkH) (p : Params.First)
    (wsLay : WsLay) (reply : E) :
    Carries (Alike G d) (FirstEndAlike G)
      (firstBlock p
        (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) p wsLay) reply)
      (firstBlock p
        (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) p wsLay) reply) :=
  carries_firstBlock_links p _ wsLay (zipped_runs built ls (linksOf_runs X cov ls e)) reply

theorem proofRefusal_blind_links (c : Params.ProofChains) (table : Params.TableName)
    (links : Array Stages.LinkH) (wsLay : WsLay)
    (h : ∀ X ∈ links.toList, SameL (Alike AnyGiven false) X.run) (reply : E) (r r' : ProofRead)
    (h1 : ViewAlike r.first.view r'.first.view) (hk : r.key = r'.key)
    (h2 : ViewAlike r.shared.view r'.shared.view) (h3 : ViewAlike r.second.view r'.second.view)
    (hn : r.first.roots.length = r'.first.roots.length) :
    proofRefusal c table (firstBlock c.first (Stages.runLinksH links c.first wsLay) reply) r =
      proofRefusal c table (firstBlock c.first (Stages.runLinksH links c.first wsLay) reply) r' :=
  proofRefusal_blind c table (carries_firstBlock_links c.first links wsLay h reply) r r' h1 hk h2 h3
    hn

#print axioms proofRefusal_blind
#print axioms proofRefusal_blind_links

end OnBytes.TwoLaws
