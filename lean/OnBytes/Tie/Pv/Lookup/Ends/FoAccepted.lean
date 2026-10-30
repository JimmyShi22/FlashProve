-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAccepted.lean.
From the checker's yes on a proof file to the run of every link.

The checker of a proof file (`Proof.check`) runs the block of the first chain on the view that the
strict reader has made of the file. That block begins with the caller's links.

 * `accepted_links`: if the checker accepts, the file was read (to rd), and the caller's links have
   returned from the context in which a run on the first chain's view begins (`viewStart`,
   OnBytes/Tie/Pv/Lookup/Ends/FoLinksOf.lean). By the library's `Proof.proofRefusal_eq`: the
     decision is a run of the first
   chain's block by `Blk.runOn`, then the tail; `runOn_start`; and the first line of
   `Proof.firstBlock`.
 * `accepted_ran`: if the checker accepts with the links as the verifier runs them (the premise is
   what `wholeCall_passed` in OnBytes/Model/VerifyLawsWhole.lean concludes of a call that passes),
   then the chain's calls have started from that context, and
   `LinksRan` (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean) holds behind that start: link by link, the
     chain's first call from
   where the link before ended, `Clean` behind it, and there the link's routine from its planned
   state. With `built_kind`, `some_ok` and `none_ok` (OnBytes/Tie/Pv/Lookup/Ends/FoLinksKind.lean)
     each of these runs is a run
   of one of the three sub-proofs' routines.

`words`, in both statements: any bytes; at the program's call the request file's own.

Not tied: what the links return, r, to the rest of the first chain's block. No statement here draws
the last sentence's conclusion link by link: whoever wants it opens `LinksRan` by its recursion.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksKind
import OnBytes.Proof.File

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem accepted_links (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (reply : E) (links : Blk Proof.LinksResult) (file : ByteArray)
    (h : Proof.check c table copy request words reply links file = .accepted) :
    ∃ (rd : Proof.ProofRead) (r : Proof.LinksResult × Ctx),
      (Proof.readProof c table copy request words (Proof.firstBlock c.first links reply)
        file).fromStart = .ok rd ∧
      links (viewStart (Proof.firstStart c.first) rd.first.view) = .ok r := by
  unfold Proof.check at h
  dsimp only at h
  split at h
  · exact absurd h (by intro e; cases e)
  · rename_i rd hrd
    split at h
    · exact absurd h (by intro e; cases e)
    · rename_i hn
      rw [Proof.proofRefusal_eq] at hn
      unfold Proof.judge at hn
      cases e : (Proof.firstBlock c.first links reply).runOn (Proof.firstStart c.first)
          rd.first.view with
      | error f =>
        rw [e] at hn
        exact absurd hn (by simp)
      | ok real =>
        obtain ⟨x', hr⟩ := runOn_start _ _ _ _ e
        unfold Proof.firstBlock at hr
        obtain ⟨r, x1, h1, _⟩ := (bindB_ok _ _ _ _).1 hr
        exact ⟨rd, (r, x1), hrd, h1⟩

/-- The checker's yes, with the links as the verifier runs them. -/
theorem accepted_ran (X : Verify.Public) (cov : Head.Covered) (links built : Array Stages.LinkH)
    (hl : Verify.linksOf X cov = .ok links) (c : Params.ProofChains) (table : Params.TableName)
    (copy : Nat) (request words : ByteArray) (reply : E) (wsLay : WsLay) (file : ByteArray)
    (h : Proof.check c table copy request words reply
      (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) links) c.first wsLay)
      file = .accepted) :
    ∃ (rd : Proof.ProofRead) (r : Proof.LinksResult × Ctx) (check check2 : ChainCheck)
      (c1 c2 : Ctx),
      (Proof.readProof c table copy request words (Proof.firstBlock c.first
        (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) links) c.first
          wsLay) reply) file).fromStart = .ok rd ∧
      ChainCheck.start c.first.shape c.first.layout
        (viewStart (Proof.firstStart c.first) rd.first.view) = .ok (check, c1) ∧
      LinksRan (built.zipWith (fun b l => { b with run := l.run }) links) c.first wsLay
        (built.zipWith (fun b l => { b with run := l.run }) links).toList 0 check {} c1
        ((check2, r.1), c2) ∧
      check2.finish c2 = .ok ((), r.2) := by
  obtain ⟨rd, r, hrd, hr⟩ := accepted_links c table copy request words reply _ file h
  obtain ⟨k, k2, c1, c2, e1, e2, e3⟩ :=
    run_ran _ c.first wsLay _ r (built_stays X cov links built hl) hr rfl
  exact ⟨rd, r, k, k2, c1, c2, hrd, e1, e2, e3⟩

end Fo
