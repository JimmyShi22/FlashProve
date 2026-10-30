-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ProofOwn.lean: the first chain of a proof file opens own trees alone, and the book
that its block's dry run leaves holds own trees alone, for the blocks that the verifier program
lays.

Statements and proofs. OnBytes/Maker/SrcFitsOf.lean asks `OwnAlone` and `OwnBook` of the first chain
and pays them for a key's one-time chain. A proof's first chain runs the caller's links. The laws of
OnBytes/TypedOracleCompiler/Laws/LawProof.lean say that the program's own block carries the relation "alike" under
every relation of given sources; at the relation that no two given sources meet, "alike to itself"
says: no given source.

Main names:
  `first_own`: for every block of a first chain that carries the relation at `NoGiven` in a dry run,
    from a start that is alike to itself.
  `proof_own_links`: for `firstBlock p (runLinksH links p wsLay) reply`, if each link's check
    carries the relation.
  `proof_own_program`: for the links that the program passes to its check, from the yes of
    `Verify.linksOf` alone.
Limits: for a block with other links the two stay premises. Nothing on soundness.


-/
import OnBytes.Maker.SrcFitsOf

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws OnBytes.Model
open OnBytes.Params (Rounds)

/-- **Every block of a first chain that carries the relation where no given source is met.** -/
theorem first_own {block : Blk FirstEnd} {s : Start}
    (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
    (hs : StartAlike NoGiven s s) {R : Rounds} {e : FirstEnd}
    (h : block.dryRun s = some (R, e)) : OwnAlone R ∧ OwnBook e.book := by
  have k := hb.dryRun hs
  rw [h] at k
  cases k with
  | some q => exact ⟨ownAlone_of_noGiven q.1, fun _ => q.2.book.of_noGiven⟩

/-- The program's form of a first chain's block, if each link's check carries the relation. -/
theorem proof_own_links (p : Params.First) (links : Array Stages.LinkH) (wsLay : WsLay)
    (hl : ∀ X ∈ links.toList, SameL (Alike NoGiven true) X.run) (reply : E) {R : Rounds}
    {e : FirstEnd}
    (h : (firstBlock p (Stages.runLinksH links p wsLay) reply).dryRun (firstStart p) =
      some (R, e)) : OwnAlone R ∧ OwnBook e.book :=
  first_own (carries_firstBlock_links p links wsLay hl reply) (firstStart_alike p) h

/-- **The links that the program passes to its check.** -/
theorem proof_own_program (X : Verify.Public) {cov : Head.Covered} {ls : Array Stages.LinkH}
    (hX : Verify.linksOf X cov = .ok ls) (built : Array Stages.LinkH) (p : Params.First)
    (wsLay : WsLay) (reply : E) {R : Rounds} {e : FirstEnd}
    (h : (firstBlock p
      (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) p wsLay)
      reply).dryRun (firstStart p) = some (R, e)) : OwnAlone R ∧ OwnBook e.book :=
  first_own (carries_programBlock X hX built p wsLay reply) (firstStart_alike p) h

end OnBytes.Maker
