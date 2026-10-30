-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntrySound.lean: ROUND-BY-ROUND SOUNDNESS OF THE ENTRY FILE'S LINK, as a protocol and
behind the two transformers at their idle settings, at the full-size and at the small files of the
setting "record with work", UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove), AND NOTHING ELSE.

Statements and their proofs, each one application: of OnBytes/Join1/LinkSound.lean to the link's
item on knowledge soundness (`entryFull_know`, `entrySmall_know`, OnBytes/Flat/EntryValue.lean) and
to the bound on its list of error counts (`frErr_below`, `srErr_below`,
OnBytes/Slice/LinkHoleAt.lean).

Main theorems:
  `entryFull_sound`, `entrySmall_sound`: the protocol of the link is sound, with `frErr`, `srErr`,
    for the language: the first table gives no index with its record; or the copy has a collision
    at its record's seed; or both give the same index.
  `entryFull_passed`, `entrySmall_passed`: behind the samplers that change nothing and the
    transformer for proof of work at no added bit: a list of errors, each at most 2^-128 as a share
    of its round's verifier messages, with which the passed protocol is sound for that language.

Letters that stay free: how a decoded table is read as an index (A), the rest of the configuration
(R), the nonces' type (W).
Not claimed. The theorem on codes. THE 128 BITS COUNT WORK: at six rounds of the full-size files and
at four of the small ones 32 of them are proof of work, which stands inside the written verifier
messages as test bits; the transformer adds none; that work is worth its bits is not shown. The
bound is one round's: no bound on the chance of a false proof. The language has ways out: how often
a collision occurs, and where a seed comes from, is not said here. The interactive form: no hash, no
bytes. Nothing on an honest prover. No transcript is shown that the link accepts. Whether a
statement of this file bites hangs on A: a table holds an index only where `A.inRange (A.mat u)`
(`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean), so where `A.inRange` holds of nothing `ConfigurationWithOutOfDomainSample.onEq` is
empty and the statement is true for free; and "the same index" is as fine as `A.mat` is. That
`ConfigurationWithOutOfDomainSample.onEq` has a member at this configuration is stated nowhere. One premise rides inside a
letter: the law `mat_cut` of A (OnBytes/Slice/DecoderRec.lean), which whoever hands in A must prove.
`Cb.BCHKS46At` speaks of all lengths, degree bounds and radii, not of the link's own codes and radii
alone: one false instance would empty what rests on it (the limits of Cb/Gen/CodeListRSAt.lean).
"Knowledge soundness" is the item's name: nothing is extracted (the comment on `Hiop.LinkKnowR`,
Hiop/RecSubs.lean). All that the heads of the files named above do not claim.

-/
import OnBytes.Flat.EntryValue
import OnBytes.Join1.LinkSound

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Hiop _root_.Run OnBytes.Slice OnBytes.Join1 OnBytes.Maker
open scoped ENNReal

/-! ## The full-size files -/

section
variable (hA : BCHKS46At GF GE) {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A)

include hA in
/-- **THE ENTRY'S LINK AT THE FULL-SIZE FILES IS ROUND-BY-ROUND SOUND, UNDER THE THEOREM ON CODES
ALONE**, for the language "the first table gives no index with its record, or the copy has a
collision at its record's seed, or both give the same index", with the list of error counts `frErr`.
-/
theorem entryFull_sound :
    entryFull.toInteractiveOracleProof.Sound
      (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
        (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) frErr :=
  link_sound_of_know (DecR.configurationOfStoredTable A R) entryFull frErr (entryFull_know hA A R)

include hA in
/-- **THE SAME AT THE PASSED PROTOCOL** (challenges drawn by the samplers that change nothing; no
bit of proof of work added by the transformer): a list of errors, each at most 2^-128 as a share of
its round's verifier messages, with which it is sound for that language. At six rounds 32 of the 128
bits are proof of work, inside the written verifier messages. W: the nonces' type. -/
theorem entryFull_passed (W : Type) [Inhabited W] :
    ∃ ε : Err (passed W entryFull.toInteractiveOracleProof).shape, Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      (passed W entryFull.toInteractiveOracleProof).Sound
        (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
          (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε :=
  link_passed W (DecR.configurationOfStoredTable A R) entryFull frErr _ (entryFull_know hA A R) frErr_below

end

/-! ## The small files -/

section
variable (hA : BCHKS46At GF GE) {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)

include hA in
/-- **THE SAME AT THE SMALL FILES**, with the list `srErr`. -/
theorem entrySmall_sound :
    entrySmall.toInteractiveOracleProof.Sound
      (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
        (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) srErr :=
  link_sound_of_know (DecR.configurationOfStoredTable A R) entrySmall srErr (entrySmall_know hA A R)

include hA in
/-- At the passed protocol. At four rounds 32 of the 128 bits are proof of work, inside the written
verifier messages. -/
theorem entrySmall_passed (W : Type) [Inhabited W] :
    ∃ ε : Err (passed W entrySmall.toInteractiveOracleProof).shape, Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      (passed W entrySmall.toInteractiveOracleProof).Sound
        (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
          (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε :=
  link_passed W (DecR.configurationOfStoredTable A R) entrySmall srErr _ (entrySmall_know hA A R) srErr_below

end
end OnBytes.Flat

#print axioms OnBytes.Flat.entryFull_sound
#print axioms OnBytes.Flat.entryFull_passed
#print axioms OnBytes.Flat.entrySmall_sound
#print axioms OnBytes.Flat.entrySmall_passed
