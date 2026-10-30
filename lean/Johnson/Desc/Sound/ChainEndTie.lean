-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/ChainEndTie.lean: THE LAST BLOCK OF A CHAIN, IN ITS OWN TEXT, IS TIED TO
THE TYPED BLOCK THAT HANDS ITS STATEMENT ON; so it is good, at no error.

The block. `ChainEnd.chainEnd` (Johnson/Desc/ChainEnd.lean): one text for the last block of each of
a file's three chains: where the chain is sealed it declares the one round "SEAL", which holds and
draws nothing; it decides the chain's own named clauses on the carried record, and hands the record
on.

What it decides is a law of its own files: `ChainEnd.chainEnd_decide_iff`
(Johnson/Desc/ChainEndExact.lean): its `decide` returns a record if and only if every clause holds,
and then the record that it was handed.

What is said. `chainEnd_tie`: as a piece, at any stretch, rounds put back
and errors, with the extractor that hands the witness back, it is tied (`PieceTie`,
Johnson/Desc/Sound/TypedRow.lean) to `KObj.BK.pass A`, at every joint A and every reading of
statements that reads no tree from the block's place on. `chainEnd_good`: so it is good between the
joint's condition and relation, read, and themselves.
Trials. By `chainEnd_decide_iff` the block is no silly member: it refuses wherever a clause fails.
The tie does not use that: a chain's end adds nothing to what is claimed, and drops nothing.

Limits. What the clauses buy (that nothing is left untested) is not used and not stated here. That
the stretch laid here is the file's is `Three.Fits`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ChainEndExact
import Johnson.Desc.Sound.PassTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.ChainEnd
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- A chain's last block with its stretch; the extractor hands the witness back. -/
abbrev endPiece (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds)) :
    Piece C F S Cl W :=
  ⟨ChainEnd.chainEnd chain piece sealed inFront asks, base, ds, back, fun _ _ w => w, err⟩

/-- **A chain's last block is tied to the typed block that hands its statement on.** -/
theorem chainEnd_tie (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds))
    (A : JK) (rd : S × F.E.Str → A.X × A.E.Str) (wr : W → A.W)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) :
    PieceTie (endPiece (Cl := Cl) chain piece sealed inFront asks base ds back err) (BK.pass A)
      rd rd wr wr :=
  passTie _ A rd wr hnd hrd (fun _ _ _ => rfl) fun s rs gs s' h =>
    ((chainEnd_decide_iff chain piece sealed inFront asks s s' rs gs).1 h).1

/-- **So it is good**, between the joint's condition and relation, read, and themselves. -/
theorem chainEnd_good (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds))
    (A : JK) (rd : S × F.E.Str → A.X × A.E.Str) (wr : W → A.W)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) :
    ((endPiece (Cl := Cl) chain piece sealed inFront asks base ds back err).bk
      (fun a => A.on (rd a)) (fun a => A.on (rd a)) (fun a w => A.relR (rd a) (wr w))
      (fun a w => A.relR (rd a) (wr w))).Good :=
  goodOfTie _ (BK.pass A) rd rd wr wr (BK.pass_good A)
    (chainEnd_tie chain piece sealed inFront asks base ds back err A rd wr hnd hrd)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.chainEnd_tie
#print axioms VerifiableInference.Desc.Sound.chainEnd_good
