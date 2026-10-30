-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10Riders.lean (kind K10): THE FIELD "back" OF `K10CondAt`
(KindK10.lean, beside this file: the fifth tie of `TiedAtR`, word for word) FROM THE TABLE's
RULE ON RIDERS: WHAT IS LEFT TO THIS KIND IS ONE SENTENCE AT ONE WITNESS. One statement and its
proof.

Why. The fifth tie says: an item that is open at border k and that sub-protocol k does not close
holds in front, of the witness that the piece's extractor makes, if all that is open behind holds of
the witness behind. The table's files split it (`t5R_of_sides`,
Johnson/Desc/Sound/BordersSidesOnR.lean): (1) a rider reads of the witness only what the table says
(`ReadsOkAtQR`: no kind's); (2) what riders read is clear of what rows lay (`RidersClearQ`: a fact
on the table); (3) the piece's extractor is the table's (`extQAt`); (4) WHAT HOLDS BEHIND HOLDS IN
FRONT AT ONE WITNESS: the kind's own.
  `k10_back_of_sides`: at a piece q₀ with the table's extractor at number k laid in by
    `Piece.withMap`: from (1), (2) and (4): `K10CondAt`'s field back, to the letter. (3) holds by
    `withMap_ext`.
By Lean's evaluator at the written lists, AT ALL 25 PLACES of the kind K10, the riders (open at the
border; not among what the sub-protocol closes or reads; not "no mark") are of FIVE sorts: the
stored table's pin; the pile; the later links' constraints; the index masks' message's pin; AND, at
the 13 links 0, 2, .., 22 and 24, the link's own pending claim on the weights (the item "wo").

The sentence (4) runs over every rider.
BY READING, NOT SHOWN: the fifth sort's sentence reads the index
masks' message's ledger, and K10's step closes its members' ledgers: so at these 13 places (4) is
not to be had at a state whose index masks' message is a member of the link's group. Whether it is
to be had where that message is a member of no group is not shown either.
Limits. (1), (2) and (4) are premises here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.KindK10
import Johnson.Desc.Sound.BordersSidesOnR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj Johnson.Pack
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart start)

section
variable (cs : OnBytes.Codes) {Xi Pz Cells Tok Cl : Type} {F : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pz × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : Pz × VerifiableInference.Desc.First.S → Tok)

/-- **THE FIFTH TIE AT K10, FROM THE SIDES.** -/
theorem k10_back_of_sides (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place)
    (Rch : ℕ → (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop) (k : ℕ)
    (q₀ : Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl (Wit Cells Tok MsgT))
    (hr : ReadsOkAtQR arr Nu Mg links ps (fun a => a) Rch k)
    (hc : RidersClearQ arr Nu links ps)
    (hs : ∀ a τ b w i, onQ Nu Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q₀.ior.red.out a τ = some b → onQ Nu Mg links ps (fun a => a) (k + 1) b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nu Mg (fun a => a) i b w → meansQ Nu Mg (fun a => a) i a w) :
    ∀ a τ b w i, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
      (q₀.withMap (extQAt cs G arr smp ms decT c₀ tokOf Nu links ps (fun a => a)
        k)).ior.red.out a τ = some b →
      onQ Nu Mg links ps (fun a => a) (k + 1) b →
      relQ Nu Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nu Mg (fun a => a) i a
        ((q₀.withMap (extQAt cs G arr smp ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext a τ
          w) :=
  t5R_of_sides cs G arr smp ms decT c₀ tokOf Nu Mg links ps (fun a => a) Rch k _ hr hc
    (fun a τ b w hb => withMap_ext q₀ _ a τ b w hb) hs

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_back_of_sides
