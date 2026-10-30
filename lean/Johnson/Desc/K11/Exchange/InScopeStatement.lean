-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/InScopeStatement.lean: WHERE THE KIND's BLOCK STANDS IN THE DESCRIPTION's
FIRST CHAIN, IN SCOPE: ONE STATEMENT: a definition of a proposition. NOTHING IS PROVED IN THIS FILE,
and it is none of the library's goals: a lemma's statement. The texts are the description's; no
prover is named.

What is said. At public files in scope, at an opening of the description's return (`IM.Open`,
Johnson/IMR/SeatOpen.lean) at the library's constant for the format's second hash function
(`OnBytes.secondHashFunction`), and where `verify-on-bytes`'s step under the name that the kind's lot looks up
is found: there are a link and a name such that, with K the kind's block AT THE LOT's NUMBERS as it
stands alone at the seat of that name at the kind's address (`IM.seatedAs`,
Johnson/IMR/SeatForm.lean; `K11.parOf`, Johnson/Desc/ProofFile/Lot/K11.lean; `IM.k11Place`,
Johnson/IMR/K11Seat.lean):
  the chain's link number 24 is that link;
  that link is also what the reader of a link off the public part alone gives at 24 (`ProofFile.linkAt`,
    Johnson/Desc/ProofFile/LinkAt.lean): the reader of which the composed meaning's data at the full
    size take their links (`P5J.At.lk`, Johnson/P5J/LettersAt.lean);
  its hearing block number 8 is K;
  THE MEMBER NUMBER 346 OF THE CHAIN's FLAT LIST IS K;
  the lot's number of the link is 24.

Why. The statements of this folder and of Honest/K11/Plays/ on a link or on a flat list take "its
block is the kind's block as it stands alone at a seat" for a premise. This is that premise, at the
description itself.

Limits. In scope alone, and at that one earlier hash. That the description returns, and that the
step's name is found, are premises. That a thread's list of members is this chain's flat list is not
said here: it is that thread's letter to lay. Nor that the public part at which some data of the
composed meaning are laid is this opening's Z. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtSeatStatement
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)

/-- The statement. P, pp, lay: the public files, what is read off them, the layout's bytes. F, Z,
Bs, base, c, A, B: the letters of the opening: c is the first chain. Not proved here; a lemma's
statement, none of the library's goals. -/
def HeadMergeInScope : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat),
    VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    (K11.sentAt? Z "H.8.call").isSome = true →
    ∃ (Lk : Link S Cl) (name : String),
      c.links[24]? = some Lk ∧ ProofFile.linkAt Z 24 = some Lk ∧
      Lk.hear[8]? =
        some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Z Bs.G₀)) name IM.k11Place) ∧
      c.blocksInOrder[346]? =
        some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Z Bs.G₀)) name IM.k11Place) ∧
      (K11.parOf Z Bs.G₀).link = 24

end Johnson.Desc.First.ForkMerge.Exchange
