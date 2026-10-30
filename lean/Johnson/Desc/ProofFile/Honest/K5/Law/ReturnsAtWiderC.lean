-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsAtWiderC.lean: A LAW ON TWO WRITTEN FILLINGS; NO THREAD
STANDS IN IT. WHEREVER THE DESCRIPTION OPENS (`IM.Open`): WHAT THE FRAME's MAKER onlineProverFromPublicFiles ASKS OF A
FILLING (`MakerAsks`, ReturnsOf.lean) HOLDS OF `widerFillOwnC own₀ L I o S O`
(Honest/AtPureWiderK10.lean: `widerFillOwn` with the closings of the segments, the kind K10, as an
eleventh list) WHERE IT HOLDS OF `widerFillOwn` AT THE SAME LETTERS. One theorem; no definition.

  `makerAsks_ownC_of_own`  Op: the description F opens at the public part Z; a: `MakerAsks` at
                           `widerFillOwn` ⊢ `MakerAsks` at `widerFillOwnC`: general in own₀, L, I

How. `widerFillOwnC` is `widerFillOwn` with one list more behind its ten; its other fields are
`widerFillOwn`'s. Of the four things that the maker asks three do not read the lists: they are
handed on. The first goes list by list (`strays_firstOf_iff`, ReturnsOf.lean): the ten from the
premise; the eleventh by its authors' `closeLotAt_clean` (Honest/AtPureWiderK10Places.lean), which
wants the opening alone. What follows under the head at `fullIn`: ReturnsAtWiderCFullIn.lean.

Limits. IT NAMES WRITTEN FILLINGS: at a filling with more lists all is to be had anew, by this
lemma's way. An implication: Op and a are premises. `MakerAsks` forbids halves that stray, it does
not ask for halves. Nothing here says that onlineProverFromPublicFiles or `ready` returns at either filling. All limits
of AtPureWiderK10.lean and AtPureWiderK10Places.lean hold.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Places
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Chain FileDescription)

/-- **WHAT THE MAKER ASKS, AT THE FILLING WITH THE CLOSINGS, FROM WHAT IT ASKS AT THE ONE WITHOUT.**
CONDITIONAL: Op: the description F opens at the public part Z; a: `MakerAsks` at `widerFillOwn`. -/
theorem makerAsks_ownC_of_own {W₀ X : Type} (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {G : Ground}
    {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (Op : IM.Open o' pol lay KL F Z Bs base c Sh Se)
    (a : MakerAsks (widerFillOwn own₀ L I o S O) Z G F) :
    MakerAsks (widerFillOwnC own₀ L I o S O) Z G F := by
  refine ⟨(strays_firstOf_iff F.first.blocksInOrder Z G _).2 fun M hM => ?_, a.shared, a.second, a.range⟩
  rw [widerFillOwnC_lots] at hM
  rcases List.mem_append.1 hM with h1 | h1
  · exact (strays_firstOf_iff F.first.blocksInOrder Z G _).1 a.first M h1
  · obtain rfl := List.mem_singleton.1 h1
    exact closeLotAt_clean I S G Op

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.makerAsks_ownC_of_own
