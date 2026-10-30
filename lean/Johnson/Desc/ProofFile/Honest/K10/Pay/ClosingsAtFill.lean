-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/ClosingsAtFill.lean: the closing of a segment (K10): at the prover that the maker
`onlineProverFromPublicFiles` returns, the first half that stands at each closing's place is the closing's own.

The functions that play a chain take, at a sub-protocol's place, the first half of the prover's list that stands there.
`ClosingsFirst` (Honest/K10/Thr/HalfOfLot.lean) says of a list of halves that at each closing's place this first half has
one part: the move for the round "BAT", then the fold's part at the lot's job of that place. The laws on the closing's
play and on its acceptance (Honest/K10/Thr/AtThread.lean) take it as a premise.

  **`closingsFirst_of_fill`**   at any choice of fields P at which `onlineProverFromPublicFiles` returns A: where one of P's lots lays, at A's
                    public part and ground, the halves of `seatLotC`, and every lot of P either lays no half at a place of
                    the kind K10 or lays these same halves, `ClosingsFirst` holds of A's list for the first chain
  **`closingsFirst_of_last`**   the same where P's lots are a list Ls with such a lot behind it, and no lot of Ls lays a
                    half at a place of the kind K10

Limits. That `onlineProverFromPublicFiles` returns is a premise. The premises on the lots are shown here of no choice of fields. The statement
names the first half's parts alone; what these parts send is not read here. Where the public part has no closing
(`closePars` is empty) it holds for nothing.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (KindName)

variable {W₀ Rc Tr X₀ X : Type}

/-- **At the prover that `onlineProverFromPublicFiles` returns, each closing's place is served by the closing's own half**, where one lot of
the choice of fields lays `seatLotC`'s halves and no other lot lays a different half of the kind K10. -/
theorem closingsFirst_of_fill {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (readers : Local W₀ Rc Inst Tr → Readers) (rows : RowDataOf Inst) (stAt : StAtOf Inst)
    {Lc : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hL : Lc ∈ P.lots)
    (hLc : Lc.halves A.Z A.G = (seatLotC readers rows stAt).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ e ∈ M.halves A.Z A.G, e.place.kind ≠ KindName.K10) ∨
      M.halves A.Z A.G = Lc.halves A.Z A.G) :
    ClosingsFirst A.H.first readers rows stAt A.Z A.G := by
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open hA
  exact first_of_kinds O readers rows stAt A.G (atPure_ok hA).2.2.2.2.2.2.2.1 hL hLc ho

/-- The same where the lot with the closings stands last, behind lots that lay no half of the kind K10. -/
theorem closingsFirst_of_last {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (readers : Local W₀ Rc Inst Tr → Readers) (rows : RowDataOf Inst) (stAt : StAtOf Inst)
    {Ls : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)}
    {Lc : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hP : P.lots = Ls ++ [Lc])
    (hLc : Lc.halves A.Z A.G = (seatLotC readers rows stAt).halves A.Z A.G)
    (ho : ∀ M ∈ Ls, ∀ e ∈ M.halves A.Z A.G, e.place.kind ≠ KindName.K10) :
    ClosingsFirst A.H.first readers rows stAt A.Z A.G := by
  refine closingsFirst_of_fill hA readers rows stAt (Lc := Lc) (by rw [hP]; simp) hLc ?_
  intro M hM
  rw [hP] at hM
  rcases List.mem_append.1 hM with h | h
  · exact Or.inl (ho M h)
  · rcases List.mem_singleton.1 h with rfl
    exact Or.inr rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closingsFirst_of_fill
#print axioms ProofFile.Honest.K10.closingsFirst_of_last
