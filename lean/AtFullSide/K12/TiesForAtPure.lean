-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesForAtPure.lean

What it proves. "One owner and one start" at the very call by which the frame's onlineProverFromPublicFiles
(Johnson/Desc/ProofFile/Honest/AtPure.lean) makes its book of random values: under the head, at the
concrete earlier hash, at the last three of the seven lists that the library's list of sendings
returns and the merges that the maker reads off the first chain: whatever book the maker returns,
the test tiesB (Johnson/Desc/ProofFile/Honest/K12/AgreeBook.lean) says yes at the folded row's
test's place, at two members, and at the request's own test's place, at three.

Names.
  ties_of_written   at every book whose entries are the written list.
  ties_for_atPure   the law.

By what. tiesB_of_ahead, ties_written (TiesAtLaid.lean in this folder). Of the authors of the honest
side of the linear claim's shared rounds (K14): bookWhole_returns_written_ahead
(AtFullSide/K14/BookWholeWritten.lean); book_same_for_atPure
(Johnson/Desc/ProofFile/Honest/K14/BookForAtPure.lean).

Limits.
- TiesAtLaid.lean's limits stand, but the one on the written sendings: here the sendings are the
  library's own list's.
- That the fifth of the seven lists is the public part's first is part of the premise hs, as in
  book_same_for_atPure.
- That onlineProverFromPublicFiles returns is not shown; nor is onlineProverFromPublicFiles opened here.
- Under the head with its place x₀ (AtMgA), at the concrete earlier hash alone. That head has
  members at the goals' two named sets of files (headMember_named,
  AtFullSide/Top/HeadMemberAtGap.lean); it is not called here.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (ProverCoinCounts bookWhole mergesByName)
open ProofFile.Honest.K12 (tiesB)
open ProofFile.Honest.K12.AtProof (placeU placeW)
open AtFullSide.K14 (rawAheadW)
open P5J (TS)

/-- The test says yes at the two places at every book whose entries are the written list. -/
theorem ties_of_written (B : ProverCoinCounts) (hA : B.ahead = rawAheadW) :
    tiesB B placeU 2 = true ∧ tiesB B placeW 3 = true :=
  ⟨(tiesB_of_ahead B { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } hA
      placeU 2).trans ties_written.1,
    (tiesB_of_ahead B { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } hA
      placeW 3).trans ties_written.2⟩

/-- **"One owner and one start" at onlineProverFromPublicFiles's own call**: under the head, at the concrete earlier
hash: at the last three of the seven lists that the library's list of sendings returns, and the
merges that the maker reads off the first chain: whatever book the maker returns, tiesB says yes at
the two places. -/
theorem ties_for_atPure {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (k0 k1 k2 e p1 p2 : Johnson.G.ChainSends)
    (hs : Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2])
    {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
      (mergesByName cF.blocksInOrder) = .ok Bk) :
    tiesB Bk placeU 2 = true ∧ tiesB Bk placeW 3 = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.book_same_for_atPure h₀ h k0 k1 k2 e p1 p2 hs).symm.trans hB)
  exact ties_of_written B₀ hA

end AtFullSide.K12

#print axioms AtFullSide.K12.ties_of_written
#print axioms AtFullSide.K12.ties_for_atPure
