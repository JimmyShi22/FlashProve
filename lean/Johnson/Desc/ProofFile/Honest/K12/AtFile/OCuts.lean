-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OCuts.lean: the public test on the book `bookCutsOmega`
(K12/CutOfBookAt.lean), at whatever book the maker returns, at the shared chain's own plan and the seated
place of the test on G_omega: the second part carries o_omega and o_sp, cut as the sending cuts them.

  `place_of_four`   the seated place stands at the test's address
  `shortBook`, `placedO`   a book of the written entries outside the first chain; the written place at the
                 test's address
  `cuts_short`, `cuts_short_place`, `cuts_short_sender`   the test says yes there, by the kernel; no at the
                 written place's own address; no with the sending of o_u in the stead of o_omega's
  `carried_short`, `cuts_of_carried`   what the test reads of a book and a place
  `bookCutsOmega_head`   the statement

By what. `ahead_at` (AtFullSide/K12/TiesAtLaid.lean): the written list's entries outside the first chain are
those of `rawShortW`; `bookWhole_returns_written_ahead`, `bookWhole_same_at_laid`, as `he_at_laid`
(AtFullSide/K12/CutsAtLaid.lean) has them.

Limits. That a filling's book is the maker's at these letters is a premise (hB). The full size alone, under
the head. Nothing on completeness, on soundness or on what is hidden.
-/
import AtFullSide.K12.CutsAtLaid
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12)
open Johnson.G (codesFull2 proofSendsFull)
open H2K.Member (piOFull)
open AtFullSide.K14 (rawAheadW rawShortW)
open AtFullSide.K12 (ahead_at)
open ProofFile.Honest.K14 (SendPub sendPlace jobU jobOmega)
open ProofFile.Honest.K12.AtProof (fourOf placeO p12At_place)
open ProofFile.Honest.K12.Light (bookCutsOmega written_at_head qAt_written)

/-- The seated place stands at the test's address. -/
theorem place_of_four {N : H2U.Places4} {pO : P12} (hO : (fourOf N).O = some pO) :
    pO.place = placeO := by
  obtain ⟨nO, -, rfl⟩ := Option.map_eq_some_iff.1 hO
  exact p12At_place _ _

/-- A book of the written entries outside the first chain. -/
def shortBook : ProofFile.Honest.ProverCoinCounts :=
  { first := [], shared := [], second := [], ahead := rawShortW, cuts := [] }

/-- The written place at the test's address. -/
def placedO : P12 := { piOFull with place := placeO }

#eval realSized.map fun q => bookCutsOmega shortBook (Light.planOf q.2 q.1.shape) placedO

-- Foretold: yes. Controls: the written place's own address; o_u's sending in the stead of o_omega's.
#guard realSized.all fun q => bookCutsOmega shortBook (Light.planOf q.2 q.1.shape) placedO
#guard realSized.all fun q => !bookCutsOmega shortBook (Light.planOf q.2 q.1.shape) piOFull
#guard realSized.all fun q =>
  !Light.cutFits shortBook ⟨placeO, 1⟩ 0 ⟨sendPlace 5, 0⟩ (jobU (Light.planOf q.2 q.1.shape)) 0

theorem cuts_short :
    (realSized.all fun q => bookCutsOmega shortBook (Light.planOf q.2 q.1.shape) placedO) = true := by
  decide +kernel

theorem cuts_short_place :
    (realSized.all fun q => !bookCutsOmega shortBook (Light.planOf q.2 q.1.shape) piOFull) = true := by
  decide +kernel

theorem cuts_short_sender : (realSized.all fun q =>
    !Light.cutFits shortBook ⟨placeO, 1⟩ 0 ⟨sendPlace 5, 0⟩ (jobU (Light.planOf q.2 q.1.shape)) 0) = true := by
  decide +kernel

/-- At a book of the written entries the test's second part carries what `shortBook` says. -/
theorem carried_short (B : ProofFile.Honest.ProverCoinCounts) (hA : B.ahead = rawAheadW) :
    Light.carriedOf B ⟨placeO, 1⟩ = Light.carriedOf shortBook ⟨placeO, 1⟩ := by
  unfold Light.carriedOf
  rw [hA, ahead_at ⟨placeO, 1⟩ (by decide)]
  rfl

/-- The test reads of a book what the second part carries, and of a place its address. -/
theorem cuts_of_carried {B B' : ProofFile.Honest.ProverCoinCounts} (A : SendPub) {p q : P12} (hp : p.place = placeO)
    (hq : q.place = placeO) (hc : Light.carriedOf B ⟨placeO, 1⟩ = Light.carriedOf B' ⟨placeO, 1⟩) :
    bookCutsOmega B A p = bookCutsOmega B' A q := by
  unfold bookCutsOmega Light.cutFits
  rw [hp, hq, hc]

theorem cuts_plan (B : ProofFile.Honest.ProverCoinCounts) (A : SendPub) (p : P12) :
    bookCutsOmega B A p = bookCutsOmega B (Light.planOf A.P.codes A.P.S) p := rfl

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **`bookCutsOmega` under the head, at whatever book the maker returns.** -/
theorem bookCutsOmega_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    {Bk : ProofFile.Honest.ProverCoinCounts}
    (hB : ProofFile.Honest.bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (ProofFile.Honest.mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ h.scope h.laid).symm.trans hB)
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := cuts_short
  rw [hx] at k
  have k' : bookCutsOmega shortBook (Light.planOf codesFull2 x.shape) placedO = true := k
  rw [cuts_of_carried _ (place_of_four hO) (q := placedO) rfl (carried_short B₀ hA), cuts_plan,
    qAt_written Wr Np]
  exact k'

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.place_of_four
#print axioms ProofFile.Honest.K12.AtFile.cuts_short
#print axioms ProofFile.Honest.K12.AtFile.cuts_short_place
#print axioms ProofFile.Honest.K12.AtFile.cuts_short_sender
#print axioms ProofFile.Honest.K12.AtFile.carried_short
#print axioms ProofFile.Honest.K12.AtFile.cuts_of_carried
#print axioms ProofFile.Honest.K12.AtFile.bookCutsOmega_head
