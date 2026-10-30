-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsAtConstant.lean: THE NAMED EQUATIONS ON THE COMPOSED MEANING's PARAMETERS THAT
`laterAt_whole` AND `firstAt_whole` TAKE (Johnson/Road/K4/K4PinsLaterWhole.lean,
K4PinsFirstWhole.lean), ASKED OF LEAN AT THE COMPOSED MEANING's OWN CLOSED TERM:
`P5J.At.𝔇Whole` (Johnson/P5J/LettersAt4.lean; `𝔇All`, LettersAll.lean, with its
two last parameters laid). The binders are that term's; q5 is the line
as it is spent. Until here they were held against that term by reading alone. Each is a theorem of
its own, so that one that fails does not hide the others. By unfolding; one call. No draw, no count.

  `asOurs`: THE TYPE: the closed term, whose numbers of rows and columns are written `numsFull.rows`
    and `colsAt numsFull` and whose public parameters `At.X Zp`, IS TAKEN BY LEAN at hRef, 2 ^ kRef
    and Zp.p.X.
  `q1_sent` · `q2_arr` · `q3_ms` (at the radii `At.rad Zp lay`) · `q4_sent` · `q4_index` · `q5_hid`
    · `q6_seat3` · `q7_smp` (at the seats `At.seats Zp`) · `q8_noRec` (`noRec_decT`,
    Johnson/P5J/LettersAt.lean, called) · `q9_lay` · `q10_mat13` · `q11_uL`.

OBJECT: `P5J.At.𝔇Whole`. USER: Johnson/Road/K4/K4PinsFirstScope.lean; meant: the assembly of K4's
law at the constant. LETTERS: those of `𝔇Whole`.

Limits. K04_law IS NOT PROVED BY THIS. EQUATIONS OF TERMS: NOTHING SAYS THAT THE CLOSED TERM's HEAD
CAN BE MET: "the head is not shown to be meetable". The wider meaning's
further parameters (`WideData`) are no part of it: nothing on them here. IT WILL TURN WHEN THAT TERM
TURNS.
-/
import Johnson.P5J.LettersAt4
import Johnson.Road.K4.K4PinsLaterWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open VerifiableInference.Desc.First.Look (Stored.NoRec)
open VerifiableInference.Desc.Sound (MgData SeatsNamed GroupsSeated smpNamed)
open VerifiableInference.Desc.K13.Law (matOfCells)
open Inst.Model.Layout (kRef hRef)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain
              P5J.TS ProofFile.Cl)
  {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
    (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB
    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp)) (P5J.At.layout Zp) = true)
  (hN : SeatsNamed (P5J.At.arr Zp) (P5J.At.N Zp cF) (Meaning.sizesOf (P5J.At.X Zp))
    (Meaning.seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
      (Meaning.sizesOf (P5J.At.X Zp))))
  (hG : GroupsSeated (P5J.At.ms Zp lay) (P5J.At.N Zp cF))
  (x : VerifiableInference.Desc.First.Look.Place)
  (nR : ℕ)

/-- **The closed term, at K4's letters for its numbers of rows and columns and its public
parameters.** -/
def asOurs : MgData ProofFile.Inst ProofFile.InstPub ℕ hRef (2 ^ kRef) nR Zp.p.X :=
  P5J.At.𝔇Whole o Zp Np cF E hs lay hL hN hG x nR

/-- the closed term -/
local notation "𝔄" => asOurs o Zp Np cF E hs lay hL hN hG x nR

theorem q1_sent : (𝔄).sent = sentAt Zp := rfl

theorem q2_arr : (𝔄).arr = arrAt Zp := rfl

theorem q3_ms : (𝔄).ms = P5T.msAtR Zp (P5J.At.rad Zp lay) := rfl

theorem q4_sent : (𝔄).N.sent = (numbersAt Zp).sent := rfl

theorem q4_index : (𝔄).N.index = (numbersAt Zp).index := rfl

theorem q5_hid (g : ℕ) (w) : ((𝔄).H.hid w).MG g =
    Meaning.mgOf Zp.p.X.y
      (ownW (𝔄).arr (𝔄).ms (𝔄).N (Meaning.sizesOf Zp.p.X)
        (Meaning.seatBy (Meaning.fLay (sentAt Zp).layout (numAt Zp)) Zp.p.X
          (Meaning.sizesOf Zp.p.X)) (𝔄).cs w) g := rfl

theorem q6_seat3 (l j : ℕ) :
    (𝔄).seat3 l false j = P6T.seatCallsT (seatsAt Zp) (sentAt Zp) l j := rfl

theorem q7_smp : (𝔄).smp = smpNamed (𝔄).cs (P5J.At.seats Zp) := rfl

theorem q8_noRec : Stored.NoRec (𝔄).decT := P5J.At.noRec_decT o Zp Np cF E hs

theorem q9_lay : (𝔄).d1.lay = Zp.p.X.layers.wsLay := rfl

theorem q10_mat13 : (𝔄).mat13 = matOfCells nR (𝔄).P13.lin.kCol := rfl

theorem q11_uL : (𝔄).uL = uLAt Zp.p.X (namesOf (𝔄).built) := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.asOurs
#print axioms OnBytes.Road.K4.q1_sent
#print axioms OnBytes.Road.K4.q2_arr
#print axioms OnBytes.Road.K4.q3_ms
#print axioms OnBytes.Road.K4.q4_sent
#print axioms OnBytes.Road.K4.q4_index
#print axioms OnBytes.Road.K4.q5_hid
#print axioms OnBytes.Road.K4.q6_seat3
#print axioms OnBytes.Road.K4.q7_smp
#print axioms OnBytes.Road.K4.q8_noRec
#print axioms OnBytes.Road.K4.q9_lay
#print axioms OnBytes.Road.K4.q10_mat13
#print axioms OnBytes.Road.K4.q11_uL
