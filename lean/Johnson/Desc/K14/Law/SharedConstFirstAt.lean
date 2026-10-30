-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/K14/Law/SharedConstFirstAt.lean: THE SHARED TABLE's CONSTANT AT A PROOF FILE's SEAT:
    THE
FIRST TABLE's CONSTANT's FIVE (Sh.Open₁, Johnson/Desc/K14/Law/SharedConstOpenAt.lean: N₁ links Mg₁
smp₁ ms₁) AND THE CONFIGURATION's TWO (pp, E) AT OTHER FILES' TERMS: the composed meaning's
constant as a term (Johnson/P5J/MgAtAll.lean, LettersAt.lean, DecFree.lean). A definition a letter.
With it ShOpen is closed at the seat, twelve of twelve.

  Sh.open₁At h e       Open₁ at: N₁ := P5J.At.N Zp cF · links := P5J.At.links · Mg₁ := P5J.mgAtAll h
                       · smp₁ := P5J.At.smp Zp, carried along e · ms₁ := P5J.At.ms Zp Z.lay
  Sh.openAll h e       Sh.openAt at these, pp := ppAtFiles Z.pol Z.KL, E := P5J.At.EAt Z
  Sh.links_at          the letter links is Sh.linksFull
      (Johnson/Desc/K14/Law/SharedConstLinksAt.lean)
LETTERS THAT STAY: these files' head h : P5J.AtMgA o Z D r Zp Np cF x (scope, what is laid, named
tests, two conditions) with its own letters · e: the first chain's codes as these files read them
off Zp are the shared chain's parameters' codes: an equation in scope: smp₁'s type names the codes,
so the term is carried along it.
MARKS. These files' own: a member of their whole head is proved at storedPublicFiles and zGap alone (at secondHashFunction;
side library AtFullSide/Top/) (its named tests are evaluated: they
accept at the release's own three public files). JointSays at this Mg₁: four clauses through Lean;
pileOne by hpile_at9 (Johnson/Desc/AtSeats/HpileAt9.lean) under three premises; the fit of the two
tables at the joint is not shown here.
WHAT IS NOT HERE. No law.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstHeldAt
import Johnson.Desc.K14.Law.SharedConstLinksAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open VerifiableInference.OnPublicFiles (kcReq)

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The first table's constant's five, at the seat.** -/
def open₁At (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp Np
    (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    Open₁ (kcReq numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I
        P5J.At.Tok (planAt Zp Np
        (seatF o Zp Np (Desc.K14.Law.secondAt Zp Np) cF)).Q where
  N₁ := P5J.At.N Zp cF
  links := P5J.At.links
  Mg₁ := P5J.mgAtAll h
  smp₁ := e ▸ P5J.At.smp Zp
  ms₁ := P5J.At.ms Zp Z.lay

/-- **ShOpen at the seat, twelve of twelve.** -/
def openAll (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp Np
    (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    ShOpen ProofFile.InstPub (ProofFile.InstPub × First.S) (kcReq numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL)
                    (P5J.At.EAt Z)).conf.I P5J.At.Tok (planAt Zp Np (seatF o Zp Np
                    (Desc.K14.Law.secondAt Zp Np) cF)).Q :=
  openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF h.plan.shape
      (VerifiableInference.OnPublicFiles.ppAtFiles
      Z.pol Z.KL) (P5J.At.EAt Z) (open₁At h e)

/-- The letter links is the written row. -/
theorem links_at (h : P5J.AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp Np
    (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) :
    (openAll h e).links = linksFull := rfl

/-- P5J.F0T (AtTerm.lean), another file's spelling of what the verifier makes, is the seat's. -/
theorem f0T_is : P5J.F0T o Zp Np cF = (seatF o Zp Np (Desc.K14.Law.secondAt Zp Np)
    cF) := rfl

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.links_at
#print axioms Desc.K14.Law.Sh.f0T_is
