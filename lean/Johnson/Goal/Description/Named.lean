-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Named.lean: the provers and the named side. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: in part true. `theNamed`, field by field (`LPFD.Full.namedH`,
Johnson/Top/Fire/Code/TieFilled.lean): the error 2^-128 and the reference instance are values that
the theorems on soundness read; the extractor finds nothing and its error is 0; the next token is
none: a place-holder. `theProvers`: fixedMessageProvers: a place-holder.
`theProversAt o`, `theNamedAt o`: over the gates at o; `theProvers`, `theNamed`: at the format's
second
hash function.
Limit. That the three hypotheses on soundness are met at this error is not shown here; where they
are proved, and how far: the head of Johnson/Goal/TopOfThree.lean, limit (1).

-/
import Johnson.Goal.Description.Coding
import Johnson.Goal.Description.Gates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

def theProversAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    (FsAtR (theClaims Zk) (theCoding Zk) G DK DP (theKeyGateAt o Zk) (theProofGateAt o Zk)
      (theLinkGateAt o Zk)).Provers :=
  Files.fixedMessageProvers _

def theNamedAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    NamedSideOfFullD (theClaims Zk) (theCoding Zk) DK DP (theKeyGateAt o Zk) (theProofGateAt o Zk)
      dsF xsF (theLinkGateAt o Zk) G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G)
      (theProversAt o Zk G DK DP) :=
  LPFD.Full.namedH (theClaims Zk) (theCoding Zk) G DK DP (theKeyGateAt o Zk) (theProofGateAt o Zk)
    (theLinkGateAt o Zk) (theProversAt o Zk G DK DP) G.z₀.1

def theProvers (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    (FsAtR (theClaims Zk) (theCoding Zk) G DK DP (theKeyGate Zk) (theProofGate Zk) (theLinkGate
        Zk)).Provers :=
  theProversAt OnBytes.secondHashFunction Zk G DK DP

def theNamed (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    NamedSideOfFullD (theClaims Zk) (theCoding Zk) DK DP (theKeyGate Zk) (theProofGate Zk) dsF xsF
        (theLinkGate Zk) G.rec₀
      G.z₀.2 (sBG G).logLeaves G.early (saltG G) (theProvers Zk G DK DP) :=
  theNamedAt OnBytes.secondHashFunction Zk G DK DP

end FlashProve
