-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/DecFree.lean: THE ONE DECODER OF THE COMMITTED TABLE READS NEITHER THE CODING E NOR THE
TABLE pp OF SCALES AND POLICY; AND BOTH ARE LAID AT THE TOP STATEMENTS' OWN TERMS. Definitions and
theorems, proved.

`dtK E …` (Johnson/P5J/AtTerm.lean) and `At.decT … E hs` (LettersAt.lean) take a parameter E :
`Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)`: how an honest prover holds, encodes
and samples an index (OnBytes/Flat/FilesAt.lean). The decoder uses E in one place: "which matrix
does a decoded message hold?" (`heldFull`, Johnson/Desc/Sound/DataAlong.lean), which is the field
held of the configuration (`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean): "the claims' matrix of the
message, where it is in range". That field reads the claims' `mat` and `inRange` alone, and these
read neither E nor pp (`claimsLedgerOnAt`, Johnson/Top/H/TargetAtPolicy.lean: pp stands in `Rel`
alone).
  `heldAlong_free`, `heldFull_free`: so, through Lean: at any two pp, pp' and any two codings the
    function is one.
  `dtK_free`, `At.decT_free`: **the decoder is one at every coding and every pp.**
  `nums_full_ref`: `numsFull` (Johnson/Flat/ClaimsSizes.lean) and `numsRef`
    (Johnson/Flat/ThreeFull.lean) are two names of one pair of numbers.
  `pp_of_reads`: what the reader of the public files returns is `ppAtFiles Z.pol Z.KL`
    (Johnson/Flat/PolicyAtFrame.lean).
  `At.EAt Z`: THE TOP STATEMENTS' OWN CODING, `FlashProve.theCoding (VerifierAndGoals.asDescriptionFiles Z)`
    (Johnson/Goal/Description/Coding.lean), at the type that the decoder takes.
  `At.decTAt Z …`: the decoder at that coding: no parameter E, no parameter pp. `At.decT_is`: at
    every E it is that one.
Limits. Nothing is said of the other places in which E is read (the honest side of the top
statements' configuration). Nothing on soundness.

-/
import Johnson.P5J.LettersAt
import Johnson.Goal.Description.Coding
import Johnson.Goal.Tie.ReadThruHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Desc.Plain

theorem heldAlong_free (p : Par) (err eM : Nat) {D₀ : DecR} (e : decROfS p.S.fold eM = D₀)
    (N : MatrixNums) (pp pp' : Inst.Model.ScalesAndPolicy) (R : D₀.RelationsAndEncoding (claimsReqAt D₀ N pp))
    (R' : D₀.RelationsAndEncoding (claimsReqAt D₀ N pp')) :
    heldAlong p err eM e (claimsReqAt D₀ N pp) R =
      heldAlong p err eM e (claimsReqAt D₀ N pp') R' := by
  subst e
  rfl

theorem heldFull_free (p : Par) (err sb : Nat)
    (h : p.S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩) (N : MatrixNums)
    (pp pp' : Inst.Model.ScalesAndPolicy) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp))
    (E' : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp')) :
    heldFull p err sb h N pp E = heldFull p err sb h N pp' E' :=
  heldAlong_free p err 2852142980 _ N pp pp' _ _

end Desc.K14.Law

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Slice
open VerifiableInference.OnPublicFiles (numsRef ppAtFiles ppAtFiles_of_read)
open Desc.K14 (p14Of beforePointOf)
open Desc.K14.Law (fullShapeB heldFull_free)

/-- **The decoder is one at every coding and every table of scales and policy.** -/
theorem dtK_free {pp pp' : Inst.Model.ScalesAndPolicy}
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (E' : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp')) (o : ProofFile.SecondHashFunctionArgument)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) (err : ℕ) :
    dtK E o Zp Np cF hs err = dtK E' o Zp Np cF hs err := by
  unfold dtK
  rw [heldFull_free _ _ _ _ _ pp pp' E E']
  rfl

theorem nums_full_ref : numsFull = numsRef := rfl

theorem pp_of_reads (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : VerifierAndGoals.readFiles Z = .ok pp) :
    pp = ppAtFiles Z.pol Z.KL := (ppAtFiles_of_read hr).symm

namespace At

/-- **The top statements' own coding**, at the type that the decoder takes. -/
noncomputable def EAt (Z : VerifierAndGoals.PublicFiles) :
    Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL)) :=
  FlashProve.theCoding (VerifierAndGoals.asDescriptionFiles Z)

/-- **The one decoder, closed**: at the top statements' own coding. -/
noncomputable def decTAt (Z : VerifierAndGoals.PublicFiles) (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) :
    (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM numsFull) :=
  decT o Zp Np cF (EAt Z) hs

theorem decT_free {pp pp' : Inst.Model.ScalesAndPolicy}
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (E' : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp')) (o : ProofFile.SecondHashFunctionArgument)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) :
    decT o Zp Np cF E hs = decT o Zp Np cF E' hs :=
  dtK_free E E' o Zp Np cF hs 0

/-- At every coding the decoder is the closed one. -/
theorem decT_is (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) (o : ProofFile.SecondHashFunctionArgument)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) :
    decT o Zp Np cF E hs = decTAt Z o Zp Np cF hs :=
  decT_free E (EAt Z) o Zp Np cF hs

end At
end P5J

#print axioms Desc.K14.Law.heldAlong_free
#print axioms P5J.dtK_free
#print axioms P5J.nums_full_ref
#print axioms P5J.pp_of_reads
#print axioms P5J.At.decT_is
