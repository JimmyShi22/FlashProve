-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtMg.lean: THE ONE HEAD OF A COUNTED STATEMENT, AND THE CONSTANT. One structure, two theorems. pp is no letter: it is the files' own ppAtFiles Z.pol Z.KL, as the tops lay it. The frame alone: the constant mgAt and AtMg.tieStart stand in Johnson/P5J/MgAtConst.lean: this file hangs on no form of the composed meaning.

Why. Each kind's files end the law of their kind of sub-protocol in one form: in scope · where the verifier's own value is laid · where the named tests on the list of rounds accept · [where the facts at the fold hold] → … at the composed meaning's constant. So that all write the same dozen tokens:
  AtMg o Z D r Zp Np cF : Prop: A STRUCTURE WITH FIVE FIELDS; o: THE SECOND HASH FUNCTION, A LETTER:
    scope   VerifierAndGoals.InScope Z = true
    reads   VerifierAndGoals.readFiles Z = .ok (ppAtFiles Z.pol Z.KL): the model's public parameters are the files' own (what readFiles returns where it returns: pp_of_reads)
    laid    LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF   (Johnson/P5J/LaidOpens.lean: what "the verifier's own value is laid" holds, at Z's OWN three public files)
    plan    At.PlanOk o Zp Np cF Z.lay               (Johnson/P5J/PlanOk.lean: the named tests)
    pubOne  publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X: the two roads' public data are one
  ON o AND THE FIELD "pubOne". The description takes the second hash function as a letter o; THE TOPS' ROWS (scope_public) AND THE LIBRARY's LEMMAS ON THE SCOPE (core_of_scope and what stands on it) SPEAK OF publicOf, WHICH NAMES THE CONCRETE HASH OnBytes.secondHashFunction. LaidAt gives publicOfO o … = .ok Zp.p.X at the letter. So the tie of the two is a FIELD here, and a THEOREM AT
  o := OnBytes.secondHashFunction (AtMg.of_olderK). THE DECISION: the hash that is SAMPLED is an oracle throughout; this second hash, on the PUBLIC files, is a parameter o of the IOP as written, and the goals read it at the format's function: **THE COUNTED LAWS ARE OWED AT o := OnBytes.secondHashFunction: THERE pubOne IS A THEOREM.** The head stays general in o where that costs nothing. Whether pubOne can hold at another o is not known here.
  THE FACTS ON EVERY REACHED STATE (FoldFacts) COME BESIDE IN Johnson/P5J/AtMgR.lean, which extends this structure: no statement that ends in AtMg turns.
  (The constant under it: Johnson/P5J/MgAtConst.lean: mgAt h 𝔇₀ · Johnson/P5J/MgAtAll.lean: mgAtAll h nR, with every letter at a term.)
WHAT COMES OUT: AtMg.of_olderK (at o := OnBytes.secondHashFunction the fifth field follows from the third) · AtMg.exists_of_laid (at that hash: in scope, where readFiles returns, from the value's own "laid" and the tests: there are letters with AtMg) · AtMg.tieStart (it stands in Johnson/P5J/MgAtConst.lean): **the facts on a start (TieStart: eleven of the proof file's rows) AT mgAt's LETTER, FROM AtMg ALONE**: nine as in
Johnson/P5J/TieAtStart.lean; the two that it leaves are AtMg's own fields: scope_reads := reads · scope_public := pubOne.

Limits. A bundling and one call. The full size alone. It shows no test to accept. A MEMBER OF THE HEAD IS PROVED AT THE SECOND HASH FUNCTION OnBytes.secondHashFunction, AT TWO WRITTEN SETS OF PUBLIC FILES VerifierAndGoals.storedPublicFiles AND VerifierAndGoals.zGap, IN THE SIDE LIBRARY (AtFullSide/Top/: headMember_zFull, headMember_zGap); AT OTHER FILES OR HASHES NONE IS SHOWN. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOk
import Johnson.P5J.LaidOpens
import Johnson.P5J.DecFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain Wit)
open OnBytes.Maker (WholeD)

/-- **THE ONE HEAD.** -/
structure AtMg (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : Prop where
  scope : VerifierAndGoals.InScope Z = true
  reads : VerifierAndGoals.readFiles Z = .ok (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL)
  laid : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF
  plan : At.PlanOk o Zp Np cF Z.lay
  pubOne : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok (At.X Zp)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **At the concrete second hash function the fifth field follows from the third.** -/
theorem AtMg.of_olderK (hZ : VerifierAndGoals.InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (ok : At.PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay) :
    AtMg OnBytes.secondHashFunction Z D r Zp Np cF := by
  obtain ⟨Bs, base, O⟩ := L.opened
  have h : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  exact ⟨hZ, pp_of_reads Z hR ▸ hR, L, ok, h⟩

/-- In scope, from the value's own "laid" and the tests at the letters that it opens: the one head. -/
theorem AtMg.exists_of_laid (hZ : VerifierAndGoals.InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok (D, r))
    (hP : ∀ Zp Np cF, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      At.PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay) : ∃ Zp Np cF, AtMg OnBytes.secondHashFunction Z D r Zp Np cF := by
  obtain ⟨Zp, Np, cF, L⟩ := laid_opens hL
  exact ⟨Zp, Np, cF, AtMg.of_olderK hZ hR L (hP Zp Np cF L)⟩

end P5J

#print axioms P5J.AtMg.of_olderK
#print axioms P5J.AtMg.exists_of_laid
