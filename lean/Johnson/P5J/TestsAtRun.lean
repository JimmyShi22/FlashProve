-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TestsAtRun.lean: THE PREMISE "tests" OF THE HEAD AT THE NAME (Johnson/P5J/AtName.lean) HAS A NAME, AND IT IS MET WHERE THE FIVE TESTS ACCEPT AT THE THREE LETTERS THAT A RUN CAN MAKE. Two definitions, two theorems. chain_free | LaidAt.chain stand in the light file Johnson/P5J/ChainFree.lean. A joint build of the files of several groups.
  At.Five Z Zp Np cF : Prop: the five named tests at letters: namedThere · seatsNamedC · seatsFitP · endsThere · radIsB, each = true.
  At.Tests Z : Prop: the five at whatever letters the laid value opens: head_at_name's premise, by name.
  (Johnson/P5J/ChainFree.lean:) chain_free: THE FIRST CHAIN READS NO SECOND HASH: from the maker's opening at ANY o (IM.Open, Johnson/IMR/SeatOpen.lean): ProofFile.onlineFirstChainAt Z = .ok c (Johnson/Desc/ProofFile/LinkAt.lean: the maker of the chain off the public part, which stands at an idle stand-in for that hash): by unfolding: the seat's field "older" is read by the description's public data alone.
  LaidAt.chain: so under LaidAt the chain's letter IS onlineFirstChainAt's value.
  tests_of_run: WHERE pubPlain secondHashFunction Z.pol Z.lay Z.KL = .ok Zp₀ · placesOfMade Zp₀.made = .ok Np₀ · onlineFirstChainAt Zp₀ = .ok cF₀ AND At.Five Z Zp₀ Np₀ cF₀: At.Tests Z. THESE THREE ARE THE LETTERS AT WHICH OUR RUN EVALUATED THE FIVE: so its accepts show the premise met at its files (the run's chain stands at the idle hash, LaidAt's at secondHashFunction).
None of the five is itself a test that verify() runs: they are named conditions with code. In scope, where protocolDataWellFormed accepts, they follow from its tests (AtNameA.lean;
`P5J.conds_of_laid`, Johnson/Goal/Skeleton/CondsOfLaid.lean:134).
Limits. It shows no test to accept. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.AtName
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain FileDescription Block)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- The five named tests, at letters. -/
def At.Five (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : Prop :=
  Meaning.namedThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true ∧
  seatsNamedC (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) (At.num Zp) (At.arr Zp)
    (At.N Zp cF) = true ∧
  P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (At.pseats Zp) = true ∧
  At.endsThere Zp cF = true ∧
  P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
    (At.rad Zp Z.lay) (At.pseats Zp) = true

/-- **The five at whatever letters the laid value opens.** -/
def At.Tests (Z : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ Zp Np cF, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF →
    At.Five Z Zp Np cF

/-- **The premise is met where the five accept at the three letters that a run can make.** -/
theorem tests_of_run {Z : VerifierAndGoals.PublicFiles} {Zp₀ : ProofFile.Pub} {Np₀ : H2U.Places4} {cF₀ : Chain TS ProofFile.Cl}
    (hp : ProofFile.pubPlain OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp₀)
    (hn : H2U.placesOfMade Zp₀.made = .ok Np₀) (hc : ProofFile.onlineFirstChainAt Zp₀ = .ok cF₀)
    (T : At.Five Z Zp₀ Np₀ cF₀) : At.Tests Z := by
  intro Zp Np cF L
  obtain rfl : Zp₀ = Zp := Except.ok.inj (hp.symm.trans L.pub)
  obtain rfl : Np₀ = Np := Except.ok.inj (hn.symm.trans L.places)
  obtain rfl : cF₀ = cF := Except.ok.inj (hc.symm.trans L.chain)
  exact T

/-- The head at the name, from the named premise. -/
theorem head_of_tests {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (T : At.Tests Z) :
    ∃ Zp Np cF, AtMg OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF :=
  head_at_name hZ hl hR T

end P5J

#print axioms P5J.tests_of_run
#print axioms P5J.head_of_tests
