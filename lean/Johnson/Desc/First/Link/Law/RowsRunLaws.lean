-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsRunLaws.lean: WHAT A YES OF THE TEST `rowsMadeB`
(Johnson/Desc/First/Link/RowsRun.lean) GIVES, AND WHAT A NO REJECTS: ONE EQUATION: AT THE PROOF
FILE's PUBLIC PART, MADE AT THE SECOND HASH FUNCTION, WHERE THE DESCRIPTION's TEST protocolDataWellFormed ACCEPTS:
rowsMadeB Z IS THE NAMED CONDITION's OWN TEST P5J.rowsReadB W (Johnson/Goal/Skeleton/RowsRead.lean).
Theorems. A law file; no running text imports it.
  `sendsFrom_same`, `samplesOf_eq`, `codeIs_eq`, `radiusAt_eq`, `lengthOf_eq`, `cubeOf_eq`,
                    `cubeMax_eq`,
  `radiusOf_eq`, `oneRadius_eq`   the running file's second texts are the texts that they repeat.
  `packRun_eq`      packRun = packFrom (RowsFrom.lean).
  `firstRun_eq`     firstRun = rowsFrom, then the first proof chain's rows' sampled messages.
  `planned_of_theLive`   where protocolDataWellFormed accepts at secondHashFunction the program `verify-on-bytes`'s planner
                    returns at the files' own digest (planned_of_live · plannedAtO_older ·
                    plannedAt_at · planned_eq).
  `rowsMade_eq`     ProofFile.pubPlain secondHashFunction W.pol W.lay W.KL = .ok Z · protocolDataWellFormedAt secondHashFunction (asDescriptionFiles W) =
                    true ⊢ rowsMadeB Z = P5J.rowsReadB W.
  `rowsRead_of_yes`   so a yes gives P5J.rowsRead W. `no_of_no`: and a no is given just where it
                    fails: IDLE where the live test itself asks rowsMadeB: see there.
  `rowsRead_of_laid'`   in the join's letters: under LaidAt.

Limits. At secondHashFunction. THAT THE VERIFIER ASKS rowsMadeB IS NOT SAID HERE: it is a premise. Nothing on
what a radius means. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsOfMade
import Johnson.Goal.Skeleton.RowsRead
import Johnson.Goal.Reads.SevenAtLive
import OnBytes.Tie.ChainsAtCfg
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem sendsFrom_same (c : Configured) :
    Johnson.G.sendsFrom c = VerifiableInference.Number.sendsFrom c := rfl

theorem samplesOf_eq : samplesOf = Call.sendSamples := by
  funext c
  cases c <;> rfl

theorem codeIs_eq : codeIs = sameCode := rfl

theorem radiusAt_eq : radiusAt = radiusIn := rfl

theorem lengthOf_eq : lengthOf = Johnson.Pack.aOf := rfl

theorem cubeOf_eq : cubeOf = Johnson.Pack.bitsZ := rfl

theorem cubeMax_eq : cubeMax = Johnson.Pack.bMax := rfl

theorem radiusOf_eq : radiusOf = radiusFor := rfl

theorem oneRadius_eq : oneRadius = P5T.radOneB := rfl

theorem packRun_eq (c : Configured) (o : List Nat) (n : Nat) (A : Nat → Arm) :
    packRun c o n A = packFrom c o n A := by
  unfold packRun packFrom
  rw [samplesOf_eq, radiusOf_eq, cubeMax_eq, sendsFrom_same]

theorem firstRun_eq (c : Configured) (o : List Nat) (n : Nat) (A : Nat → Arm) :
    firstRun c o n A =
      (rowsFrom c o n A).map fun rows => (P5T.firstRows rows).flatMap (·.sampled) := by
  unfold firstRun rowsFrom
  rw [packRun_eq, sendsFrom_same]
  cases VerifiableInference.Number.sendsFrom c with
  | error e => rfl
  | ok sends =>
    cases packFrom c o n A with
    | error e => rfl
    | ok pack =>
      simp only [bind, Except.bind, Except.map, pure, Except.pure]
      split
      · simp only [Except.map, P5T.firstRows, List.filter_map, List.flatMap_map]
        rfl
      · rfl

/-- Where protocolDataWellFormed accepts, `verify-on-bytes`'s planner returns at the files' own digest. -/
theorem planned_of_theLive {pol lay KL : ByteArray}
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction ⟨pol, lay, KL⟩ = true) :
    ∃ p, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p := by
  obtain ⟨p, hp, hb⟩ := FlashProve.planned_of_live OnBytes.secondHashFunction ⟨pol, lay, KL⟩ hl
  rw [VerifiableInference.PlanWritten.plannedAtO_older] at hp
  rw [OnBytes.Tie.planned_eq]
  exact ⟨_, OnBytes.Tie.plannedAt_at VerifiableInference.Desc.theCfg_size
    (configurationDigest_size _) hb hp⟩

/-- **The test is the named condition's own.** -/
theorem rowsMade_eq {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles W) = true) :
    rowsMadeB Z = P5J.rowsReadB W := by
  obtain ⟨p, hp⟩ := planned_of_theLive (pol := W.pol) (lay := W.lay) (KL := W.KL) hl
  unfold rowsMadeB P5J.rowsReadB
  rw [firstRun_eq, rows_of_made h hp, oneRadius_eq]
  cases rowsFrom Z.made.p.chains.made
    (List.replicate Z.made.p.chains.made.sized.proof.request.link.length 1)
    (Z.made.p.X.NGr + 1) (armOf Z.made.p.X) <;> rfl

/-- **A yes gives the named condition.** -/
theorem rowsRead_of_yes {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles W) = true)
    (hB : rowsMadeB Z = true) : P5J.rowsRead W := by
  unfold P5J.rowsRead
  rw [← rowsMade_eq h hl]
  exact hB

/-- **A no is given just where the named condition fails.** IDLE WHERE THE LIVE TEST ITSELF ASKS
rowsMadeB (Johnson/Desc/Laid/ProofAsks.lean): its premise hl then gives rowsMadeB Z = true, and both
sides are false. Nothing uses it. -/
theorem no_of_no {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles W) = true) :
    rowsMadeB Z = false ↔ ¬ P5J.rowsRead W := by
  unfold P5J.rowsRead
  rw [← rowsMade_eq h hl]
  cases rowsMadeB Z <;> simp

end VerifiableInference.Desc.LinkJoin

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- In the join's letters: under "laid", from protocolDataWellFormed and the test's yes at the letter Zp. -/
theorem rowsRead_of_laid' {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hB : VerifiableInference.Desc.LinkJoin.rowsMadeB Zp = true) : rowsRead Z :=
  VerifiableInference.Desc.LinkJoin.rowsRead_of_yes L.pub hl hB

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.packRun_eq
#print axioms VerifiableInference.Desc.LinkJoin.firstRun_eq
#print axioms VerifiableInference.Desc.LinkJoin.planned_of_theLive
#print axioms VerifiableInference.Desc.LinkJoin.rowsMade_eq
#print axioms VerifiableInference.Desc.LinkJoin.rowsRead_of_yes
#print axioms VerifiableInference.Desc.LinkJoin.no_of_no
#print axioms P5J.rowsRead_of_laid'
