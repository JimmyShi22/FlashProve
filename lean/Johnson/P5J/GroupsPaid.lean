-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/GroupsPaid.lean: WHAT THE NAMED TEST "groups" OF PlanOk REALLY ASKS: TWO MEMBERSHIPS. One definition, two theorems.
  At.endsThere Zp cF : Bool: the index masks' and W's (tree, tenant), as the table's numbers name them, are entries' of the plan's seats with a sample.
  At.groups_is: groupsP N n pseats = endsThere, AT EVERY n: at numbers made off the same seats the "all" over the groups is true by the make (groupsP_numbersOf): SO AN ACCEPT OF "groups" IS NO EXAMPLE OF ANYTHING ON THE GROUPS.
  At.PlanOk.of_tests': PlanOk, in scope, at OnBytes.secondHashFunction, from LaidAt and: namedThere · named · fit · endsThere · radii.
Limits. It shows no test to accept. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidPaid
import Johnson.P5T.GroupsByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- The two memberships. -/
def endsThere (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) : Bool :=
  (((pseats Zp).filter (·.smpd)).map (·.seat)).contains (N Zp cF).index &&
    (((pseats Zp).filter (·.smpd)).map (·.seat)).contains (N Zp cF).w

/-- **"groups" is these two, at every number of groups.** -/
theorem groups_is (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (n : ℕ) :
    P5T.groupsP (N Zp cF) n (pseats Zp) = endsThere Zp cF :=
  P5T.groupsP_numbersOf (N Zp cF) n (pseats Zp) rfl

theorem PlanOk.of_tests' {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (there : Meaning.namedThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
    (named : seatsNamedC (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) (num Zp) (arr Zp) (N Zp cF) = true)
    (fit : P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (cs Zp) (pseats Zp) = true)
    (ends : endsThere Zp cF = true)
    (radii : P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (rad Zp Z.lay) (pseats Zp) = true) :
    PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay :=
  PlanOk.of_tests hZ hR L there named fit ((groups_is Zp cF _).trans ends) radii

end P5J.At

#print axioms P5J.At.groups_is
#print axioms P5J.At.PlanOk.of_tests'
