-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/CutIsOfLaid.lean: in scope, where the value is laid, the test on the three
chains' cuts has accepted whole. One theorem with its proof, and one corollary. It compiles over the
proof file's entry tests (`LPFD.lawsAsk`) as a list of thirteen rows and over the list of fourteen,
which this tree has (GLOSSARY.md, "entry tests").

Why. `P5J.pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean) hands on the first chain's cut
alone. Row 10 of the entry tests asks more: `PlanWritten.cutRow F _` is `PlanWritten.cutIs F`, the
comparison of all three chains' cuts with the written ones. The condition for kind K1 in other files
takes `cutIs` whole.

Main names. Z: the three public files. L: the value is laid at the letters o · D · r · Zp · Np · cF.
  `cutIs_of_laid`: `cutIs (F0T o Zp Np cF) = true`.
  `cuts_of_laid`: the three equations that it unfolds to (`PlanWritten.cutIs_eq`).

Limits. The pin is moved into «laid», not paid: «laid» holds that the fourteen entry tests accept,
and this is what the tenth of them says at the full size's key.
Whether a value is laid at any public files is not shown here. The full size alone. Nothing on
soundness by itself.

-/
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (cutIs cutIs_eq cutOf cutFirstFull cutSharedFull
  cutSecondFull keyOfScan fullKey key_in_scope_pure)
open OnBytes.Maker (WholeD)

/-- **In scope, where the value is laid, the test on the three cuts has accepted**: row 10 of the
entry tests' list of thirteen rows, whole. -/
theorem cutIs_of_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : cutIs (F0T o Zp Np cF) = true := by
  have hk : keyOfScan Zp.p.X.P = fullKey := key_in_scope_pure hZ L.pub
  exact (LPFD.asks_pins L.asks L.pub (decide_eq_true hk)).2

/-- The three chains' cuts are the written ones. -/
theorem cuts_of_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    cutOf (F0T o Zp Np cF).first.blocksInOrder = cutFirstFull ∧
      cutOf (F0T o Zp Np cF).shared.blocksInOrder = cutSharedFull ∧
      cutOf (F0T o Zp Np cF).second.blocksInOrder = cutSecondFull :=
  cutIs_eq (cutIs_of_laid hZ L)

end P5J

#print axioms P5J.cutIs_of_laid
#print axioms P5J.cuts_of_laid
