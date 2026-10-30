-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/PinsOfLaid.lean: in scope, where the proof file's value is laid, the two
comparisons of the plan with written values ("pins") have accepted, at the letters that the laid
value opens. One theorem with its proof.
It compiles over the proof file's entry tests (`LPFD.lawsAsk`) as a list of thirteen rows
and as one of fourteen, which this tree has.

Why. Rows 9 and 10 of either list are `madeRow` and `cutRow`, each asked at the full size's key.
`LaidAt.asks` (Johnson/P5J/LaidOpens.lean) says that every entry test accepts, at the very
description `F0T o Zp Np cF` and public part `Zp` of which the laws at the name speak. So whoever
holds a `LaidAt` in scope holds both pins in the laws' own form, and need not take them as premises.

Main name. Z: three public files. o: the second hash function. Zp Np cF: the letters.
  `pins_of_laid`: from `VerifierAndGoals.InScope Z = true` and `LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF`:
    `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true` and
    `cutOf (F0T o Zp Np cF).first.blocksInOrder = cutFirstFull`.
By four calls: `key_in_scope_pure` (Johnson/Goal/Numbers/KeyInScope.lean: in scope the key is the
full size's), `LPFD.asks_pins` (Johnson/Desc/Laid/ProofAsksLaw2.lean), `pinnedAt_of_row`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), `cut_of_row`
(Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).

Limits. Whether a value is laid at any Z under the entry tests' rows (fourteen)
is not shown here. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.LaidOpens
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.Laid.ProofAsksLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt cutOf cutFirstFull keyOfScan fullKey
  key_in_scope_pure pinnedAt_of_row cut_of_row)
open OnBytes.Maker (WholeD)

/-- **In scope, where the value is laid, the two pins have accepted**: rows 9 and 10 of the entry
tests (from thirteen rows on), at the letters that the laid value opens. -/
theorem pins_of_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true ∧
      cutOf (F0T o Zp Np cF).first.blocksInOrder = cutFirstFull := by
  have hk : keyOfScan Zp.p.X.P = fullKey := key_in_scope_pure hZ L.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins L.asks L.pub (decide_eq_true hk)
  refine ⟨pinnedAt_of_row ?_, (cut_of_row hc).1⟩
  rw [hm, Bool.or_true]

end P5J

#print axioms P5J.pins_of_laid
