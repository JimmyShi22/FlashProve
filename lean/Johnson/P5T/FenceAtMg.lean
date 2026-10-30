-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/FenceAtMg.lean: THE TABLE's TEST `fenceFit` AT THE NUMBERS IN WHICH A KIND's LAW ENDS
(`At.N Zp cF`, Johnson/P5J/LettersAt.lean), FROM THE ONE HEAD `AtMg` (Johnson/P5J/AtMg.lean)
ALONE. Three theorems. A joining: nothing is evaluated here.
Why. A law on the first chain that takes "`fenceFit N links ps = true`" as a premise is called at
`N := At.N Zp cF`, `links := fullLinks`, `ps := At.ps`, under the head `h : AtMg o Z D r Zp Np
cF`. With this file that premise is paid by h.
  `LaidAt.laidPOf`: the structure "the verifier's own value is laid" gives back the equation that
  it was opened from: `proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)`: by `laidPOf_of`
  (Johnson/Desc/Laid/ProofFullLaw.lean) at its fields value, planOk, data, asks, run.
  `AtMg.pins`: the two entry tests on the written values accept AT THE HEAD's OWN F AND Zp:
  `madeRow Zp = true` and `cutRow (F0T o Zp Np cF) Zp = true`: by `asks_pins`
  (Johnson/Desc/Laid/ProofAsksLaw2.lean) at the field asks; the guard on the key is paid in scope
  (`key_in_scope_pure`, Johnson/Goal/Numbers/KeyInScope.lean).
  `AtMg.fence`: **`fenceFit (At.N Zp cF) fullLinks At.ps = true`**: by `fence_in_scope`
  (Johnson/P5T/FenceTie.lean) and `At.told_is`.
Limits. IT STANDS OVER THE VERIFIER's LIST OF ENTRY TESTS AS THIS LIBRARY HAS IT ALONE
(`LPFD.lawsAsk` with fourteen rows): over a list without `madeRow` and `cutRow` `asks_pins` does
not exist. Whether `AtMg`
can be met at the release's own files is not shown here. The full size alone. No probability: no
soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceTie
import Johnson.P5J.AtMg
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (fenceFit possAt)
open VerifiableInference.PlanWritten (pinnedAt_of_row cut_of_row key_in_scope_pure)
open OnBytes.Maker (WholeD)

/-- "The value is laid", as a structure, gives back the equation that it was opened from. -/
theorem LaidAt.laidPOf {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt o pol lay KL D r Zp Np cF) : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r) := by
  rw [L.run]
  exact LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The two entry tests on the written values accept at the head's own F and Zp. -/
theorem AtMg.pins (h : AtMg o Z D r Zp Np cF) :
    PlanWritten.madeRow Zp = true ∧ PlanWritten.cutRow (F0T o Zp Np cF) Zp = true := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  exact LPFD.asks_pins h.laid.asks hZ (decide_eq_true (key_in_scope_pure h.scope hZ))

/-- **The table's test on the fence accepts at the numbers in which a kind's law ends.** -/
theorem AtMg.fence (h : AtMg o Z D r Zp Np cF) : fenceFit (At.N Zp cF) fullLinks At.ps = true := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, hc⟩ := h.pins
  have e := P5T.fence_in_scope h.scope hZ (pinnedAt_of_row (by rw [hm, Bool.or_true]))
    h.laid.laidPOf (cut_of_row hc).1 (At.shape Zp) (possAt cF.blocksInOrder At.links.length)
    At.links.length
  unfold At.N At.ps At.pseats
  rw [At.told_is]
  exact e

end P5J

#print axioms P5J.LaidAt.laidPOf
#print axioms P5J.AtMg.pins
#print axioms P5J.AtMg.fence
