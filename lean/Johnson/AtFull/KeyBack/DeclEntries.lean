-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/DeclEntries.lean: the key file's written declared rounds at the full size
bear, as their entries, the rounds of the three written plans.

The written declared rounds (`declKeyFull`, Johnson/HB/LLHARD/KB8/Written.lean) are the written dry
lists (`dryKeyFull`, Johnson/G/DryKeyLit.lean) turned back, round by round (`backR`). The written
plans are `keyThree` (Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean).

  `unrunD_entries`: turning written rounds back keeps their entries. General.
  `lit_parts`: the test on the three written plans (`key_lit_ok`), plan by plan.
  `decl_entries0`, `decl_entries1`, `decl_entries2`: the three equations.

By calls alone; nothing is evaluated here: `map_unrunG` (Johnson/G/Runs.lean), `unrunR_eq`,
`litOk_parts` (Johnson/Desc/Ok/NumberPrices/ByRuns.lean), `key_lit_ok`, `chainRounds_entries`
(OnBytes/Flat/HeldAll.lean).

Limits. Two written files are held against each other. That either is what the planner or the
program's dry runs make of any public files is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.HB.LLHARD.KB8.Written
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.KB8 (declKeyFull declRecsFull unrunD backR)
open Johnson.G (dryKeyRecsFull dryKeyRunsFull0 dryKeyRunsFull1 dryKeyRunsFull2 unrunR)
open Johnson.G.Runs (unrunG map_unrunG)
open VerifiableInference.Number.ByRuns (keyThree key_lit_ok litOk litOk_parts unrunR_eq)
open OnBytes.Flat.Held (chainRounds_entries)

/-- Turning written rounds back keeps their entries. -/
theorem unrunD_entries (recs : List (Fmt.Round × List Fmt.Stored)) (runs : List (Nat × Nat)) :
    (unrunD (recs.map backR) runs).map (·.entry) = (unrunR recs runs).map (·.1.entry) :=
  calc (unrunD (recs.map backR) runs).map (·.entry)
      = unrunG ((recs.map backR).map (·.entry)) runs :=
        map_unrunG (fun r : Fmt.DeclaredRound => r.entry) (recs.map backR) runs
    _ = unrunG (recs.map (·.1.entry)) runs :=
        congrArg (fun l => unrunG l runs) (List.map_map.trans rfl)
    _ = (unrunG recs runs).map (·.1.entry) :=
        (map_unrunG (fun x : Fmt.Round × List Fmt.Stored => x.1.entry) recs runs).symm
    _ = (unrunR recs runs).map (·.1.entry) := by rw [unrunR_eq]

/-- The test on the key file's three written plans says yes at each. -/
theorem lit_parts :
    litOk 32 10000 dryKeyRecsFull dryKeyRunsFull0 keyThree.A = true ∧
      litOk 32 10000 dryKeyRecsFull dryKeyRunsFull1 keyThree.B = true ∧
      litOk 32 10000 dryKeyRecsFull dryKeyRunsFull2 keyThree.C = true :=
  have h := Bool.and_eq_true_iff.1 key_lit_ok
  have h' := Bool.and_eq_true_iff.1 h.1
  ⟨h'.1, h'.2, h.2⟩

/-- The first chain's written declared rounds bear the first written plan's rounds. -/
theorem decl_entries0 : declKeyFull.1.map (·.entry) = keyThree.A.plan.plan.rounds := by
  show (unrunD (dryKeyRecsFull.map backR) dryKeyRunsFull0).map (·.entry) = _
  rw [unrunD_entries, (litOk_parts lit_parts.1).2, chainRounds_entries]

/-- The like for the shared chain. -/
theorem decl_entries1 : declKeyFull.2.1.map (·.entry) = keyThree.B.plan.plan.rounds := by
  show (unrunD (dryKeyRecsFull.map backR) dryKeyRunsFull1).map (·.entry) = _
  rw [unrunD_entries, (litOk_parts lit_parts.2.1).2, chainRounds_entries]

/-- The like for the second chain. -/
theorem decl_entries2 : declKeyFull.2.2.map (·.entry) = keyThree.C.plan.plan.rounds := by
  show (unrunD (dryKeyRecsFull.map backR) dryKeyRunsFull2).map (·.entry) = _
  rw [unrunD_entries, (litOk_parts lit_parts.2.2).2, chainRounds_entries]

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.unrunD_entries
#print axioms Johnson.AtFull.KeyBack.lit_parts
#print axioms Johnson.AtFull.KeyBack.decl_entries0
#print axioms Johnson.AtFull.KeyBack.decl_entries1
#print axioms Johnson.AtFull.KeyBack.decl_entries2
