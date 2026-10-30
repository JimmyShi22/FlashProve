-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/InputAtTrace.lean: the honest side of the smallness test (K8): TWO
BRIDGES FROM FACTS ON A TRACE TO TWO PREMISES OF THE RECORD `K8TwoAt` AS
AtFullSide/K8/TwoAtFullOwners.lean ASKS THEM: AT THE READER OF CELLS `cellsC X T`
(Johnson/HonestTrace/DigitsAtTrace.lean) AND THE PLACE's OWN LIST `K3.matsOwn X l`: hOwn's body
(`OwnersAgree`, Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanWide.lean, of other authors) AND
hsmall's body. Two theorems; no definition. A public record X, a trace T and a number l as letters:
no thread, no run, no Script, no witness, no coin.

  **`own_of_trace`** from `PlanOwners X` (Johnson/Desc/ProofFile/Honest/K3/Law/WitOwnerFull.lean:
                    public: the place's own list is the list by names, at each of the 25), `PartsFit
                    X` (public) and `BorrowedSame X T` (ON THE TRACE): at the list's key the reader
                    answers as at the segment's own (l, label): by the sealed `cellOf_owner`
                    (Johnson/HonestTrace/CellOfOwner.lean)
  **`small_of_trace`** from `PlanOwners X`, `NamesFit X T` and `MeetsAll X i x T` (ON THE TRACE):
                    the integers that `cellsAtOf` reads through that list lie inside the window: by
                    the sealed `cellsAtOf_matsOf` (DigitsAtTrace.lean) and the field small
BorrowedSame, NamesFit and MeetsAll are premises on the trace, proved here of no trace: in front of
a sentence on hiding none of them stands as a bare premise.
No option is raised; one instance is taken away, as in the files beneath. Tactics that search:
`norm_num` on one line, on two numbers; `simp only`, with its lemmas named, on one line.
Limits. Implications. That an input's reader is `cellsC X T` at a trace with these facts is not said
here. PlanOwners is shown here of no X. It stands over TiePlanWide.lean, of another house, which is
on no row, and over what lies beneath that file. Counted nowhere.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanWide
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull
import Johnson.HonestTrace.CellOfOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.HonestTrace
open OnBytes.Model (lbz)
open Inst.Model (Instance ppref)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **hOwn's body at a trace's reader of cells.** BorrowedSame is a premise on the trace. -/
theorem own_of_trace (O : K3.PlanOwners X) (N : PartsFit X) (B : BorrowedSame X T) {l : ℕ}
    (hl : l < 25) : K1.OwnersAgree Sz.ref (cellsC X T) (K3.matsOwn X l) l := by
  intro mu σ μ hm
  obtain ⟨σ', hσ, h2⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨μ', hμ', e⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hσ12 : Seg.ofNo 12 l = some σ' := hσ
  obtain ⟨hB, hno⟩ := Seg.of_ofNo hσ12
  have hn : MatName.no? 3 1 1 4 σ' μ' = some mu := no?_of_nameNo Sz.ref hμ'
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 (MatName.mem_all_of_no? hn)
  obtain rfl : a = mu := Option.some.inj ((all_no_ref σ' ha).symm.trans hn)
  refine ⟨((Sz.ref.owner σ' μ').1.no 12, (Sz.ref.owner σ' μ').2.label, 0), ?_, fun r c _ _ => ?_⟩
  · rw [O l hl]
    unfold matsOf
    rw [hσ12]
    simp only [(parts_at N hσ12).1, List.getElem?_map, ha, Option.map_some]
  · show cellOf X T ((Sz.ref.owner σ' μ').1.no 12) (Sz.ref.owner σ' μ').2.label r (0 + c) =
      cellOf X T l μ'.label r c
    rw [Nat.zero_add, ← hno]
    exact (cellOf_owner N B hB ha r c).symm

/-- **hsmall's body at a trace's reader of cells.** NamesFit and MeetsAll are premises on the
trace. -/
theorem small_of_trace (O : K3.PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T) {l : ℕ}
    (hl : l < 25) (μ r c : ℕ) :
    |cellsAtOf (cellsC X T) (K3.matsOwn X l) μ r c| < 2 * ((2 ^ lbz : ℕ) : ℤ) := by
  rw [O l hl, cellsAtOf_matsOf N M hl]
  refine lt_of_lt_of_le (M.small l μ r c) ?_
  show (129 : ℤ) ≤ 2 * ((2 ^ 17 : ℕ) : ℤ)
  norm_num

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.own_of_trace
#print axioms ProofFile.Honest.K8.small_of_trace
