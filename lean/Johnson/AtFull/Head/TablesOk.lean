-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/TablesOk.lean: the two tables of the output head's lookup (the clamp's, the
exponentials') are whole and below the prime, and so the tests of Forest.callAsk on a written table
pass at every entry of the head's lookup (Head.lookups, OnBytes/Model/HeadLayout.lean). General
laws over the library's: no row is evaluated. No sub-protocol imports this file.
  TabOk t           65,536 words, each below the prime
  fc_ok             the clamp's table (tauFCw, Johnson/Road/HeadTabs.lean)
  fe_ok             the table of exponentials, Head.tauFEOf 24 8 4 (the full size's three numbers)
  rec_ok            from the two tables to the two premises of ask_eq
                    (Johnson/Unfolds/ShapeEq.lean), at every entry of Head.lookups
After a text of this project.
Called, not typed: table_ok · word_ok (the law file
Johnson/Unfolds/Tabs.lean) · rowFC_lt · rowFE_lt · tauFEOf_eq ·
tauFELoop_toList (HeadTabs.lean).
Limits. No soundness is claimed. On hiding nothing.
-/
import Johnson.Road.HeadTabs
import Johnson.Unfolds.Tabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Head
open OnBytes OnBytes.Model
open Johnson.Unfolds (word_ok table_ok)

/-- A table is whole and below the prime. -/
def TabOk (t : Array F) : Prop := t.size = 65536 ∧ ∀ x ∈ t.toList, okF x = true

theorem fc_ok : TabOk OnBytes.Road.Hd.tauFCw :=
  table_ok Layer.rowFC 65536 fun _ ht => Nat.lt_trans (OnBytes.Road.Hd.rowFC_lt ht) (by decide)

theorem fe_ok : TabOk (Head.tauFEOf 24 8 4) := by
  have e : (Head.tauFEOf 24 8 4).toList =
      (List.range' 0 65536).map fun v => UInt64.ofNat (OnBytes.Road.Hd.rowFE v) := by
    rw [OnBytes.Road.Hd.tauFEOf_eq, OnBytes.Road.Hd.tauFELoop_toList]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← Array.length_toList, e]
    simp
  · rw [e] at hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    have hv' : v < 65536 := by
      have := (List.mem_range'_1.1 hv).2
      omega
    exact word_ok (Nat.lt_trans (OnBytes.Road.Hd.rowFE_lt hv') (by decide))

/-- From the two tables to the entries of the head's lookup. -/
theorem rec_ok (h : Head.Shape) (tauFC tauFE : Array F) (calls : List CallD) (hC : TabOk tauFC)
    (hE : TabOk tauFE) {c : Call} (hc : c ∈ (Head.lookups h tauFC tauFE calls).toList) :
    (∀ t, c.tau = some t → t.size = 2 ^ c.k) ∧ ∀ x ∈ (c.tau.getD #[]).toList, okF x = true := by
  unfold Head.lookups at hc
  simp only [List.mem_map] at hc
  obtain ⟨cd, _, rfl⟩ := hc
  by_cases h1 : (cd.kind == "FC") = true
  · have ek : cd.kind = "FC" := eq_of_beq h1
    simp only [h1, if_true]
    refine ⟨fun t ht => ?_, fun x hx => hC.2 x hx⟩
    obtain rfl : tauFC = t := Option.some.inj ht
    show tauFC.size = 2 ^ (if cd.kind == "R8" then 8 else 16)
    rw [ek]
    exact hC.1
  · by_cases h2 : (cd.kind == "FE") = true
    · have ek : cd.kind = "FE" := eq_of_beq h2
      simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
      refine ⟨fun t ht => ?_, fun x hx => hE.2 x hx⟩
      obtain rfl : tauFE = t := Option.some.inj ht
      show tauFE.size = 2 ^ (if cd.kind == "R8" then 8 else 16)
      rw [ek]
      exact hE.1
    · simp only [h1, h2, if_false, Bool.false_eq_true]
      exact ⟨fun t ht => (nomatch ht), fun x hx => absurd hx (by simp)⟩

end AtFull.Head

#print axioms AtFull.Head.fc_ok
#print axioms AtFull.Head.fe_ok
#print axioms AtFull.Head.rec_ok
