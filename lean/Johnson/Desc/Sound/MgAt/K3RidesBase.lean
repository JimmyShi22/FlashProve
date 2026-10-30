--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3RidesBase.lean: the kind "lookup" (K3) AT THE TABLE OF JOINTS: THE
PREMISE hj ("the tree of the index's seat lies below the piece's base": N.index.1 < q.base) OF THE
LOOKUPS' THEOREMS ON WHAT RIDES (ridesAtR_calls_ledger, ridesAtR_digits_step and the rows above
them: Johnson/Desc/Sound/MgAt/), IN ITS OWN TEXT, FROM THE KIND's LEDGER's OWN FIELD base | hbaseS
(Johnson/Desc/Sound/MgAt/K3Owed.lean: every sampled tenant that is open in front lies below): by
Lean's own evaluation on the table the item pinI is open at each of K3's fifty borders, and the
tenant that the table books for it is the index's seat. Statements and proofs; one evaluation by
Lean's kernel. No error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints' own functions openSets, sampledIn.
USER: nobody yet.
LETTERS: N, base, l, d.

Main names: `pinIOpenB`, `pinIOpen_full`; `index_lt_of_open`; `index_lt_at`: THE PAYMENT.

Limits. One list of segments. The head's own structure HeadRestR has no such field (its hbase
speaks of the segment's first sending alone): there hj stays a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item Numbers start openSets sampledIn)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The item pinI is open at each of K3's fifty borders. -/
def pinIOpenB : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    ((openSets linksFull PS (start linksFull))[k3K l d]?.getD []).contains Item.pinI

set_option maxRecDepth 100000 in
theorem pinIOpen_full : pinIOpenB = true := by decide +kernel

/-- Where pinI is open, the index's seat is among the sampled tenants. -/
theorem index_lt_of_open (N : Numbers) {O : List Item} (hO : Item.pinI ∈ O) {base : ℕ}
    (hb : ∀ t ∈ sampledIn N O, t.1 < base) : N.index.1 < base := by
  refine hb _ ?_
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨_, hO, List.mem_singleton.2 rfl⟩

/-- **hj, FROM THE LEDGER's OWN FIELD, AT EACH OF K3's BORDERS.** -/
theorem index_lt_at (N : Numbers) {l : ℕ} (hl : l < 25) (d : Bool) {base : ℕ}
    (hb : ∀ t ∈ sampledIn N ((openSets linksFull PS (start linksFull))[k3K l d]?.getD []),
      t.1 < base) : N.index.1 < base := by
  have h := List.all_eq_true.1 pinIOpen_full l (List.mem_range.2 hl)
  have h1 := List.all_eq_true.1 h d (by cases d <;> simp)
  exact index_lt_of_open N (List.contains_iff_mem.1 h1) hb

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.pinIOpen_full
#print axioms VerifiableInference.OnPublicFiles.index_lt_of_open
#print axioms VerifiableInference.OnPublicFiles.index_lt_at
