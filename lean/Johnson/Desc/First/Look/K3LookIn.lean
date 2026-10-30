-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LookIn.lean: the kind "lookup" (K3): WHAT THE TABLE OF JOINTS' PUBLIC ITEM
lookIn SAYS AT A LOOKUP's PLACE, AS A DEFINITION: a Bool on the carried record. With what it gives.

OBJECT: no text that runs: a definition, meant as the filling of the table of joints' letter
  Meaning.pub at the public item lookIn.
Used by K3At.lean, K3AttAtTable.lean, K3AttAtTableR.lean (Johnson/Desc/First/Look/) and 36 more.
LETTERS: p := the lookup's parameters at the place; arrayOf := D.arrayOf.getD p.link #[].
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

Why. The table's letter Meaning.pub is filled, at lookIn, by this item (K3Fill.lean). The lookup's
own condition in front asks, beside an open ledger with its sizes, that the record's own five are
the caller's data's (OwnIs, Johnson/Desc/First/Look/K3CallerOwn.lean). Two of the five are the open
link's: its number and its arrayOf. They are laid into this item. The three others (the chain's
codes, the live request's shape, its rows' layout) are not in this item: ownIs_of takes them as
premises; the last two come through the item «frame.liveIs» (K3LiveIs.lean).

Main names:
  `k3LookIn p arrayOf s`: k3OnIn p s (Johnson/Desc/First/Look/K3Borders.lean), and a link is open
    whose number is the place's and whose arrayOf is the given one.
  `k3LookIn_onIn`, `k3LookIn_link`: what it gives.
  `ownIs_of`: with the three others: OwnIs.

Limits. Who makes the item true in front of the lookup (the block in front of it) is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.K3CallerOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **lookIn.** -/
def k3LookIn (p : P) (arrayOf : Array (Nat × String)) (s : First.S) : Bool :=
  Desc.K3.k3OnIn p s && s.link?.any fun L => L.link == p.link && L.arrayOf == arrayOf

theorem k3LookIn_onIn {p : P} {arrayOf : Array (Nat × String)} {s : First.S}
    (h : k3LookIn p arrayOf s = true) : Desc.K3.k3OnIn p s = true := by
  unfold k3LookIn at h
  exact (Eq.mp (Bool.and_eq_true _ _) h).1

theorem k3LookIn_link {p : P} {arrayOf : Array (Nat × String)} {s : First.S}
    (h : k3LookIn p arrayOf s = true) :
    ∃ L, s.link? = some L ∧ L.link = p.link ∧ L.arrayOf = arrayOf := by
  unfold k3LookIn at h
  have h2 := (Eq.mp (Bool.and_eq_true _ _) h).2
  cases hl : s.link? with
  | none =>
    rw [hl] at h2
    simp at h2
  | some L =>
    rw [hl] at h2
    have h3 : (L.link == p.link && L.arrayOf == arrayOf) = true := h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    exact ⟨L, rfl, h3.1, h3.2⟩

/-- **The record's own five are D's**: two from lookIn, three from the chain's own. -/
theorem ownIs_of {D : Sent} {p : P} {s : First.S}
    (h : k3LookIn p (D.arrayOf.getD p.link #[]) s = true) (h1 : s.st.codes = D.codes)
    (h2 : s.live.frame.shape = D.shape) (h3 : s.live.rows.layout = D.layout) :
    OwnIs D p.link s := by
  obtain ⟨L, hl, e1, e2⟩ := k3LookIn_link h
  unfold OwnIs ownOf Sent.five
  rw [hl, h1, h2, h3]
  show some (D.codes, D.shape, D.layout, L.link, L.arrayOf) = _
  rw [e1, e2]

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.k3LookIn_link
#print axioms VerifiableInference.Desc.First.Look.ownIs_of
