-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ItemsBegun.lean: the rows that a proximity test takes in say behind the beginning
of the test what they said in front.

The laws on the batching speak at the statement behind the beginning of a test; the items of
Johnson/Desc/Means/ItemsAt.lean at the statement in front. The beginning closes the members'
ledgers, marks the group and empties its open rows: it turns no shape. So each row that the test
takes in says the same at both statements (says_begun), and the items in front hold just if the rows
taken in hold at the statement behind (items_iff_begun).

Main theorems: says_begun, allSay_begun, items_iff_begun.

What is not claimed. Nothing on the batched row. Nothing on soundness.

-/
import Johnson.Desc.Means.ItemsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group}

/-- A row that the test takes in says behind the beginning what it said in front. -/
theorem says_begun (hI : InOrder S) (g : Nat) (hG : S.groups[g]? = some G) {r : Row}
    (hr : r ∈ (Slice.runRows S G).toList) (m : Words K) :
    Says ρ (Slice.begun S g G) r m ↔ Says ρ S r m :=
  says_extends ρ (extends_begun S g G) (hI.runRows g G hG r hr) m

theorem allSay_begun (hI : InOrder S) (g : Nat) (hG : S.groups[g]? = some G) (m : Words K) :
    AllSay ρ (Slice.begun S g G) (Slice.runRows S G).toList m ↔
      AllSay ρ S (Slice.runRows S G).toList m :=
  ⟨fun h r hr => (says_begun ρ hI g hG hr m).1 (h r hr),
    fun h r hr => (says_begun ρ hI g hG hr m).2 (h r hr)⟩

/-- **The items in front of a test hold just if the rows taken in hold behind its beginning.** -/
theorem items_iff_begun (hI : InOrder S) (hK : OpenKinds S) (g : Nat)
    (hG : S.groups[g]? = some G) (m : Words K) :
    AllSay ρ (Slice.begun S g G) (Slice.runRows S G).toList m ↔
      (∀ i, OpenSays ρ S g i m) ∧ sampleItem ρ S G.members.toList m :=
  (allSay_begun ρ hI g hG m).trans (runRows_iff_items ρ hK g hG m)

end OnBytes.Means
