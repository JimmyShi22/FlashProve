-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/RdAtCsHead.lean

What is here. `k4_behind_all` (Law/ElevenHead.lean) asks hRd: what rides at the border in front of
the member of the layers' own rounds (kind K4) rides at the border behind, from that member's
clause of keeps alone. Here that hypothesis is PROVED at the list of clauses that the threads' own
writer lays at the first chain's thread (`csHead`, Honest/Thread/CsHead.lean; the thread's
parameter is `ridersOf (csHead ν st R)`), at each of the twelve members 28 g + 4: of the list's 55
clauses the one on the reading own? of group g is the only one whose span holds the border 28 g +
5, and it follows from `K4KeepsM` (`riderOwn_of_keepsM`, Law/OwnOfKeeps.lean). One statement with
its proof: the list's membership written out, arithmetic, and that call.

  `rd_csHead`: from K4KeepsM s s': ridersOf (csHead ν st R) (28 * g + 4 + 1) v s', at every ν, st,
      R and every g < 12. What rides in front is not even read.

Limits. THE FULL SIZE ALONE: that file writes the list for the first chain at the full size. It
speaks of the list as it is typed there; if a clause is added whose span holds a border 28 g + 5,
the proof falls. It says nothing on whether any clause of the list is laid, stays or is enough
elsewhere. `K4KeepsM` is a hypothesis here. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnOfKeeps
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (First.S)

/-- **WHAT RIDES BEHIND K4's MEMBER, AT THE THREADS' OWN LIST OF CLAUSES, FROM THE MEMBER's CLAUSE
OF keeps ALONE.** CONDITIONAL: on K4KeepsM s s'. -/
theorem rd_csHead {W : Type} (ν : Nat) (st : Nat → First.S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {g : Nat} (hg : g < 12) (v : W)
    {s s' : First.S} (hK : K4KeepsM s s') :
    ridersOf (csHead ν st R) (28 * g + 4 + 1) v s' := by
  intro c hc hlo hhi
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, _, rfl⟩) | ⟨g', _, rfl⟩) | ⟨g', _, rfl⟩)
  · exact absurd (show 342 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 343 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 347 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 344 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · exact absurd (show 346 ≤ 28 * g + 4 + 1 from hlo) (by omega)
  · have h1 : 14 * l + 9 ≤ 28 * g + 4 + 1 := hlo
    have h2 : 28 * g + 4 + 1 ≤ 14 * l + 9 := hhi
    omega
  · have h1 : 14 * (2 * g' + 1) + 4 ≤ 28 * g + 4 + 1 := hlo
    have h2 : 28 * g + 4 + 1 ≤ 14 * (2 * g' + 1) + 9 := hhi
    omega
  · exact riderOwn_of_keepsM hK 0 0 0 v

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rd_csHead
