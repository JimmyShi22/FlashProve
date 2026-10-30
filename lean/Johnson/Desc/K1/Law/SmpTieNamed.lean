-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpTieNamed.lean: THE TIE BETWEEN THE READER OF SAMPLES AND THE STATEMENT's
SAMPLE ROWS (SmpTie, Johnson/Desc/K1/Law/SealedNoColl.lean), AT THE NAMED READER smpNamed cs seats
(Johnson/Desc/Sound/SmpNamed.lean): one call of smpNamed_of.

  smpTie_named      at the state's own statement and the member's fixed number numAt seats x.
  smpTie_named_at   the same with the statement and the number as letters under two equations.
PREMISES: the member's seat is in the plan's list of seats · K1.Tie holds of its shape.
What is not claimed. That a seat is in the list; the tie of a shape. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.SealedNoColl
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Slice OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc.Sound (Mem smpNamed smpNamed_of numAt)

/-- **The tie at the named reader.** -/
theorem smpTie_named {P : Type} (cs : Codes) (seats : List (ℕ × ℕ))
    (a : P × VerifiableInference.Desc.First.S) (x : Mem) (hq : x.1.seat x.2 ∈ seats)
    (hT : Tie cs (x.1.l.get x.2).1) :
    SmpTie cs (smpNamed cs seats) a x a.2.st (numAt seats x) := fun ρ v hS => by
  obtain ⟨z, h1, -, h3⟩ := smpNamed_of cs seats a x.1 x.2 hq ρ v hT hS
  exact ⟨z, h1, h3⟩

/-- The same, with the statement and the number as letters. -/
theorem smpTie_named_at {P : Type} (cs : Codes) (seats : List (ℕ × ℕ))
    (a : P × VerifiableInference.Desc.First.S) (x : Mem) (St : Statement) (o : ℕ)
    (hq : x.1.seat x.2 ∈ seats) (hT : Tie cs (x.1.l.get x.2).1) (hSt : St = a.2.st)
    (ho : numAt seats x = o) : SmpTie cs (smpNamed cs seats) a x St o := by
  subst hSt ho
  exact smpTie_named cs seats a x hq hT

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.smpTie_named
#print axioms VerifiableInference.Desc.K1.smpTie_named_at
