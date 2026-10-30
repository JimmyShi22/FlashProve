-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwRoundIs.lean.
Which typed rounds of a lookup are which entries of a plan.

The relation is OnBytes.G4.EntryIs (OnBytes/G4/RoundIs.lean): the round's plain part is, up to a
bijection, msg / 24 elements of the field; its challenges are, up to a bijection, what drawE and
drawNZ say; it has no oracle position.
Main statements. entryIs_of, entryIs_none: from the two bijections and "no oracle position".
entryIs_draw, entryIs_point: a draw of one element, of a point. entryIs_r0, entryIs_rV: a sumcheck's
round 0 and its round of values. entryIs_var, entryIs_Y: a variable's short round,
with the challenge from the whole field, or from its elements other than 0. entryIs_long_ne: the
round of the sumcheck that sends all coefficients (f.n + 1 of them) is not the entry of the short
round (f.n).
What the relation lets through is said in the head of OnBytes/G4/RoundIs.lean: it counts sizes, not
which scalar is which.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwPlan
import OnBytes.G4.RoundIs
import Cb.Ld.LdPsc
import Ior.Draw

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop Cb OnBytes.G4

section
variable {E : Type}

def eUnit : Unit ≃ (Fin 0 → E) :=
  ⟨fun _ => Fin.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim0⟩
def eOne (α : Type) : α ≃ (Fin 1 → α) := (Equiv.funUnique (Fin 1) α).symm

theorem entryIs_of [Zero E] (r : Round) (wk : Nat) (name : String) (s k z : Nat)
    (hP : Nonempty (r.Plain ≃ (Fin s → E)))
    (hC : Nonempty (r.Chal ≃ drawT E k z)) (hE : IsEmpty r.Pos) : EntryIs E r
        (TwPlan.rd wk name s k z) :=
  ⟨⟨s, k, z⟩, ⟨hP, hC, hE⟩, rfl, rfl, rfl⟩

theorem entryIs_none [Zero E] (r : Round) (name : String) (s : Nat)
    (hP : Nonempty (r.Plain ≃ (Fin s → E)))
    (hC : Nonempty (r.Chal ≃ Unit)) (hE : IsEmpty r.Pos) : EntryIs E r (TwPlan.rdNone name s) :=
  ⟨⟨s, 0, 0⟩, ⟨hP, hC.elim fun c => ⟨c.trans eUnit⟩, hE⟩, rfl, rfl, rfl⟩

variable [Field E] [Fintype E]

theorem entryIs_draw (wk : Nat) (name : String) : EntryIs E (IOR.drawRound E)
    (TwPlan.rd wk name 0 1) :=
  entryIs_of _ wk name 0 1 0 ⟨eUnit⟩ ⟨eOne E⟩ inferInstance

/-- a draw from a set that is a point's, up to a bijection -/
theorem entryIs_point (D : Type) [Fintype D] [Nonempty D] (wk : Nat) (name : String) (k : Nat)
    (e : D ≃ (Fin k → E)) :
    EntryIs E (IOR.drawRound D) (TwPlan.rd wk name 0 k) :=
  entryIs_of _ wk name 0 k 0 ⟨eUnit⟩ ⟨e⟩ inferInstance

theorem entryIs_r0 (wk : Nat) : EntryIs E (pRound0 E) (TwPlan.rd wk "PSC epsilon" 1 1) :=
  entryIs_of _ wk _ 1 1 0 ⟨eOne E⟩ ⟨eOne E⟩ inferInstance

theorem entryIs_rV (A : Type) [Fintype A] : EntryIs E (pRoundV E A)
    (TwPlan.rdNone "PSC values" (Fintype.card A)) := by
  classical
  exact entryIs_none _ _ _ ⟨Equiv.arrowCongr (Fintype.equivFin A) (Equiv.refl E)⟩ ⟨Equiv.refl _⟩
      inferInstance

/-- a variable's short round: g scalars; the challenge from all of E -/
theorem entryIs_var (r : Round) (wk g : Nat) (hP : Nonempty (r.Plain ≃ (Fin g → E)))
    (hC : Nonempty (r.Chal ≃ E))
    (hE : IsEmpty r.Pos) : EntryIs E r (TwPlan.rd wk "PSC round" g 1) :=
  entryIs_of _ wk _ g 1 0 hP (hC.elim fun c => ⟨c.trans (eOne E)⟩) hE

/-- the further variable Y: g scalars; the challenge is not 0 -/
theorem entryIs_Y (r : Round) (wk g : Nat) (hP : Nonempty (r.Plain ≃ (Fin g → E)))
    (hC : Nonempty (r.Chal ≃ {x : E // x ≠ 0})) (hE : IsEmpty r.Pos) : EntryIs E r
        (TwPlan.rd wk "PSC Y" g 1 1) :=
  entryIs_of _ wk _ g 1 1 hP hC hE

theorem two_le : 2 ≤ Nat.card E := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- The round that sends all f.n + 1 coefficients (`pRound f`) is not the entry of the short
round. -/
theorem entryIs_long_ne (f : PFmt E) (wk : Nat) : ¬ EntryIs E (pRound f)
    (TwPlan.rd wk "PSC round" f.n 1) := by
  rintro ⟨s, hs, h1, _, _⟩
  have h2 : RoundIs E (pRound f) ⟨f.n + 1, s.drawE, s.drawNZ⟩ := ⟨⟨Equiv.refl _⟩, hs.2.1, hs.2.2⟩
  have c : s.scalars = f.n + 1 := RoundIs.scalars_eq two_le hs h2
  have h1' : 24 * f.n = 24 * s.scalars := h1
  omega

end
end TwRound
