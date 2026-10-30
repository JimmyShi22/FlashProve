-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerErrByMake.lean: THE LEDGER's TWO PREMISES herrA | herrB ("the family of
error
bounds r9 | r10, at the written rounds of the piece at place 9 | 10, IS the pair (e, εt)") ARE NO
DEBTS:
where the piece's written rounds are d :: dt (hdsA | hdsB), the pair can be READ OFF the family: lay
eA := (r9 (dBA :: dtA)).1 · εtA := (r9 (dBA :: dtA)).2, and the like at B.
  errHead · errTail   the first round's error bound, and the others', of a list of error bounds at d
  :: dt
  herr_by_make        ds = d :: dt ⊢ HEq (r ds) ((errHead (r (d :: dt)), errTail (r (d :: dt))) :
  Err …)
  herr_cap            at the family "the cap": r := fun ds => Err.cap 128 (uLT C ds): the head is
  the whole
                      number (the number of the round's challenges) / 2 ^ 128, the tail is the cap
                      of dt
  below_cap           and that family is below 2⁻¹ ^ 128 at every list of rounds (the ledger's b9 |
  b10):
                      by Err.cap_below_inv
USER     the program that lays letters into the ledger's top: herrA ↦ herr_by_make r9 hdsA ·
         herrB ↦ herr_by_make r10 hdsB: two premises and four letters out, nothing in
What is not claimed. hleA | hleB (the sub-protocol's own count is at most that head) and hAA | hAB
(the law
at the tail): they now speak of the family's own entries. Nothing on soundness.

-/
import Johnson.Desc.Sound.BoundsAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)

/-- The first round's error bound. -/
def errHead {C : CK} {d : RDT} {dt : List RDT} (ε : Err (uLT C (d :: dt))) : ℕ :=
  Prod.fst (α := ℕ) (β := Err (uLT C dt)) ε

/-- The other rounds' error bounds. -/
def errTail {C : CK} {d : RDT} {dt : List RDT} (ε : Err (uLT C (d :: dt))) : Err (uLT C dt) :=
  Prod.snd (α := ℕ) (β := Err (uLT C dt)) ε

/-- **herrA | herrB by make.** -/
theorem herr_by_make {C : CK} (r : (ds : List RDT) → Err (uLT C ds)) {ds : List RDT} {d : RDT}
    {dt : List RDT} (h : ds = d :: dt) :
    HEq (r ds) ((errHead (r (d :: dt)), errTail (r (d :: dt))) : Err (uLT C (d :: dt))) := by
  subst h
  rfl

/-- At the cap. -/
theorem herr_cap {C : CK} {ds : List RDT} {d : RDT} {dt : List RDT} (h : ds = d :: dt) :
    HEq (Err.cap 128 (uLT C ds))
      ((errHead (Err.cap 128 (uLT C (d :: dt))), Err.cap 128 (uLT C dt)) :
        Err (uLT C (d :: dt))) := by
  subst h
  rfl

/-- The cap is below 2⁻¹ ^ 128. -/
theorem below_cap {C : CK} (ds : List RDT) :
    Err.Below (Err.cap 128 (uLT C ds)) ((2 : ENNReal)⁻¹ ^ 128) := Err.cap_below_inv 128 _

end Desc.K14.Law
