-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersBegun.lean: the beginning of a proximity test keeps every ledger in
order.

  fit_close1, fit_closeLedgers   shutting a ledger turns "closed" alone, which LedgerAt
                   (Johnson/Desc/K13/Law/LedgerWithin.lean) does not read.
  fit_groups       a change of the groups turns no message.
  fit_begun        so Slice.begun (OnBytes/Slice/BlkBegin.lean) keeps LedgersFit.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersKept
import OnBytes.Slice.BlkBegin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice

/-- Shutting one ledger turns "closed" alone, which the sentence does not read. -/
theorem fit_close1 (T : Statement) (o : ℕ) (h : LedgersFit T) :
    LedgersFit { T with oracles := T.oracles.modify o fun x =>
      { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
  fit_of
    (fun _ ⟨k, hk⟩ => ⟨k, ledgerAt_modify₀ T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      (fun x => ⟨rfl, fun l hl => ⟨{ l with closed := true }, by simp [hl], rfl, rfl, rfl, rfl⟩⟩)
      hk⟩)
    (noNew_modify₀ T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun x _ hl => by
        have hl' : (x.ledger.map fun l => { l with closed := true }).isSome = true := hl
        rw [Option.isSome_map] at hl'
        exact hl') h

/-- So does the shutting of a list of ledgers. -/
theorem fit_closeLedgers : ∀ (l : List Nat) (T : Statement), LedgersFit T →
    LedgersFit (closeLedgers T l)
  | [], _, h => h
  | o :: l, T, h => by
    show LedgersFit (closeLedgers _ l)
    exact fit_closeLedgers l _ (fit_close1 T o h)

/-- A change of the groups turns no message. -/
theorem fit_groups (T : Statement) (gs : Array Group) (h : LedgersFit T) :
    LedgersFit { T with groups := gs } := fun o x hx hl =>
  let ⟨k, hk⟩ := h o x hx hl
  ⟨k, ledgerAt_same rfl (fun y hy => ⟨y, hy, LedSame.refl y⟩) hk⟩

/-- **The beginning of a proximity test keeps every ledger in order.** -/
theorem fit_begun (T : Statement) (g : Nat) (G : Group) (h : LedgersFit T) :
    LedgersFit (begun T g G) :=
  fit_groups _ _ (fit_closeLedgers _ _ h)

end VerifiableInference.Desc.K13.Law
