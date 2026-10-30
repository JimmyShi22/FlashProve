-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsLedger.lean: if the forms of the list `rowsForm`
(OnBytes/Tie/Pv/Tail/EndForms.lean) hold on the committed entries, then every tie and every read of
the typed smallness test holds, at the letters that are read off these entries.

Statements and proofs. The list `rowsForm` is the share of the ties and reads in the verifier's one
equation (OnBytes/Tie/Pv/Tail/EndFormsFrom.lean). A ledger that holds this list can be batched as
any ledger; behind the batching draw stands "every form holds", and this file leads from there to
the equations that ride through the lookup on the digits.
Main names:
  `rowsLedger`: the forms of `rowsForm`, without their exponents.
  `rowsLedger_holds`: they hold on m if and only if every row of `rowsTail` is 0 at the cells of m.
  `TiesReads`: every tie and every read at the drawn matrix, at given digits: the second and the
    third clause of `relOut` (Cb/Pv/Tail/Block.lean).
  `eqs_of_ledger`: under `AtA` at the cells of m: they give `TiesReads`.
  `eqs_port`: the same at the letters of OnBytes/Tie/Pv/Tail/LettersAt.lean, under `PortOK`.
Limits: one way alone. The premises of OnBytes/Tie/Pv/Tail/EndsAt.lean and EndsAtPort.lean stand.
-/
import OnBytes.Tie.Pv.Tail.EndForms
import OnBytes.Tie.Pv.Tail.EndsAtPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model OnBytes.Road.Rows

open Finset Cb.Pv.Tail Iop

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (tl : HTailF2)

/-- The forms of the list, without their exponents. -/
def rowsLedger (funs : Array HFun) (pc : Nat) : TWhole.Ledger K J :=
  (rowsForm Y ρ tl funs pc).map Prod.snd

/-- The forms hold on m if and only if every row is 0 at the cells of m. -/
theorem rowsLedger_holds (funs : Array HFun) (pc : Nat) (m : J → K) :
    TWhole.Ledger.Holds (rowsLedger ρ Y tl funs pc) m ↔
      ∀ r ∈ rowsTail ρ tl funs pc, r.2 (fun t r c => Y.cellAt m t r c) = 0 := by
  unfold TWhole.Ledger.Holds rowsLedger rowsForm
  rw [List.map_map]
  constructor
  · intro h r hr
    have h1 := h (formOfGap Y r.2) (List.mem_map.2 ⟨r, hr, rfl⟩)
    unfold TWhole.Form.Holds at h1
    rwa [formOfGap_gap Y (lin_rowsTail ρ tl funs pc r hr)] at h1
  · intro h f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
    show (formOfGap Y r.2).gap m = 0
    rw [formOfGap_gap Y (lin_rowsTail ρ tl funs pc r hr)]
    exact h r hr

/-- Every tie and every read at the drawn matrix, at given digits. -/
def TiesReads {s : Size} (Λ : Letters K s) (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) : Prop :=
  (∀ (μ : Fin s.NM) u (i' : Fin (Alg.symRows (s.m μ))),
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.sym msg μ i' c = Alg.pack (s.rad : ℤ) (comb Z μ u) i') ∧
  (∀ μ u r,
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.tab msg μ r c = ∑ i, Λ.w x μ r i * comb Z μ u i)

/-- Under `AtA` at the cells of m the forms give every tie and every read. -/
theorem eqs_of_ledger {Θ : TLetters K (sizeOf tl)} {x : Θ.X} {msg : Θ.M}
    {Z : Dig K (sizeOf tl).size} {β : Dr (sizeOf tl).size} (pc : Nat) (m : J → K)
    (at' : AtA ρ tl Θ x msg Z β fun t r c => Y.cellAt m t r c) (hfit : Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (h : TWhole.Ledger.Holds (rowsLedger ρ Y tl tl.funs pc) m) :
    TiesReads Θ.letters x β msg Z := by
  obtain ⟨hT, hR⟩ := (rows_iff ρ _ tl tl.funs pc).1 ((rowsLedger_holds ρ Y tl tl.funs pc m).1 h)
  exact ⟨ties_of_rows at' hfit hT, reads_of_rows at' htree hR⟩

/-- The same at the letters that are read off the committed entries. -/
theorem eqs_port (K3 : Nat) (ws : List UInt64) (ok : PortOK tl K3 ws) (X : Type) (Ex : ExtSpec)
    (W₀ : Type) (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) (x : X)
    (m : JE Y tl → K) (u : JL Y tl → K) (Z : Dig K (sizeOf tl).size)
    (hzl : ∀ μ v i, Z.zl μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 0 0).getD 0 + i))
    (hzh : ∀ μ v i, Z.zh μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 1 0).getD 0 + i))
    (hfit : Fits tl) (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2) (pc : Nat)
    (h : TWhole.Ledger.Holds (rowsLedger ρ Y tl tl.funs pc) (glue Y tl m u)) :
    TiesReads (thetaAt ρ Y tl (u3Of tl) K3 X Ex W₀ ride).letters x
      (drawnOf (sizeOf tl).size ws) m Z :=
  eqs_of_ledger ρ Y tl pc (glue Y tl m u)
    (ata_port ρ Y tl K3 ws ok X Ex W₀ ride x m u Z hzl hzh) hfit htree h

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.rowsLedger_holds
#print axioms OnBytes.Tie.Pv.Tail.Port.eqs_of_ledger
#print axioms OnBytes.Tie.Pv.Tail.Port.eqs_port
