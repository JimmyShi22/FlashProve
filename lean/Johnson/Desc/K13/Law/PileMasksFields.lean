-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileMasksFields.lean: "K13.pileMasks" (every row on the table names mask
entries of the index masks' message alone) AT THE FOUR SORTS OF STEP THAT TOUCH WHAT IT READS:
bricks for a walk along the first chain, with few imports.

  pendingRowO_names   the pending row's mask entries name the number that the row's function is
                   given. No premise on the ledgers.
  pileMasksC_same  the rows and the number stay: the test goes on.
  pileMasksC_nil   no row lies on the table: the test accepts, whatever the number: so over link 0's
                   "opened", which writes the number, where no row lies.
  pileMasksC_push  one pending row, made at the state's own number, is laid behind the others.
  pileMasksC_atM3  behind kind K13's batching the test accepts OUTRIGHT (rowMasks,
                   Johnson/Desc/K13/Law/RowMasks.lean).

What is not claimed. The test at reached states. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K13.Law.PileMasksIff
import Johnson.Desc.K13.Law.RowMasks
import Johnson.Desc.First.Pend.RowMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff)

theorem pendingRowO_names {lay : WsLay} {indexMasks : ℕ} {o : WsForkOut} {claims : ℕ}
    {Sh : LinShape} {os : Array OnBytes.Oracle} {row : TensorRow}
    {oracles' : Array OnBytes.Oracle}
    (h : pendingRowO lay indexMasks o claims Sh os = .ok (row, oracles')) :
    ∀ t ∈ row.masks, t.1.oracle = indexMasks := by
  obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
    (pendingRowO_iff lay indexMasks o claims Sh os oracles' row).1 h
  intro t ht'
  rw [List.mem_singleton] at ht'
  subst ht'
  rfl

theorem pileMasksC_same {s s' : S} (hr : s'.rows = s.rows)
    (hi : s'.out.indexMasks = s.out.indexMasks) (h : pileMasksC s = true) :
    pileMasksC s' = true := by
  unfold pileMasksC at h ⊢
  rw [hr, hi]
  exact h

theorem pileMasksC_nil {s : S} (hr : s.rows = []) : pileMasksC s = true := by
  unfold pileMasksC
  rw [hr]
  rfl

theorem pileMasksC_push {s s' : S} {lay : WsLay} {o : WsForkOut} {claims : ℕ} {Sh : LinShape}
    {os : Array OnBytes.Oracle} {row : TensorRow} {oracles' : Array OnBytes.Oracle}
    (hp : pendingRowO lay s.out.indexMasks o claims Sh os = .ok (row, oracles'))
    (hr : s'.rows = s.rows ++ [row]) (hi : s'.out.indexMasks = s.out.indexMasks)
    (h : pileMasksC s = true) : pileMasksC s' = true := by
  simp only [pileMasksC, List.all_eq_true, beq_iff_eq] at h ⊢
  intro r hr' t ht
  rw [hr, List.mem_append, List.mem_singleton] at hr'
  rw [hi]
  rcases hr' with hr' | rfl
  · exact h r hr' t ht
  · exact pendingRowO_names hp t ht

theorem pileMasksC_atM3 {Cl : Type} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    pileMasksC s' = true := by
  obtain ⟨r, hr, hon, -⟩ := rowMasks P s s' rs gs h
  refine (pileMasksC_iff s').2 fun r' hr' => ?_
  rw [hr, List.mem_singleton] at hr'
  subst hr'
  exact hon

end VerifiableInference.Desc.K13.Law
