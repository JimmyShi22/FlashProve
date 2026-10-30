-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyBattRow.lean: THE KEY FILE's ROW 1.16: WHAT THE KIND K13's batt's OWN YES SAYS OF THE ROWS' FORM: over batt_ok (Johnson/Desc/K13/Law/Law.lean) and OnBytes/Iop/Batt | Psc | Tensor. No state, no lens, no reading.
  batt_pile_psi   every row of the pile has a point of just kCol coordinates (Batt.fits asks it)
  batt_row_psi    so has the one row that is handed on (the sumcheck's point)
  scale_ok        Tensor.scale turns the scalar alone: ok is the same
  batt_row_ok     if every vector of every row of the pile is Tensor.ok, so is every vector of the row that is handed on
WHAT FOR: the one premise of the bridge «At» (Johnson/Desc/Key/KeyCoinK13.lean: x.psi.length = kCol) at BOTH borders of the row; and the promise's clause «every vector of the claim's g is Tensor.ok» behind it.
Nothing on soundness.
-/
import Johnson.Desc.K13.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.K13 (batt St)
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.K13.Law (batt_ok)

theorem fits_psi {k : Nat} {pile : List TensorRow} (h : Batt.fits k pile = true) : ∀ r ∈ pile, r.psi.length = k := by
  unfold Batt.fits at h
  cases pile with
  | nil => exact nomatch h
  | cons r₀ l =>
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    intro r hr
    exact (h.2 r hr).1.1

/-- Tensor.ok, as a function of the four fields that it reads. -/
def okOf (pairs : List (E × E)) (denseVars : List Nat) (values : Array E) (first : Nat) : Bool :=
  decide (pairs.length ≤ 63) &&
  (denseVars.isEmpty || decide (first + 2 ^ denseVars.length ≤ values.size)) &&
  (denseVars.all fun d => pairs[d]? == some (oneE, oneE)) &&
  distinctNats denseVars

theorem ok_eq (t : Tensor) : t.ok = okOf t.pairs t.denseVars t.values t.first := by
  unfold Tensor.ok okOf Tensor.vars
  rfl

theorem scale_ok (t : Tensor) (x : E) : (t.scale x).ok = t.ok := by
  rw [ok_eq, ok_eq]
  unfold Tensor.scale
  rfl

theorem mem_zipT {α β : Type} (l : List α) (m : List β) (p : α × β) (h : p ∈ zipT l m) : p.1 ∈ l := by
  rw [zipT_eq] at h
  exact (List.of_mem_zip h).1

theorem rowOf_ok (pile : List TensorRow) (o : Psc.Out) (h : ∀ r ∈ pile, ∀ t ∈ r.g, t.ok = true) : ∀ t ∈ (Batt.rowOf pile o).g, t.ok = true := by
  intro t ht
  simp only [Batt.rowOf, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨p, hp, t₀, ht₀, rfl⟩ := ht
  rw [scale_ok]
  exact h p.1 (mem_zipT _ _ p hp) t₀ ht₀

theorem run_point {c : Psc.Claim} {S : Psc.Summand} {fresh : List Slot} {hd : Psc.Heard} {o : Psc.Out} (hS : S.shown = 0)
    (h : Psc.run c S fresh hd = some o) : o.point.length = c.vars.length := by
  unfold Psc.run at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hl : hd.rounds.length = (Psc.varsOf c S).length := hc.1.1.1.2
    have hv : Psc.varsOf c S = c.vars := by simp [Psc.varsOf, hS]
    obtain rfl := Option.some.inj h
    show ((hd.rounds.map (·.2)).take c.vars.length).length = _
    rw [List.length_take, List.length_map, hl, hv, Nat.min_self]
  · exact nomatch h

section
variable {owed : RowsOwed} {k n : Nat} {pile : List TensorRow} {ledger : Nat} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}

theorem batt_pile_psi (h : batt owed k n pile ledger d rs = .ok out) : ∀ r ∈ pile, r.psi.length = k := by
  obtain ⟨_, _, _, _, _, _, _, _, hf, _⟩ := batt_ok h
  exact fits_psi hf

theorem batt_row_psi (h : batt owed k n pile ledger d rs = .ok out) : out.1.psi.length = k := by
  obtain ⟨_, _, x, _, _, o, _, _, hf, _, _, _, _, ho, _, rfl⟩ := batt_ok h
  show o.point.length = k
  rw [run_point rfl ho]
  show (List.replicate ((pile.head?.map (·.psi.length)).getD 0) (Psc.Weight.plain 3)).length = k
  rw [List.length_replicate]
  cases pile with
  | nil => exact nomatch hf
  | cons r₀ l => exact fits_psi hf r₀ List.mem_cons_self

theorem batt_row_ok (h : batt owed k n pile ledger d rs = .ok out) (hp : ∀ r ∈ pile, ∀ t ∈ r.g, t.ok = true) : ∀ t ∈ out.1.g, t.ok = true := by
  obtain ⟨_, _, _, _, _, o, _, _, _, _, _, _, _, _, _, rfl⟩ := batt_ok h
  exact rowOf_ok pile o hp

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.batt_pile_psi
#print axioms VerifiableInference.Desc.Key.batt_row_psi
#print axioms VerifiableInference.Desc.Key.batt_row_ok
