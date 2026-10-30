-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedSpread.lean: what is still open between the closing draw's count and the
claims that the shipped Lean verifier adds.

The count of bad batching elements (cnt_batchAt_le, LedBatch.lean) is
for a list of claims that does not hang on theta. The verifier's own list, read at the state at
which the one equation is written, does hang on theta. Each tie and each read of the smallness test
is one claim whose form holds powers of theta, and the weights of some virtual rows on the rows of
their arrays are powers of theta (coefficientsF, OnBytes/Model/Tail.lean). By far the most of the
plan's rows lie inside such claims.

Main names.
  SameGap Ok c H l rowsOf: at every theta with Ok theta, and on all entries, the one form of rowsOf
    has the same gap as the one form of the verifier's claims l theta, read at the state H theta,
    under the exponents c, c + 1 and so on. Ok theta is meant as: the verifier's run at theta
    reaches the state at which the one equation is written. The verifier refuses at some theta, by
    tests that hang on theta, and there H theta and l theta are no states and lists of a run.
    sameGap_append: a list of claims may be spread piece by piece.
    sameGap_of_const: a piece whose reading does not hang on theta is its own spread.
  Spread Ok rows H l rowsOf: rowsOf is a list of claims with exponents, on the committed entries,
    that does not hang on theta. No two of its exponents are equal, none is above rows - 1, and
    SameGap Ok 0 H l rowsOf.
  HSpread Ok rows H l: there is such a list. THIS IS A HYPOTHESIS. It is proved here only where H
    and l do not hang on theta (spread_const).
  spread_iff: under Spread, at a theta with Ok theta, the one form of the verifier's claims holds
    if and only if the one form of rowsOf does.
  spread_count: under Spread, if some member of rowsOf fails on m, the one form of rowsOf holds at
    no more than rows - 1 elements. The count is over all elements, so it bounds the bad ones among
    those with Ok.

What this file does not claim. Ok is a letter here: with an Ok that holds nowhere the empty list
serves, and HSpread says nothing. That the verifier's claims spread into such a list is not shown
here.
What the members of rowsOf say (the single equations of the ties and reads) is whoever gives rowsOf
to say. The count is over the elements of the field K. That the verifier's theta, read in K, is a
uniform draw from K is not stated.


-/
import OnBytes.Tie.Pv.Led.LedWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

variable {K J : Type} [Field K] [Fintype J] (ρ : Model.Reading K) (Y : Lay J)

/-- At every theta with Ok theta, and on all entries, the one form of rowsOf has the same gap as the
one form of the verifier's claims l theta, read at the state H theta, under the exponents c, c + 1
and so on. rowsOf is one list for all theta. -/
def SameGap (Ok : E → Prop) (c : Nat) (H : E → Model.Fork) (l : E → List Model.Aff)
    (rowsOf : List (Nat × TWhole.Form K J)) : Prop :=
  ∀ theta : E, Ok theta → ∀ m : J → K, (batchAt (ρ.val theta) rowsOf).gap m =
    (batchAt (ρ.val theta)
      ((List.range' c (l theta).length).zip (claimsOf ρ Y (H theta) (l theta)))).gap m

/-- The verifier's claims, which may hang on theta, spread into the list rowsOf, which does not.
Ok theta: the run at theta reaches the state at which the one equation is written; H theta: that
state; l theta: the forms that were added. -/
structure Spread (Ok : E → Prop) (rows : Nat) (H : E → Model.Fork) (l : E → List Model.Aff)
    (rowsOf : List (Nat × TWhole.Form K J)) : Prop where
  /-- no two exponents are equal -/
  nodup : (rowsOf.map Prod.fst).Nodup
  /-- no exponent is above rows - 1 -/
  le : ∀ p ∈ rowsOf, p.1 ≤ rows - 1
  /-- at every theta with Ok theta and on all entries the two one forms have the same gap -/
  same : SameGap ρ Y Ok 0 H l rowsOf

/-- The hypothesis: the verifier's claims spread into a list that does not hang on theta. -/
def HSpread (Ok : E → Prop) (rows : Nat) (H : E → Model.Fork) (l : E → List Model.Aff) : Prop :=
  ∃ rowsOf : List (Nat × TWhole.Form K J), Spread ρ Y Ok rows H l rowsOf

variable {ρ Y}

omit [Fintype J] in
theorem sumFrom_append {α : Type} (g : Nat → α → K) : ∀ (a b : List α) (s : Nat),
    Model.sumFrom g s (a ++ b) = Model.sumFrom g s a + Model.sumFrom g (s + a.length) b
  | [], b, s => by simp [Model.sumFrom]
  | x :: a, b, s => by
    simp only [List.cons_append, Model.sumFrom, sumFrom_append g a b (s + 1), List.length_cons]
    rw [show s + 1 + a.length = s + (a.length + 1) by omega]
    ring

/-- Two pieces of the verifier's list, spread one by one, are spread together. The first piece has
the same number of claims at every theta with Ok theta. -/
theorem sameGap_append {Ok : E → Prop} {c n : Nat} {H : E → Model.Fork}
    {l₁ l₂ : E → List Model.Aff} {R₁ R₂ : List (Nat × TWhole.Form K J)}
    (h₁ : SameGap ρ Y Ok c H l₁ R₁) (hn : ∀ theta, Ok theta → (l₁ theta).length = n)
    (h₂ : SameGap ρ Y Ok (c + n) H l₂ R₂) :
    SameGap ρ Y Ok c H (fun theta => l₁ theta ++ l₂ theta) (R₁ ++ R₂) := by
  intro theta ok m
  have e1 := h₁ theta ok m
  have e2 := h₂ theta ok m
  rw [batch_claimsValue, batchAt_gap] at e1 e2 ⊢
  simp only [List.map_append, List.sum_append, e1, e2, Model.claimsValue, sumFrom_append,
    hn theta ok]

/-- A piece of the verifier's list whose reading is the same ledger L at every theta with Ok theta
is its own spread. -/
theorem sameGap_of_const {Ok : E → Prop} {c : Nat} {H : E → Model.Fork}
    {l : E → List Model.Aff} (L : TWhole.Ledger K J)
    (h : ∀ theta, Ok theta → claimsOf ρ Y (H theta) (l theta) = L) :
    SameGap ρ Y Ok c H l ((List.range' c L.length).zip L) := by
  intro theta ok m
  have e : (l theta).length = L.length := by rw [← h theta ok, claimsOf, List.length_map]
  rw [h theta ok, e]

theorem spread_iff {Ok : E → Prop} {rows : Nat} {H : E → Model.Fork}
    {l : E → List Model.Aff} {rowsOf : List (Nat × TWhole.Form K J)}
    (S : Spread ρ Y Ok rows H l rowsOf) (theta : E) (ok : Ok theta) (m : J → K) :
    (batchAt (ρ.val theta)
      ((List.range' 0 (l theta).length).zip (claimsOf ρ Y (H theta) (l theta)))).Holds m ↔
      (batchAt (ρ.val theta) rowsOf).Holds m := by
  unfold TWhole.Form.Holds
  rw [S.same theta ok m]

theorem spread_count [Fintype K] {Ok : E → Prop} {rows : Nat} {H : E → Model.Fork}
    {l : E → List Model.Aff} {rowsOf : List (Nat × TWhole.Form K J)}
    (S : Spread ρ Y Ok rows H l rowsOf) (m : J → K)
    (bad : ∃ p ∈ rowsOf, ¬ p.2.Holds m) :
    Prob.cnt (fun x : K => (batchAt x rowsOf).Holds m) ≤ rows - 1 :=
  cnt_batchAt_le rowsOf m S.nodup (rows - 1) S.le bad

variable (ρ Y)

/-- Where neither the state nor the list hangs on theta, the claims are their own spread. -/
theorem spread_const (Ok : E → Prop) (rows : Nat) (H : Model.Fork) (l : List Model.Aff)
    (hl : l.length ≤ rows) :
    Spread ρ Y Ok rows (fun _ => H) (fun _ => l)
      ((List.range' 0 l.length).zip (claimsOf ρ Y H l)) where
  nodup := List.Nodup.sublist (zip_fst_sublist _ _) List.nodup_range'
  le := fun p hp => by
    have h1 : p.1 ∈ List.range' 0 l.length :=
      (zip_fst_sublist _ _).subset (List.mem_map.2 ⟨p, hp, rfl⟩)
    have := List.mem_range'_1.1 h1
    omega
  same := fun _ _ _ => rfl

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.spread_iff
#print axioms OnBytes.Road.Rows.spread_count
#print axioms OnBytes.Road.Rows.spread_const
#print axioms OnBytes.Road.Rows.sameGap_append
#print axioms OnBytes.Road.Rows.sameGap_of_const
