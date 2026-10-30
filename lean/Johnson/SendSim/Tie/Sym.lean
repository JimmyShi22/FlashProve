-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Sym.lean: a row's symbol (sym, Johnson/LinkSim/Tail.lean) depends only on its
tail below r and on its message below l, and it is additive; and lemmas on tl, which extends a tail
on Fin r to all natural numbers (Johnson/SendSim/Defs.lean).
Terms: Johnson/SendSim/Defs.lean, "Terms of the model". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves, over any field, by algebra on finite sums.
  msgPart_congr, sym_congr   Messages that agree below l and tails that agree below r give the same
                             symbol.
  sym_add                    The symbol of sums is the sum of the symbols.
  tl_lt, tl_ge               tl t q is entry q of t for q below r, and 0 from r on.
  tl_add, tl_zero            tl is additive.
  cutTl, tl_cutTl            cutTl r t restricts a function on all natural numbers to Fin r; tl of
                             it agrees with t below r.
  sym_tl_cutTl               So a symbol is the same at the tail t and at tl (cutTl r t).

How it fits. shown_move (Johnson/SendSim/CoreProofs.lean), on the way to sendExact and sendFresh,
uses sym_congr, tl_add and tl_cutTl. Johnson/SendSim/At/Symbols.lean and
Johnson/SendSim/Tie/SymF.lean use others. tl_ge and msgPart_congr are used only in this file.
-/
import Johnson.SendSim.Defs

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes.LinkSim

variable {K : Type} [Field K]

/-- Messages that agree below l contribute the same to a symbol. -/
theorem msgPart_congr (r l : ℕ) (p : K) {m m' : ℕ → K} (h : ∀ j, j < l → m j = m' j) :
    msgPart r l p m = msgPart r l p m' := by
  unfold msgPart
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

/-- If two messages agree below l and two tails agree below r, they give the same symbol at every
point. -/
theorem sym_congr (r l : ℕ) (p : K) {m m' t t' : ℕ → K} (hm : ∀ j, j < l → m j = m' j)
    (ht : ∀ q, q < r → t q = t' q) : sym r l p m t = sym r l p m' t' := by
  unfold sym
  rw [msgPart_congr r l p hm]
  exact congrArg (· + _) (Finset.sum_congr rfl fun q hq => by rw [ht q (Finset.mem_range.1 hq)])

/-- The symbol of a sum of messages and a sum of tails is the sum of the two symbols. -/
theorem sym_add (r l : ℕ) (p : K) (m m' t t' : ℕ → K) :
    sym r l p (m + m') (t + t') = sym r l p m t + sym r l p m' t' := by
  classical
  unfold sym
  rw [msgPart_add]
  have e : ∑ q ∈ Finset.range r, p ^ q * (t + t') q =
      ∑ q ∈ Finset.range r, p ^ q * t q + ∑ q ∈ Finset.range r, p ^ q * t' q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => mul_add _ _ _
  rw [e]
  ring

theorem tl_lt {r : ℕ} (t : Fin r → K) {q : ℕ} (h : q < r) : tl t q = t ⟨q, h⟩ := dif_pos h

theorem tl_ge {r : ℕ} (t : Fin r → K) {q : ℕ} (h : r ≤ q) : tl t q = 0 :=
  dif_neg (Nat.not_lt.2 h)

theorem tl_add {r : ℕ} (t t' : Fin r → K) : tl (t + t') = tl t + tl t' := by
  funext q
  by_cases h : q < r
  · rw [Pi.add_apply, tl_lt _ h, tl_lt _ h, tl_lt _ h, Pi.add_apply]
  · rw [Pi.add_apply, tl_ge _ (Nat.le_of_not_lt h), tl_ge _ (Nat.le_of_not_lt h),
      tl_ge _ (Nat.le_of_not_lt h), add_zero]

theorem tl_zero {r : ℕ} : tl (0 : Fin r → K) = 0 := by
  funext q
  by_cases h : q < r
  · rw [tl_lt _ h]
    rfl
  · rw [tl_ge _ (Nat.le_of_not_lt h)]
    rfl

/-- The restriction to Fin r of a function on all natural numbers. -/
def cutTl (r : ℕ) (t : ℕ → K) : Fin r → K := fun q => t q.val

theorem tl_cutTl (r : ℕ) (t : ℕ → K) {q : ℕ} (h : q < r) : tl (cutTl r t) q = t q := tl_lt _ h

/-- A symbol is the same at the tail t and at tl (cutTl r t). -/
theorem sym_tl_cutTl (r l : ℕ) (p : K) (m t : ℕ → K) :
    sym r l p m (tl (cutTl r t)) = sym r l p m t :=
  sym_congr r l p (fun _ _ => rfl) fun _ h => tl_cutTl r t h

end OnBytes.SendSim

#print axioms OnBytes.SendSim.sym_congr
#print axioms OnBytes.SendSim.sym_add
#print axioms OnBytes.SendSim.tl_add
#print axioms OnBytes.SendSim.sym_tl_cutTl
