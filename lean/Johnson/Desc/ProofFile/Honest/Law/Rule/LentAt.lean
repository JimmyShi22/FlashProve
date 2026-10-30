-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LentAt.lean: the coins that a part is given
(Honest/Frame.lean: `lendPart`) at a run's coins in which one row has been set anew
(Honest/Law/Rule/RowLens.lean). No run of a protocol occurs here.

  1  `RowAt`, `RowAt.set`   what `Coins.lens` gives, as one structure: a lens on the row at an
     address o, typed at the row's count; `look` elsewhere does not read the row; in o's own chain
     and in the second chain `look` at o returns what the lens shows
  2  `lent_other`   another part, which is given no block of o's coins, is given the same coins,
     whatever is in o's row
  3  `lent_known`   another part, which is given blocks of o's coins, is given the same coins at two
     settings of the row that have these blocks in common
  4  `lent_self`   the part at o itself: its own coins are the row; its blocks do not read the row

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

variable {V W X : Type}

/-- **A lens on the row at the address o**, of the chain number t, at the count d. -/
structure RowAt (B : ProverCoinCounts) (o : Addr) (t : Nat) (d : Due) (get : Coins B → Cs d)
    (put : Cs d → Coins B → Coins B) : Prop where
  ok : Lens.OK get put
  other : ∀ x k ch b, b ≠ o → (put x k).look ch b = k.look ch b
  self : ∀ ch, ch = t ∨ ch = 2 → ∀ k : Coins B, k.look ch o = ⟨d, get k⟩

section
variable {B : ProverCoinCounts} {o : Addr} {t : Nat} {d : Due} {get : Coins B → Cs d}
  {put : Cs d → Coins B → Coins B}

/-- At o, where the chain sees the row: what was set. -/
theorem RowAt.set (R : RowAt B o t d get put) {ch : Nat} (hch : ch = t ∨ ch = 2) (x : Cs d)
    (k : Coins B) : (put x k).look ch o = ⟨d, x⟩ := by
  rw [R.self ch hch, R.ok.tst_set]

/-- **Another part than the one at o, which is given no block of o's coins.** -/
theorem lent_other (R : RowAt B o t d get put) (rows : List (Addr × Due)) (ch : Nat) (b : Addr)
    (p : Part V W X) (hb : b ≠ o) (hno : ∀ e ∈ B.ahead, e.spender = b → e.owner ≠ o) (x : Cs d)
    (k : Coins B) :
    lendPart B rows ((put x k).look ch) b p = lendPart B rows (k.look ch) b p :=
  lendPart_congr B rows _ _ b p (R.other x k ch b hb) fun e he hs => by
    rw [R.other x k ch e.owner (hno e he hs)]

/-- **Another part than the one at o, which is given blocks of o's coins**, in a chain that sees o's
row. -/
theorem lent_known (R : RowAt B o t d get put) (rows : List (Addr × Due)) {ch : Nat}
    (hch : ch = t ∨ ch = 2) (b : Addr) (p : Part V W X) (hb : b ≠ o) (x x' : Cs d)
    (hx : ∀ e ∈ B.ahead, e.spender = b → e.owner = o →
      x.cut e.start e.count = x'.cut e.start e.count) (k : Coins B) :
    lendPart B rows ((put x k).look ch) b p = lendPart B rows ((put x' k).look ch) b p :=
  lendPart_congr B rows _ _ b p ((R.other x k ch b hb).trans (R.other x' k ch b hb).symm)
    fun e he hs => by
      by_cases ho : e.owner = o
      · rw [ho, R.set hch x k, R.set hch x' k]
        exact hx e he hs ho
      · rw [R.other x k ch e.owner ho, R.other x' k ch e.owner ho]

/-- **The part at o itself**, where its count is the row's and no entry gives it a block of its own
coins: in its own chain its own coins are what is set in the row; the rest, an error too, is as
before. -/
theorem lent_self {p : Part V W X} {get : Coins B → Cs p.takes}
    {put : Cs p.takes → Coins B → Coins B} (R : RowAt B o t p.takes get put)
    (rows : List (Addr × Due)) (hno : ∀ e ∈ B.ahead, e.spender = o → e.owner ≠ o)
    (x : Cs p.takes) (k : Coins B) :
    lendPart B rows ((put x k).look t) o p =
      (lendPart B rows (k.look t) o p).map fun c => (x, c.2.1, c.2.2) := by
  have h1 : ∀ P : Ahead → Bool, ∀ e ∈ (B.ahead.filter fun e => e.spender == o).filter P,
      (((put x k).look t) e.owner).2.cut e.start e.count =
        ((k.look t) e.owner).2.cut e.start e.count := by
    intro P e he'
    have h2 := List.mem_filter.1 (List.mem_filter.1 he').1
    rw [R.other x k t e.owner (hno e h2.1 (beq_iff_eq.1 h2.2))]
  simp only [lendPart]
  rw [R.set (Or.inl rfl) x k, R.self t (Or.inl rfl) k,
    lend_congr ((put x k).look t) (k.look t) p.spends _ (h1 fun e => e.once),
    lend_congr ((put x k).look t) (k.look t) p.carries _ (h1 fun e => !e.once)]
  simp only [Cs.cut_zero]
  by_cases hd : (p.takes != dueAt rows o) = true
  · simp only [if_pos hd]
    rfl
  · simp only [if_neg hd]
    cases lend (k.look t) p.spends ((B.ahead.filter fun e => e.spender == o).filter fun e =>
        e.once) with
    | error _ => rfl
    | ok sp =>
      cases lend (k.look t) p.carries ((B.ahead.filter fun e => e.spender == o).filter fun e =>
          !e.once) with
      | error _ => rfl
      | ok ca => rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.RowAt.set
#print axioms ProofFile.Honest.lent_other
#print axioms ProofFile.Honest.lent_known
#print axioms ProofFile.Honest.lent_self
