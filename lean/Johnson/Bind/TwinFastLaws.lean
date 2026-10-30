-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastLaws.lean: what the statement `FastIsPlain` buys: if the fast encoder's columns
are the plain encoder's, the committer at the fast encoder is the committer.

The committer (Johnson/Bind/Twin.lean) reads the encoder's columns at the positions below 2^a alone
(`leavesFromW_congr`), and its loop over the leaves can be cut at any place (`leavesFromW_add`). So
the loop over blocks of Johnson/Bind/TwinFast.lean is the plain loop (`leavesBlocksW_eq`), and from
`FastIsPlain`, which is a hypothesis here, at every shape with a ≤ 32 and l + r ≤ 2^a, over every
lawful monad and every hash: `commitFastW` is `commitW` (`commitFastW_eq`).
No Mathlib.
Limits. `FastIsPlain` is a hypothesis in this file. Johnson/Bind/TwinFastProof.lean proves it and
draws the conclusion without it (`commitFastW_is_commitW`).

-/
import Johnson.Bind.TwinFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The leaves from x on read the columns at the n positions from x on alone. -/
theorem leavesFromW_congr (S : Shape) (start : Nat → ByteArray) (col col' : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (n x : Nat) (acc : Array ByteArray), (∀ y, x ≤ y → y < x + n → col y = col' y) →
      leavesFromW h S start col salt n x acc = leavesFromW h S start col' salt n x acc
  | 0, _, _, _ => rfl
  | n + 1, x, acc, hc => by
    simp only [leavesFromW]
    rw [hc x (Nat.le_refl x) (by omega)]
    refine congrArg _ (funext fun d => ?_)
    exact leavesFromW_congr S start col col' salt n (x + 1) _
      fun y h1 h2 => hc y (by omega) (by omega)

theorem span_le (S : Shape) : S.span ≤ S.a := Nat.min_le_left _ _

variable [LawfulMonad m]

/-- The loop over n₁ + n₂ leaves is the loop over n₁, then the loop over n₂. -/
theorem leavesFromW_add (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (n₁ n₂ x : Nat) (acc : Array ByteArray),
      leavesFromW h S start col salt (n₁ + n₂) x acc =
        leavesFromW h S start col salt n₁ x acc >>= fun more =>
          leavesFromW h S start col salt n₂ (x + n₁) more
  | 0, n₂, x, acc => by
    rw [Nat.zero_add]
    show _ = pure acc >>= _
    rw [pure_bind] <;> rfl
  | n₁ + 1, n₂, x, acc => by
    have e : n₁ + 1 + n₂ = (n₁ + n₂) + 1 := by omega
    have e2 : x + 1 + n₁ = x + (n₁ + 1) := by omega
    rw [e]
    simp only [leavesFromW, bind_assoc]
    refine congrArg _ (funext fun d => ?_)
    rw [leavesFromW_add S start col salt n₁ n₂ (x + 1), e2]

/-- The loop over blocks is the plain loop, where the blocks' columns are col's. -/
theorem leavesBlocksW_eq (S : Shape) (start : Nat → ByteArray) (block : Nat → Array ByteArray)
    (col : Nat → List UInt64) (salt : Nat → ByteArray) :
    ∀ (n B : Nat) (acc : Array ByteArray),
      (∀ B' i, B ≤ B' → B' < B + n → i < 2 ^ S.span →
        fastColumn (block B') i = col (B' * 2 ^ S.span + i)) →
      leavesBlocksW h S start block salt n B acc =
        leavesFromW h S start col salt (n * 2 ^ S.span) (B * 2 ^ S.span) acc
  | 0, B, acc, _ => by
    rw [Nat.zero_mul] <;> rfl
  | n + 1, B, acc, hb => by
    have e : (n + 1) * 2 ^ S.span = 2 ^ S.span + n * 2 ^ S.span := by
      rw [Nat.succ_mul, Nat.add_comm]
    have hc : ∀ y, B * 2 ^ S.span ≤ y → y < B * 2 ^ S.span + 2 ^ S.span →
        (fun x => fastColumn (block B) (x - B * 2 ^ S.span)) y = col y := by
      intro y h1 h2
      show fastColumn (block B) (y - B * 2 ^ S.span) = col y
      rw [hb B (y - B * 2 ^ S.span) (Nat.le_refl B) (by omega) (by omega),
        Nat.add_sub_cancel' h1]
    rw [e, leavesFromW_add]
    simp only [leavesBlocksW]
    rw [leavesFromW_congr h S start _ col salt (2 ^ S.span) (B * 2 ^ S.span) acc hc]
    refine congrArg _ (funext fun more => ?_)
    rw [leavesBlocksW_eq S start block col salt n (B + 1) more
      fun B' i h1 h2 h3 => hb B' i (by omega) (by omega) h3, Nat.succ_mul]

theorem fastW_eq (hF : FastIsPlain) (S : Shape) (ha : S.a ≤ 32) (hS : S.l + S.r ≤ 2 ^ S.a)
    (cfg : ByteArray) (T : Table) : fastW h S cfg T = plainW h S cfg T := by
  have hl := leavesBlocksW_eq h S (fun _ => cfg) (blockAt S (prepare S T)) (columnOf S (laid S T))
    T.salt (2 ^ (S.a - S.span)) 0 #[] fun B' i _ h2 h3 => hF S T ha hS B' i (by omega) h3
  rw [← Nat.pow_add, Nat.sub_add_cancel (span_le S), Nat.zero_mul] at hl
  simp only [fastW, plainW, coreW, rootW, bind_assoc, hl]

/-- **If the fast encoder's columns are the plain encoder's, the committer at the fast encoder is
the committer.** -/
theorem commitFastW_eq (hF : FastIsPlain) (S : Shape) (ha : S.a ≤ 32) (hS : S.l + S.r ≤ 2 ^ S.a)
    (files : List ByteArray) (T : Table) : commitFastW h S files T = commitW h S files T := by
  unfold commitFastW commitW
  exact congrArg _ (funext fun cfg => fastW_eq h hF S ha hS cfg T)

end Bind.Twin

#print axioms Bind.Twin.leavesFromW_congr
#print axioms Bind.Twin.span_le
#print axioms Bind.Twin.leavesFromW_add
#print axioms Bind.Twin.leavesBlocksW_eq
#print axioms Bind.Twin.fastW_eq
#print axioms Bind.Twin.commitFastW_eq
