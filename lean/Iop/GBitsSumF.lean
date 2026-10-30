-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GBitsSumF.lean: the sum of f b over the rounds with b > 0 proof-of-work bits (b: the round's
number in the list `GBits`, Iop/GBits.lean), for any function f into a commutative monoid, with
lemmas that evaluate it along `GBits.zero`, `GBits.app`, `GBits.rep`, not round by round; and a plan
of splits and merges (Iop/GrindRecut.lean: `GBits.recut`) does not change the sum, under the side
condition `GBits.RecutEx`. (Words of this library: lean/GLOSSARY.md.)
    `GBits.RecutEx P g`    at a merge of two prover messages the first round has no such bits
                           (`GBits.RecutOK` asks the same); at a merge of two challenges at most one
                           of the two rounds has.
Use (Compile/Batch/CountsGrSumF.lean): the bound on the honest prover's attempts after the first,
the sum of its chances of failure and the number of rounds with bits are such sums.
Notation: `XPlan s` (Iop/Recut.lean): a plan of splits and merges for the list of rounds s; its
steps: `keep`; `cut`: a first part is split off; `msg`: a merge of prover messages, (J1); `chal`: a
merge of challenges, (J2) (cases of Iop/Join.lean); `g : GBits s` (Iop/GBits.lean): for each round a
number of proof-of-work bits.
Limits: nothing is said on any protocol.
-/
import Iop.GrindRecut
import Iop.GBitsCount

set_option autoImplicit false

namespace Iop
namespace GBits

variable {M : Type} [AddCommMonoid M] (f : ℕ → M)

/-- The sum of f b over the rounds with proof-of-work bits. -/
def sumF : {s : Shape} → GBits s → M
  | [], _ => 0
  | _ :: _, (b, g) => (if b = 0 then 0 else f b) + sumF g

theorem count_eq_sumF : ∀ {s : Shape} (g : GBits s), g.count = sumF (fun _ => 1) g
  | [], _ => rfl
  | _ :: _, (b, g) => congrArg ((if b = 0 then 0 else 1) + ·) (count_eq_sumF g)

theorem sum_eq_sumF : ∀ {s : Shape} (g : GBits s), g.sum = sumF (fun b => b) g
  | [], _ => rfl
  | _ :: _, (b, g) => by
    show b + g.sum = (if b = 0 then 0 else b) + sumF (fun b => b) g
    rw [sum_eq_sumF g]
    by_cases h : b = 0
    · rw [if_pos h, h]
    · rw [if_neg h]

theorem sumF_zero : ∀ s : Shape, sumF f (GBits.zero s) = 0
  | [] => rfl
  | _ :: s => by
    show (if (0 : ℕ) = 0 then 0 else f 0) + sumF f (GBits.zero s) = 0
    rw [if_pos rfl, sumF_zero s, add_zero]

theorem sumF_app :
    ∀ {s t : Shape} (g : GBits s) (g' : GBits t), sumF f (GBits.app g g') = sumF f g + sumF f g'
  | [], _, _, _ => (zero_add _).symm
  | _ :: _, _, (b, g), g' => by
    show (if b = 0 then 0 else f b) + sumF f (GBits.app g g') =
      (if b = 0 then 0 else f b) + sumF f g + sumF f g'
    rw [sumF_app g g', add_assoc]

theorem sumF_rep (r : Round) (b : ℕ) :
    ∀ (n : ℕ) {t : Shape} (g : GBits t),
      sumF f (GBits.rep r b n g) = n • (if b = 0 then 0 else f b) + sumF f g
  | 0, _, g => by rw [zero_smul, zero_add]; rfl
  | n + 1, _, g => by
    show (if b = 0 then 0 else f b) + sumF f (GBits.rep r b n g) = _
    rw [sumF_rep r b n g, succ_nsmul, ← add_assoc, add_comm (if b = 0 then 0 else f b)]

theorem sumF_rep0 (r : Round) (n : ℕ) {t : Shape} (g : GBits t) :
    sumF f (GBits.rep r 0 n g) = sumF f g := by
  rw [sumF_rep, if_pos rfl, smul_zero, zero_add]

/-- a round without proof-of-work bits adds nothing (`sumF_cons`: a round with b ≠ 0 adds f b) -/
theorem sumF_cons0 {r : Round} {s : Shape} (g : GBits s) :
    sumF f (s := r :: s) (0, g) = sumF f g := by
  show (if (0 : ℕ) = 0 then 0 else f 0) + sumF f g = _
  rw [if_pos rfl, zero_add]

theorem sumF_cons {r : Round} {s : Shape} {b : ℕ} (hb : b ≠ 0) (g : GBits s) :
    sumF f (s := r :: s) (b, g) = f b + sumF f g := by
  show (if b = 0 then 0 else f b) + sumF f g = _
  rw [if_neg hb]

/-! ## Under a plan of splits and merges -/

/-- The side condition: no round's bits are dropped, and no two rounds that both have such bits are
merged. -/
def RecutEx : {s : Shape} → (P : XPlan s) → GBits s → Prop
  | _, .nil => fun _ => True
  | _, .keep _ P => fun (z : ℕ × GBits _) => RecutEx P z.2
  | _, .cut (s := s) c P => fun (z : ℕ × GBits s) => RecutEx P (show GBits (c.snd :: s) from z)
  | _, .msg r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) => z.1 = 0 ∧ RecutEx P (show GBits (r1.joinMsg r2 :: s) from z.2)
  | _, .chal r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) =>
      (z.1 = 0 ∨ z.2.1 = 0) ∧
      RecutEx P (show GBits (r1.joinChal r2 :: s) from (max z.1 z.2.1, z.2.2))

theorem RecutEx.ok {s : Shape} (P : XPlan s) : ∀ g : GBits s, RecutEx P g → GBits.RecutOK P g := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih => exact fun g h => ih g.2 h
  | cut c P ih => exact fun g h => ih g h
  | msg r1 r2 u P ih => exact fun g h => ⟨h.1, ih g.2 h.2⟩
  | chal r1 r2 np P ih => exact fun g h => ih (max g.1 g.2.1, g.2.2) h.2

/-- Under `RecutEx`, the plan does not change the sum. -/
theorem sumF_recut {s : Shape} (P : XPlan s) :
    ∀ g : GBits s, RecutEx P g → sumF f (g.recut P) = sumF f g := by
  induction P with
  | nil => intro _ _; rfl
  | keep r P ih => exact fun g h => congrArg ((if g.1 = 0 then 0 else f g.1) + ·) (ih g.2 h)
  | cut c P ih =>
      intro g h
      show (if (0 : ℕ) = 0 then 0 else f 0) + sumF f (GBits.recut P _) = _
      rw [if_pos rfl, zero_add]
      exact ih g h
  | msg r1 r2 u P ih =>
      rintro ⟨b1, b2, g⟩ ⟨h1, h⟩
      obtain rfl : b1 = 0 := h1
      refine (ih (b2, g) h).trans ?_
      exact (sumF_cons0 f (r := r1) (s := r2 :: _) (show GBits (r2 :: _) from (b2, g))).symm
  | chal r1 r2 np P ih =>
      rintro ⟨b1, b2, g⟩ ⟨h1, h⟩
      refine (ih (max b1 b2, g) h).trans ?_
      show (if max b1 b2 = 0 then 0 else f (max b1 b2)) + sumF f g =
        (if b1 = 0 then 0 else f b1) + ((if b2 = 0 then 0 else f b2) + sumF f g)
      rcases h1 with h0 | h0
      · obtain rfl : b1 = 0 := h0
        rw [Nat.zero_max, if_pos rfl, zero_add]
      · obtain rfl : b2 = 0 := h0
        rw [Nat.max_zero, if_pos rfl, zero_add]

theorem recutEx_keepAll : ∀ {s : Shape} (g : GBits s), RecutEx (XPlan.keepAll s) g
  | [], _ => trivial
  | _ :: _, (_, g) => recutEx_keepAll g

theorem recutEx_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (g' : GBits t) (hQ : RecutEx Q g') :
    ∀ g : GBits s, RecutEx P g → RecutEx (XPlan.app P Q) (GBits.app g g') := by
  induction P with
  | nil => intro _ _; exact hQ
  | keep r P ih => exact fun g h => ih g.2 h
  | cut c P ih => exact fun g h => ih g h
  | msg r1 r2 u P ih => exact fun g h => ⟨h.1, ih g.2 h.2⟩
  | chal r1 r2 np P ih => exact fun g h => ⟨h.1, ih (max g.1 g.2.1, g.2.2) h.2⟩

theorem recutEx_thenX {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s))
    (g : ℕ × GBits s) (h : RecutEx X (show GBits (p.last :: s) from g)) :
    RecutEx (p.thenX X) (show GBits (r :: s) from g) := by
  induction p with
  | keep r => exact h
  | cut c rest ih => exact ih X h

theorem recutEx_zero {s : Shape} (P : XPlan s) : RecutEx P (GBits.zero s) := by
  induction P with
  | nil => trivial
  | keep r P ih => exact ih
  | cut c P ih => exact ih
  | msg r1 r2 u P ih => exact ⟨rfl, ih⟩
  | chal r1 r2 np P ih => exact ⟨Or.inl rfl, ih⟩

/-- n copies of a round r without bits, before a list t. The plan `XPlan.repLast r n X0 X1`
(Iop/RecutKit.lean) is X0, a plan of t, for n = 0; else it keeps all copies but the last and goes on
with X1, a plan of the last copy and t, so that the last copy may be merged with what follows. It
has `RecutEx` if X0 and X1 have it. -/
theorem recutEx_repLast0 (r : Round) :
    ∀ (n : ℕ) {t : Shape} (X0 : XPlan t) (X1 : XPlan (r :: t)) (g : GBits t), RecutEx X0 g →
      RecutEx X1 (show GBits (r :: t) from (0, g)) →
      RecutEx (XPlan.repLast r n X0 X1) (GBits.rep r 0 n g)
  | 0, _, _, _, _, h0, _ => h0
  | 1, _, _, _, _, _, h1 => h1
  | n + 2, _, X0, X1, g, h0, h1 => recutEx_repLast0 r (n + 1) X0 X1 g h0 h1

end GBits
end Iop
