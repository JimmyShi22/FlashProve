-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/BaseCounts.lean: THE TEST «THE PINNED TREES LIE BELOW THE PIECES' BASES» (BaseNums.lean: baseN | basesAllN; BasePins.lean: basesDoor) FROM LOWER BOUNDS ON A FEW SHORT STRETCHES: baseN walks the data anew at every border and sums over «take»s of thousands of rounds: at the key file's first chain (18,850 rounds) «decide +kernel» on the test itself aborted. BUT THE TEST ASKS ONLY «a seat's tree < a base»: A LOWER BOUND ON EACH BASE SERVES: countsLe ds rs cs: the i-th block's stretch sends AT LEAST cs[i] trees: at a stretch of which nothing is claimed (cs[i] = 0) NOTHING IS EVALUATED.
OBJECT: basesDoor at_ rs₁ rs₂ rs₃ D · USER: basesAll_of_door | four_of_all · LETTERS: all.
  countsLe     the walk, with lower bounds
  baseC        the n-th base off the bounds: baseN's own recursion
  baseC_le     PROVED: under countsLe, b ≤ b': baseC b cs rs n ≤ baseN b' ds rs n
  sum_le       PROVED: under countsLe: cs.sum ≤ treesOf ds (for the later chains' first bases)
  basesDoorC   the door's test on the short lists
  basesDoor_of_lower   PROVED
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.BasePins

set_option autoImplicit false

namespace LPFD
open OnBytes.Maker

theorem treesOf_split (ds : List RDT) (r : Nat) : treesOf ds = treesOf (ds.take r) + treesOf (ds.drop r) := by
  unfold treesOf
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

/-- The i-th block's stretch sends at least cs[i] trees. -/
def countsLe : List RDT → List Nat → List Nat → Prop
  | _, [], [] => True
  | ds, r :: rs, c :: cs => c ≤ treesOf (ds.take r) ∧ countsLe (ds.drop r) rs cs
  | _, _, _ => False

/-- The n-th base off the bounds: baseN's own recursion. -/
def baseC : Nat → List Nat → List Nat → Nat → Nat
  | base, _, [], _ => base
  | base, _, [_], _ => base
  | base, _, _ :: _ :: _, 0 => base
  | base, [], _ :: _ :: _, _ + 1 => base
  | base, c :: cs, _ :: r' :: rs, n + 1 => baseC (base + c) cs (r' :: rs) n

theorem baseC_le : ∀ (rs cs : List Nat) (ds : List RDT) (b b' n : Nat), countsLe ds rs cs → b ≤ b' → baseC b cs rs n ≤ baseN b' ds rs n
  | [], _, _, _, _, _, _, hb => by simpa [baseN, baseC] using hb
  | [_], _, _, _, _, _, _, hb => by simpa [baseN, baseC] using hb
  | _ :: _ :: _, _, _, _, _, 0, _, hb => by simpa [baseN, baseC] using hb
  | _ :: _ :: _, [], _, _, _, _ + 1, h, _ => absurd h (by simp [countsLe])
  | r :: r' :: rs, c :: cs, ds, b, b', n + 1, h, hb => by
    have h' : c ≤ treesOf (ds.take r) ∧ countsLe (ds.drop r) (r' :: rs) cs := h
    show baseC (b + c) cs (r' :: rs) n ≤ baseN (b' + treesOf (ds.take r)) (ds.drop r) (r' :: rs) n
    exact baseC_le (r' :: rs) cs (ds.drop r) (b + c) (b' + treesOf (ds.take r)) n h'.2 (Nat.add_le_add hb h'.1)

theorem sum_le : ∀ (rs cs : List Nat) (ds : List RDT), countsLe ds rs cs → cs.sum ≤ treesOf ds
  | [], [], _, _ => Nat.zero_le _
  | [], _ :: _, _, h => absurd h (by simp [countsLe])
  | _ :: _, [], _, h => absurd h (by simp [countsLe])
  | r :: rs, c :: cs, ds, h => by
    have h' : c ≤ treesOf (ds.take r) ∧ countsLe (ds.drop r) rs cs := h
    rw [List.sum_cons, treesOf_split ds r]
    exact Nat.add_le_add h'.1 (sum_le rs cs (ds.drop r) h'.2)

theorem t₁_eq (D : WholeD) : D.t₁ = treesOf D.ds₁ := rfl
theorem t₂_eq (D : WholeD) : D.t₂ = treesOf D.ds₂ := rfl

/-- The door's test, on the short lists. u₂ u₃: lower bounds on the later chains' first bases. -/
def basesDoorC (at_ : Nat → Nat × Nat) (rs₁ rs₂ rs₃ cs₁ cs₂ cs₃ : List Nat) (u₂ u₃ : Nat) : Bool :=
  ((List.range rs₁.length).all fun n => (pinW pinsW₁ n).all fun j => decide ((at_ j).1 < baseC 0 cs₁ rs₁ n)) &&
  ((List.range rs₂.length).all fun n => (pinW pinsW₂ n).all fun j => decide ((at_ j).1 < baseC u₂ cs₂ rs₂ n)) &&
  ((List.range rs₃.length).all fun n => (pinW pinsW₃ n).all fun j => decide ((at_ j).1 < baseC u₃ cs₃ rs₃ n))

theorem basesDoor_of_lower (at_ : Nat → Nat × Nat) (rs₁ rs₂ rs₃ cs₁ cs₂ cs₃ : List Nat) (D : WholeD) (u₂ u₃ : Nat)
    (h₁ : countsLe D.ds₁ rs₁ cs₁) (h₂ : countsLe D.ds₂ rs₂ cs₂) (h₃ : countsLe D.ds₃ rs₃ cs₃) (e₂ : u₂ ≤ D.t₁) (e₃ : u₃ ≤ D.t₁ + D.t₂)
    (h : basesDoorC at_ rs₁ rs₂ rs₃ cs₁ cs₂ cs₃ u₂ u₃ = true) : basesDoor at_ rs₁ rs₂ rs₃ D = true := by
  unfold basesDoor basesAllN
  unfold basesDoorC at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨fun n hn j hj => Nat.lt_of_lt_of_le (h.1.1 n hn j hj) (baseC_le rs₁ cs₁ D.ds₁ 0 0 n h₁ (Nat.le_refl _)),
    fun n hn j hj => Nat.lt_of_lt_of_le (h.1.2 n hn j hj) (baseC_le rs₂ cs₂ D.ds₂ u₂ D.t₁ n h₂ e₂)⟩,
    fun n hn j hj => Nat.lt_of_lt_of_le (h.2 n hn j hj) (baseC_le rs₃ cs₃ D.ds₃ u₃ (D.t₁ + D.t₂) n h₃ e₃)⟩

end LPFD

#print axioms LPFD.baseC_le
#print axioms LPFD.sum_le
#print axioms LPFD.basesDoor_of_lower
