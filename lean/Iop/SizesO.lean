-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SizesO.lean: sums for bounds on the sizes of proof strings with pruned Merkle paths.

The counterpart of the second half of Iop/Sizes.lean (`entBits`, `entSum`), which is for a whole
path at each opening (words of this library: lean/GLOSSARY.md).
In the format with pruned paths an opened position is encoded without a path, and all sibling
digests of a proof string are in one list (Compile/Batch/Pruned.lean, Compile/Batch/SizeO.lean). In
a protocol with slots a round has two trees (Iop/BatchWire.lean; `has0`, `hasJ`: whether a
component has a tree at all): the tree of the shared component of the prover message and the tree
of the slot's component. In this file's sums a list of flags `fl` has one number for each round. A
flag that is not 0 says that both Merkle trees of the round have pruned paths; the flag 0, that
every opening has a separate path. The wire record has a flag for each tree (`pr0`, `prJ`,
Iop/BatchWire.lean).
  `octB d nT n`: (sum over k < d - 1 of min (n, nT * 2^k)) + min (n, nT). It is an upper bound on
      the number of digests that a traversal (the joint verification of Hash/Octopus.lean) takes
      (`Octopus.need`, there), for a traversal from at most n leaves, in strictly ascending order,
      of nT trees of depth d (`Octopus.need_le_octMax`, Hash/OctopusFacts.lean). It is the same
      number as `Octopus.octMax` (Hash/OctopusFacts.lean), defined again because Iop/ does not
      import Hash/; that they are the same is `Compile.Batch.octB_eq` (by definition)
  `sibC fl d n`: the sibling digests of one round with n openings in trees of depth d: n * d (flag
      0); octB d 2 n (flag not 0: the two trees of the round as one forest)
  `entBitsO`, `entSumO`: the bits of one opening without path; of all lists of openings
  `newSum`: these and the sibling digests of all rounds (`sibList`), in bits: for each round gam n +
      n * entBitsO + lam * sibC (lam: the bits of a digest; `gam n`, Iop/Ser.lean: the bits of a
      length prefix n); `newSum_eq`: = entSumO + lam * sibList
  `newSum_zero_le`: with all flags 0, `newSum` is at most `entSum`: what is saved are the length
      prefixes of the paths
  `newSum_app_zero_le`, `sibList_app_zero_le`, `sibList_zero_le`: a part with any flags and after it
      a part whose flags are all 0: a statement "`entSum` of both is at most `entSum` of the first
      part plus T" turns into the same statement on `newSum` (see the docstrings). So the bounds
      that are proved for whole paths can be used unchanged for all parts whose flags are 0.

Notation: `OpenList s : Type` (Iop/SerS.lean): for each round a number; in `sibList` and `newSum`
of this type are `fl` (the flags), `d` (the depths of the Merkle trees) and `o` (how many positions
are opened at most); `BitsS s : Type` (Iop/SerS.lean): for each round two numbers: the bits of a
pair (position, symbol), and the bits of the plain part; `Samplers s : Type 1` (Iop/Pull.lean): one
sampler for each round; `Shape.pull s σ : Shape` (there): the rounds `r.pull σ`: the same round
with an element of the sampler's source Src as challenge.

Limits: of these, Compile/Batch/SizeO.lean uses `entBitsO`, `entSumO` and `octB`; no theorem of this
library compares `sibC`, `sibList` or `newSum` with a proof string.
-/
import Iop.Sizes
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Iop
open Ser (gam)

/-- an upper bound on the number of digests that a traversal from at most n leaves, in strictly
ascending order, of nT trees of depth d takes (`Octopus.need_le_octMax`, Hash/OctopusFacts.lean) -/
def octB (d nT n : ℕ) : ℕ := (∑ k ∈ Finset.range (d - 1), min n (nT * 2 ^ k)) + min n nT

theorem octB_mono {d d' n n' : ℕ} (nT : ℕ) (hd : d ≤ d') (hn : n ≤ n') :
    octB d nT n ≤ octB d' nT n' :=
  Nat.add_le_add (le_trans (Finset.sum_le_sum fun _ _ => min_le_min_right _ hn)
      (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le_sub_right hd 1))))
    (min_le_min_right _ hn)

/-- the sibling digests of one round -/
def sibC (fl d n : ℕ) : ℕ := if fl = 0 then n * d else octB d 2 n

theorem sibC_mono (fl : ℕ) {d d' n n' : ℕ} (hd : d ≤ d') (hn : n ≤ n') :
    sibC fl d n ≤ sibC fl d' n' := by
  unfold sibC
  split_ifs
  · exact Nat.mul_le_mul hn hd
  · exact octB_mono 2 hd hn

/-- the bits of one opening without path: x for (position, symbol), and a salt of at most sMT bits
with its length prefix -/
def entBitsO (sMT x : ℕ) : ℕ := x + (gam sMT + sMT * 1)

theorem entBitsO_mono (sMT : ℕ) {x x' : ℕ} (h : x ≤ x') : entBitsO sMT x ≤ entBitsO sMT x' :=
  Nat.add_le_add_right h _

/-- an opening with a path is an opening without, and the path with its length prefix -/
theorem entBits_eq (lam sMT d x : ℕ) :
    entBits lam sMT d x = entBitsO sMT x + (gam d + d * lam) := by
  unfold entBits entBitsO
  omega

/-- the bits of the lists of opened positions without paths, a sum over the rounds -/
def entSumO (sMT : ℕ) : (s : Shape) → BitsS s → OpenList s → ℕ
  | [], _, _ => 0
  | _ :: s, ((x, _), t), (n, o) => (gam n + n * entBitsO sMT x) + entSumO sMT s t o

/-- the sibling digests of all rounds -/
def sibList : (s : Shape) → (fl d o : OpenList s) → ℕ
  | [], _, _, _ => 0
  | _ :: s, (f, fs), (d, ds), (n, o) => sibC f d n + sibList s fs ds o

/-- the bits of the lists of opened positions and of their sibling digests -/
def newSum (lam sMT : ℕ) : (s : Shape) → (fl d : OpenList s) → BitsS s → (o : OpenList s) → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (f, fs), (d, ds), ((x, _), t), (n, o) =>
    (gam n + n * entBitsO sMT x + lam * sibC f d n) + newSum lam sMT s fs ds t o

theorem newSum_eq (lam sMT : ℕ) :
    ∀ (s : Shape) (fl d : OpenList s) (b : BitsS s) (o : OpenList s),
      newSum lam sMT s fl d b o = entSumO sMT s b o + lam * sibList s fl d o
  | [], _, _, _, _ => rfl
  | _ :: s, (f, fs), (d, ds), ((x, _), t), (n, o) => by
      show (gam n + n * entBitsO sMT x + lam * sibC f d n) + newSum lam sMT s fs ds t o =
        ((gam n + n * entBitsO sMT x) + entSumO sMT s t o) + lam * (sibC f d n + sibList s fs ds o)
      rw [newSum_eq lam sMT s fs ds t o, Nat.mul_add]
      omega

theorem sibList_mul_le (lam sMT : ℕ) (s : Shape) (fl d : OpenList s)
    (b : BitsS s) (o : OpenList s) :
    lam * sibList s fl d o ≤ newSum lam sMT s fl d b o := by
  rw [newSum_eq]
  exact Nat.le_add_left _ _

theorem newSum_app (lam sMT : ℕ) :
    ∀ {s t : Shape} (fl : OpenList s) (fl' : OpenList t) (d : OpenList s) (d' : OpenList t)
        (b : BitsS s) (b' : BitsS t) (o : OpenList s) (o' : OpenList t),
      newSum lam sMT (s ++ t) (OpenList.app fl fl') (OpenList.app d d')
          (BitsS.app b b') (OpenList.app o o') =
        newSum lam sMT s fl d b o + newSum lam sMT t fl' d' b' o'
  | [], _, _, _, _, _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (f, fs), fl', (d, ds), d', ((x, _), b), b', (n, o), o' => by
      show (gam n + n * entBitsO sMT x + lam * sibC f d n) +
          newSum lam sMT _ (OpenList.app fs fl') (OpenList.app ds d')
            (BitsS.app b b') (OpenList.app o o') = _
      rw [newSum_app lam sMT fs fl' ds d' b b' o o', ← Nat.add_assoc]
      rfl

theorem sibList_app :
    ∀ {s t : Shape} (fl : OpenList s) (fl' : OpenList t) (d : OpenList s) (d' : OpenList t)
        (o : OpenList s) (o' : OpenList t),
      sibList (s ++ t) (OpenList.app fl fl') (OpenList.app d d') (OpenList.app o o') =
        sibList s fl d o + sibList t fl' d' o'
  | [], _, _, _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (f, fs), fl', (d, ds), d', (n, o), o' => by
      show sibC f d n + sibList _ (OpenList.app fs fl') (OpenList.app ds d') (OpenList.app o o') = _
      rw [sibList_app fs fl' ds d' o o', ← Nat.add_assoc]
      rfl

theorem newSum_pull (lam sMT : ℕ) :
    ∀ (s : Shape) (σ : Samplers s) (fl d : OpenList s) (b : BitsS s) (o : OpenList s),
      newSum lam sMT (Shape.pull s σ) (OpenList.pull s σ fl) (OpenList.pull s σ d)
          (BitsS.pull s σ b) (OpenList.pull s σ o) =
        newSum lam sMT s fl d b o
  | [], _, _, _, _, _ => rfl
  | _ :: s, (_, σs), (f, fs), (d, ds), ((x, _), b), (n, o) =>
    congrArg ((gam n + n * entBitsO sMT x + lam * sibC f d n) + ·)
      (newSum_pull lam sMT s σs fs ds b o)

theorem sibList_pull :
    ∀ (s : Shape) (σ : Samplers s) (fl d o : OpenList s),
      sibList (Shape.pull s σ) (OpenList.pull s σ fl) (OpenList.pull s σ d) (OpenList.pull s σ o) =
        sibList s fl d o
  | [], _, _, _, _ => rfl
  | _ :: s, (_, σs), (f, fs), (d, ds), (n, o) =>
    congrArg (sibC f d n + ·) (sibList_pull s σs fs ds o)

theorem entSumO_pull (sMT : ℕ) :
    ∀ (s : Shape) (σ : Samplers s) (b : BitsS s) (o : OpenList s),
      entSumO sMT (Shape.pull s σ) (BitsS.pull s σ b) (OpenList.pull s σ o) = entSumO sMT s b o
  | [], _, _, _ => rfl
  | _ :: s, (_, σs), ((x, _), b), (n, o) =>
    congrArg ((gam n + n * entBitsO sMT x) + ·) (entSumO_pull sMT s σs b o)

/-- With all flags 0, `newSum` is at most `entSum`. -/
theorem newSum_zero_le (lam sMT : ℕ) :
    ∀ (s : Shape) (d : OpenList s) (b : BitsS s) (o : OpenList s),
      newSum lam sMT s (OpenList.zero s) d b o ≤ entSum lam sMT s d b o
  | [], _, _, _ => Nat.le_refl _
  | _ :: s, (d, ds), ((x, _), t), (n, o) => by
      show (gam n + n * entBitsO sMT x + lam * sibC 0 d n) +
          newSum lam sMT s (OpenList.zero s) ds t o ≤
        (gam n + n * entBits lam sMT d x) + entSum lam sMT s ds t o
      refine Nat.add_le_add ?_ (newSum_zero_le lam sMT s ds t o)
      have e : sibC 0 d n = n * d := rfl
      rw [e, entBits_eq, Nat.mul_add, Nat.mul_add, Nat.mul_comm lam, Nat.mul_assoc]
      omega

/-- Under `hd`, `hx`, `hN`: `newSum` is at most the first round's term at d', x' plus N. -/
theorem newSum_cons_le (lam sMT : ℕ) {r : Round} {s : Shape} (fl d : OpenList (r :: s))
    (b : BitsS (r :: s)) (o : OpenList (r :: s)) {d' x' N : ℕ} (hd : d.1 ≤ d') (hx : b.1.1 ≤ x')
    (hN : newSum lam sMT s fl.2 d.2 b.2 o.2 ≤ N) :
    newSum lam sMT (r :: s) fl d b o ≤
      (gam o.1 + o.1 * entBitsO sMT x' + lam * sibC fl.1 d' o.1) + N := by
  obtain ⟨f, fs⟩ := fl
  obtain ⟨d0, ds⟩ := d
  obtain ⟨⟨x, y⟩, t⟩ := b
  obtain ⟨n, o⟩ := o
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left n (entBitsO_mono sMT hx)) _)
      (Nat.mul_le_mul_left lam (sibC_mono f hd (Nat.le_refl n)))) hN

/-- A part with any flags, and after it a part whose flags are all 0: whatever bounds `entSum` of
both by `entSum` of the first part and a number T, bounds `newSum` of both by `newSum` of the first
part and T. -/
theorem newSum_app_zero_le (lam sMT : ℕ) {s t : Shape} (fl : OpenList s) (d : OpenList s)
    (d' : OpenList t) (b : BitsS s) (b' : BitsS t) (o : OpenList s) (o' : OpenList t) {T : ℕ}
    (h : entSum lam sMT (s ++ t) (OpenList.app d d') (BitsS.app b b') (OpenList.app o o') ≤
      entSum lam sMT s d b o + T) :
    newSum lam sMT (s ++ t) (OpenList.app fl (OpenList.zero t)) (OpenList.app d d')
        (BitsS.app b b') (OpenList.app o o') ≤
      newSum lam sMT s fl d b o + T := by
  rw [entSum_app] at h
  rw [newSum_app]
  exact Nat.add_le_add_left
    (le_trans (newSum_zero_le lam sMT t d' b' o') (Nat.le_of_add_le_add_left h)) _

/-- For 0 < lam and `entSum` at most T, a part with all flags 0 has at most T / lam sibling digests.
-/
theorem sibList_zero_le {lam : ℕ} (hlam : 0 < lam) (sMT : ℕ) (t : Shape) (d' : OpenList t)
    (b' : BitsS t) (o' : OpenList t) {T : ℕ} (h : entSum lam sMT t d' b' o' ≤ T) :
    sibList t (OpenList.zero t) d' o' ≤ T / lam :=
  (Nat.le_div_iff_mul_le hlam).2 (by
    rw [Nat.mul_comm]
    exact le_trans (sibList_mul_le lam sMT t _ d' b' o')
      (le_trans (newSum_zero_le lam sMT t d' b' o') h))

/-- Under `h` of `newSum_app_zero_le` and 0 < lam, the second part's flags all 0: the sibling
digests of both parts are at most those of the first part plus T / lam. -/
theorem sibList_app_zero_le {lam : ℕ} (hlam : 0 < lam) (sMT : ℕ) {s t : Shape} (fl : OpenList s)
    (d : OpenList s) (d' : OpenList t) (b : BitsS s) (b' : BitsS t) (o : OpenList s)
    (o' : OpenList t) {T : ℕ}
    (h : entSum lam sMT (s ++ t) (OpenList.app d d') (BitsS.app b b') (OpenList.app o o') ≤
      entSum lam sMT s d b o + T) :
    sibList (s ++ t) (OpenList.app fl (OpenList.zero t)) (OpenList.app d d') (OpenList.app o o') ≤
      sibList s fl d o + T / lam := by
  rw [entSum_app] at h
  rw [sibList_app]
  exact Nat.add_le_add_left (sibList_zero_le hlam sMT t d' b' o' (Nat.le_of_add_le_add_left h)) _

/-- all flags 1 -/
def OpenList.ones : (s : Shape) → OpenList s
  | [] => ()
  | _ :: s => (1, OpenList.ones s)

end Iop
