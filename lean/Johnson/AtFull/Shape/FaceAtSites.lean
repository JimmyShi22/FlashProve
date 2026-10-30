-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FaceAtSites.lean: AT EVERY SITE OF THE LOOKUPS' LOT THE FACE PASSES THE
HEARING's OWN TEST ON ITS NUMBERS (`Face.ok`, Johnson/Desc/First/Look/K3LookupGeneral.lean). A GENERAL
LAW: at every public part; no head, no scope, no size; nothing is evaluated.

Why. The lookups' `faceOf_ok` (Johnson/Desc/ProofFile/Honest/K3/Law/FaceOk.lean) leads to `Face.ok`
from two tests on the shape: `FoNums.ok`, which their `sites_shape_ok`
(Johnson/Desc/ProofFile/Honest/K3/Law/SitesOk.lean) has at every site, and `someKey`: not all keys
of the face are padding. The second follows from the first together with the test on the numbers of
padding keys, `pubOk` (Johnson/Desc/First/Look/ShapeOwn.lean), without which no shape is made
(`P.shape`, Johnson/Desc/First/Look/LookKind.lean).

The argument. The face's padding is the keys of the trees that hold only padding, (2^rK - NT) 2^dT,
and each tree's own count. `pubOk` says that a tree's count is at most 2^dT, and that the counts of
one call's 2^i trees sum to less than 2^(dT + i): so one of these trees has a count below 2^dT. By
`FoNums.ok` there is a call, and its trees are among the NT. So the NT counts sum to less than NT
2^dT, and with NT ≤ 2^rK the padding is below 2^rK 2^dT = 2^v.

Main names.
* `sum_le_range`, `sum_lt_range`, `le_sum_range`, `foldl_add_list`, `foldl_add_range`: five small
  laws on sums over a list and over `List.range`.
* `someKey_of_pubOk`: for every shape h: `FoNums.ok h = true` and `pubOk h h.pub = true` give
  `someKey h = true`.
* `pubOk_site`: at every site: `pubOk s.shape s.shape.pub = true`.
* `face_ok_site`: for every public part Z and every s in `lookSites Z`: `s.at_.face.ok = true`.

Limits. It says that a test on public numbers accepts wherever a site is made; that a site is made
is Johnson/AtFull/Shape/SitesAtHead.lean's. Of the face it says nothing beyond that test's yes.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.FaceOk
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes.Model (Forest.Shape)
open VerifiableInference.Desc.First.Look (pubOk shapeOwn)
open VerifiableInference.Desc.K3 (faceOf)
open ProofFile.Honest.K3 (Site lookSites)
open ProofFile.Honest.K3.Law (site_made_shape sites_shape_ok)
open ProofFile.Honest.K3.Law.Spec (someKey faceOf_ok)

/-! ## 1 Sums over a range -/

/-- Where each of the first n values is at most M, their sum is at most n M. -/
theorem sum_le_range (f : Nat → Nat) (M : Nat) : ∀ n : Nat, (∀ y < n, f y ≤ M) →
    ((List.range n).map f).sum ≤ n * M
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, Nat.succ_mul]
    have h1 := sum_le_range f M n fun y hy => h y (by omega)
    have h2 := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- Where, besides, one of them is below M, the sum is below n M. -/
theorem sum_lt_range (f : Nat → Nat) (M : Nat) : ∀ n : Nat, (∀ y < n, f y ≤ M) →
    (∃ y < n, f y < M) → ((List.range n).map f).sum < n * M
  | 0, _, ⟨_, hy, _⟩ => by omega
  | n + 1, h, ⟨y, hy, hlt⟩ => by
    rw [List.range_succ, List.map_append, List.sum_append, Nat.succ_mul]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases e : y = n
    · subst e
      have h1 := sum_le_range f M y fun z hz => h z (by omega)
      omega
    · have h1 := sum_lt_range f M n (fun z hz => h z (by omega)) ⟨y, by omega, hlt⟩
      have h2 := h n (by omega)
      omega

/-- Where each of the first n values is at least M, their sum is at least n M. -/
theorem le_sum_range (f : Nat → Nat) (M : Nat) : ∀ n : Nat, (∀ y < n, M ≤ f y) →
    n * M ≤ ((List.range n).map f).sum
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, Nat.succ_mul]
    have h1 := le_sum_range f M n fun y hy => h y (by omega)
    have h2 := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- A fold that starts at a and adds g b for each member b of l gives a plus the sum of g over l. -/
theorem foldl_add_list (g : Nat → Nat) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun s b => s + g b) a = a + (l.map g).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_list g l, List.map_cons, List.sum_cons]
    omega

/-- So such a fold over `List.range n` that starts at 0 gives the sum of g over `List.range n`. -/
theorem foldl_add_range (g : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun s b => s + g b) 0 = ((List.range n).map g).sum := by
  rw [foldl_add_list, Nat.zero_add]

/-! ## 2 Not all keys are padding -/

/-- **WHERE A SHAPE PASSES THE TEST ON ITS NUMBERS (`FoNums.ok`) AND THE TEST ON ITS NUMBERS OF
PADDING KEYS (`pubOk`), NOT ALL KEYS OF THE FACE ARE PADDING.** Two premises; the proof uses
both. -/
theorem someKey_of_pubOk (h : Forest.Shape) (hok : FoNums.ok h = true)
    (hp : pubOk h h.pub = true) : someKey h = true := by
  obtain ⟨⟨-, a2, -, a4, -, -, -⟩, -, c, -⟩ := Cb.Fo.ok_parts hok
  unfold pubOk at hp
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hp
  obtain ⟨⟨-, p3⟩, p4⟩ := hp
  -- a tree's count is at most 2^dT
  have hle : ∀ y, h.pub.getD y 0 ≤ 2 ^ h.dT := by
    intro y
    by_cases hy : y < h.pub.size
    · have := (Array.all_iff_forall.1 p3) y hy
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy]
      simpa using this ⟨Nat.zero_le _, hy⟩
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact Nat.zero_le _
  -- one tree of call 0 has a count below 2^dT
  have h0 := p4 0 a2
  rw [foldl_add_range (fun b => h.pub.getD (h.first.getD 0 0 + b) 0), Nat.pow_add,
    Nat.mul_comm] at h0
  have hex : ∃ b < 2 ^ h.iota.getD 0 0, h.pub.getD (h.first.getD 0 0 + b) 0 < 2 ^ h.dT := by
    by_contra hn
    have hall : ∀ b < 2 ^ h.iota.getD 0 0, 2 ^ h.dT ≤ h.pub.getD (h.first.getD 0 0 + b) 0 :=
      fun b hb => Nat.le_of_not_lt fun hlt => hn ⟨b, hb, hlt⟩
    have := le_sum_range (fun b => h.pub.getD (h.first.getD 0 0 + b) 0) (2 ^ h.dT) _ hall
    omega
  obtain ⟨b, hb, hlt⟩ := hex
  have hin : h.first.getD 0 0 + b < h.NT := ((c 0 a2).2.2.2 b hb).1
  -- so the NT counts sum to less than NT 2^dT
  have hs := sum_lt_range (fun y => h.pub.getD y 0) (2 ^ h.dT) h.NT (fun y _ => hle y)
    ⟨_, hin, hlt⟩
  unfold someKey
  refine decide_eq_true ?_
  have e : ((faceOf h).padding.map (·.1)).sum =
      h.emptyKeys + ((List.range h.NT).map fun y => h.pub.getD y 0).sum := by
    unfold faceOf
    simp only [List.map_cons, List.sum_cons, List.map_map]
    rfl
  rw [e]
  have ev : 2 ^ h.v = 2 ^ h.rK * 2 ^ h.dT := by
    show 2 ^ (h.dT + h.rK) = _
    rw [Nat.pow_add, Nat.mul_comm]
  have ee : h.emptyKeys + h.NT * 2 ^ h.dT = 2 ^ h.rK * 2 ^ h.dT := by
    show (2 ^ h.rK - h.NT) * 2 ^ h.dT + h.NT * 2 ^ h.dT = _
    rw [← Nat.add_mul, Nat.sub_add_cancel a4]
  omega

/-! ## 3 At every site -/

/-- At every site the test on the numbers of padding keys accepts. -/
theorem pubOk_site (Z : ProofFile.Pub) (s : Site) (hs : s ∈ lookSites Z) :
    pubOk s.shape s.shape.pub = true := by
  unfold lookSites at hs
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hs
  obtain ⟨-, h2⟩ := site_made_shape _ _ x s hx
  unfold VerifiableInference.Desc.First.Look.P.shape at h2
  obtain ⟨h0, -, e1⟩ := Option.bind_eq_some_iff.1 h2
  by_cases hpk : pubOk h0 s.p.pub = true
  · rw [if_pos hpk] at e1
    rw [← Option.some.inj e1]
    exact hpk
  · rw [if_neg hpk] at e1
    cases e1

/-- **AT EVERY SITE THE FACE PASSES THE HEARING's OWN TEST.** -/
theorem face_ok_site (Z : ProofFile.Pub) (s : Site) (hs : s ∈ lookSites Z) :
    s.at_.face.ok = true := by
  obtain ⟨h1, h2⟩ := sites_shape_ok Z s hs
  rw [h1]
  exact faceOf_ok s.shape h2 (someKey_of_pubOk s.shape h2 (pubOk_site Z s hs))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sum_le_range
#print axioms Johnson.AtFull.Shape.sum_lt_range
#print axioms Johnson.AtFull.Shape.le_sum_range
#print axioms Johnson.AtFull.Shape.foldl_add_list
#print axioms Johnson.AtFull.Shape.foldl_add_range
#print axioms Johnson.AtFull.Shape.someKey_of_pubOk
#print axioms Johnson.AtFull.Shape.pubOk_site
#print axioms Johnson.AtFull.Shape.face_ok_site
