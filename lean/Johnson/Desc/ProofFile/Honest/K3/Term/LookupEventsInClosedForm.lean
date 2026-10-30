-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: A COUNT OF THE VERIFIER's CHALLENGES ALONE: no prover, no filling, no run and no coin is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupEventsInClosedForm.lean: the kind "lookup" (K3): HOW MANY EVENTS THE
LOOKUPS' MARKS COUNT, AS NUMBERS. An event is "one named drawn field element (three words) of one named round of the
lookup's own member has one named value". The numerators of the marks' stated shares (`events`, `eventsOut`,
Honest/K3/GoodDraws.lean) are sums over lists; here they are tied to the closed forms that stand beside them there
(`eventsAt`, `eventsOutAt`), bounded, added up over the fifty lookups, and multiplied by the bound at one value.

  `eventsOfAShapeInClosedForm`, `eventsOutOfAShapeInClosedForm`   at the face of a shape with 2 ^ v keys and 2 ^ d rows
  `lookupEventsOfSizes v d`   v (v - 1) / 2 + d (d - 1) / 2 + 5 v + 14 d + 72: both marks of one lookup
  `lookupEventsAtSiteInClosedForm`, `lookupEventsAtSiteAtMost`   at a site; at most 1591 (v, d at most 31)
  `lookupEventsInAllAtMost`   under the head: at most 79550 at the fifty sites
  `allLookupMarksTogetherAreSmall`   79550 times the bound at one value is at most 1 / 2 ^ 175
  `lookupMarksWholeShare`   **under the head: the numbers at which the hundred marks pay
      (`lookupMarksPayAtAWrittenNumber`) add up to at most 1 / 2 ^ 175**

Limits. The last but two and the last are conditional on the library's head `P5J.AtMgA`: the full size alone. The
bounds 1591 and 79550 are at the largest sizes that the public test on a shape allows, not at the plan's own sizes,
which are smaller. Both marks' events are counted, though the second mark's silence has no user in this folder yet. A
sum of numbers: that the measure of "some mark of the lookups speaks" is at most this sum is the
frame's law on the first chain, not this file's.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupMarksPayAtAWrittenNumber
import Johnson.P1K8R.DeadMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open scoped ENNReal
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.K3 (faceOf)
open OnBytes.Model.Forest (Shape)
open OnBytes.Maker (RDT WholeD)
open ProofFile.Honest.K3.Good

/-! ## 1 Sums over lists -/

/-- A sum over a list made piece by piece is the sum of the pieces' sums. -/
theorem sumOverPieces {α β : Type} (l : List α) (F : α → List β) (w : β → ℕ) :
    ((l.flatMap F).map w).sum = (l.map fun a => ((F a).map w).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- What a spot counts: two events where 0 and 1 are forbidden, one where 0 alone is. -/
def eventsOfSpot (p : Spot) : ℕ := if p.one then 2 else 1

theorem spotsThatForbidZeroAlone {α : Type} (l : List α) (g : α → Spot) (hg : ∀ a, (g a).one = false) :
    ((l.map g).map eventsOfSpot).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.length_cons]
    unfold eventsOfSpot
    rw [hg a]
    simp only [Bool.false_eq_true, if_false]
    omega

theorem spotsThatForbidZeroAndOne {α : Type} (l : List α) (g : α → Spot) (hg : ∀ a, (g a).one = true) :
    ((l.map g).map eventsOfSpot).sum = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.length_cons]
    unfold eventsOfSpot
    rw [hg a]
    simp only [if_true]
    omega

theorem triangleStep (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  cases n with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]

/-- c + 0, c + 1, …, c + (n - 1) add up to c n + n (n - 1) / 2. -/
theorem sumOfARisingRow (c n : ℕ) : ((List.range n).map fun m => c + m).sum = c * n + n * (n - 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.sum_range_succ, ih, triangleStep]
    generalize n * (n - 1) / 2 = T
    ring

/-! ## 2 A stage's events -/

/-- The events of one stage's spots. -/
def eventsOfStage (f : LFace) (s : Stage) : ℕ := ((spotsAt f s).map eventsOfSpot).sum

theorem eventsByStage (f : LFace) : events f = ((stages f).map (eventsOfStage f)).sum :=
  sumOverPieces (stages f) (spotsAt f) eventsOfSpot

theorem eventsOfKeyLevel (f : LFace) (i m : ℕ) : eventsOfStage f (.key i m) = 1 + m := by
  show (([(⟨.key i m, 0, 0, false⟩ : Spot)] ++
    (List.range (levelCall m).vs.length).map fun l => (⟨.key i m, 1 + l, 0, false⟩ : Spot)).map eventsOfSpot).sum = _
  rw [List.map_append, List.sum_append, spotsThatForbidZeroAlone _ _ (fun _ => rfl), List.length_range, level_vars]
  rfl

theorem eventsOfTableLevel (f : LFace) (l : ℕ) : eventsOfStage f (.tab l) = 1 + (f.mu + l) := by
  show (([(⟨.tab l, 0, 0, false⟩ : Spot)] ++
    (List.range (levelCall (f.mu + l)).vs.length).map fun j => (⟨.tab l, 1 + j, 0, false⟩ : Spot)).map
      eventsOfSpot).sum = _
  rw [List.map_append, List.sum_append, spotsThatForbidZeroAlone _ _ (fun _ => rfl), List.length_range, level_vars]
  rfl

theorem eventsOfLeaves (f : LFace) : eventsOfStage f .leaves = 1 + (f.mu + f.d) := by
  show (([(⟨.leaves, 0, 0, false⟩ : Spot)] ++
    (List.range (VerifiableInference.Desc.K3.leafVars f #[]).length).map
      fun j => (⟨.leaves, 1 + j, 0, false⟩ : Spot)).map eventsOfSpot).sum = _
  rw [List.map_append, List.sum_append, spotsThatForbidZeroAlone _ _ (fun _ => rfl), List.length_range, leaf_vars]
  rfl

theorem eventsOfBits (f : LFace) : eventsOfStage f .bits = f.mu + f.d := by
  show (((List.range (VerifiableInference.Desc.K3.bitsCall
    (List.replicate (f.mu + f.d) OnBytes.zeroE)).vs.length).map
      fun j => (⟨.bits, 1 + j, 0, false⟩ : Spot)).map eventsOfSpot).sum = _
  rw [spotsThatForbidZeroAlone _ _ (fun _ => rfl), List.length_range, bits_vars]

theorem eventsOfJoin (f : LFace) : eventsOfStage f .join = 2 * f.mu := by
  show (((List.range f.mu).map fun k => (⟨.join, 0, k, true⟩ : Spot)).map eventsOfSpot).sum = _
  rw [spotsThatForbidZeroAndOne _ _ (fun _ => rfl), List.length_range]

theorem sumOfOnes {α : Type} (l : List α) (g : α → ℕ) (hg : ∀ a, g a = 1) : (l.map g).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, hg a, List.length_cons]
    omega

/-- The tie's first step counts nothing; each later step counts its eps. -/
theorem eventsOfTieSteps (f : LFace) (n : ℕ) :
    (((List.range (n + 1)).map Stage.tie).map (eventsOfStage f)).sum = n := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.sum_cons, List.map_map, List.map_map,
    sumOfOnes (List.range n) ((eventsOfStage f ∘ Stage.tie) ∘ Nat.succ) (fun _ => rfl), List.length_range]
  show 0 + n = n
  omega

theorem eventsOfKeyLevels (f : LFace) (i v : ℕ) :
    (((List.range v).flatMap fun m => [Stage.key i m, Stage.keyLine i m]).map (eventsOfStage f)).sum =
      3 * v + v * (v - 1) / 2 := by
  rw [sumOverPieces, ← sumOfARisingRow]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  show eventsOfStage f (.key i m) + (eventsOfStage f (.keyLine i m) + 0) = 3 + m
  rw [eventsOfKeyLevel]
  show 1 + m + (2 + 0) = 3 + m
  omega

theorem eventsOfTableLevels (f : LFace) (d : ℕ) :
    (((List.range d).flatMap fun l => [Stage.tab l, Stage.tabLine l]).map (eventsOfStage f)).sum =
      (3 + f.mu) * d + d * (d - 1) / 2 := by
  rw [sumOverPieces, ← sumOfARisingRow]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  show eventsOfStage f (.tab l) + (eventsOfStage f (.tabLine l) + 0) = 3 + f.mu + l
  rw [eventsOfTableLevel]
  show 1 + (f.mu + l) + (2 + 0) = 3 + f.mu + l
  omega

/-! ## 3 The closed forms -/

/-- The first mark's number of events, at a shape's face. -/
theorem eventsOfAShapeInClosedForm (h : Shape) : events (faceOf h) = eventsAt h.v h.d := by
  have hst : stages (faceOf h) = [Stage.shift] ++ [Stage.alpha] ++ (List.range 31).map Stage.tie ++
      (List.range 0).map Stage.split ++ [Stage.join] ++
      (((List.range h.v).flatMap fun m => [Stage.key 0 m, Stage.keyLine 0 m]) ++ []) ++
      ((List.range h.d).flatMap fun l => [Stage.tab l, Stage.tabLine l]) ++
      [Stage.leaves, Stage.zero, Stage.bits] := rfl
  have ties : (((List.range 31).map Stage.tie).map (eventsOfStage (faceOf h))).sum = 30 :=
    eventsOfTieSteps (faceOf h) 30
  rw [eventsByStage, hst]
  simp only [List.map_append, List.sum_append]
  rw [ties, eventsOfKeyLevels, eventsOfTableLevels]
  show 0 + 0 + 30 + 0 + (eventsOfStage (faceOf h) .join + 0) + (3 * h.v + h.v * (h.v - 1) / 2 + 0) +
    ((3 + 5) * h.d + h.d * (h.d - 1) / 2) +
    (eventsOfStage (faceOf h) .leaves + (0 + (eventsOfStage (faceOf h) .bits + 0))) = _
  rw [eventsOfJoin, eventsOfLeaves, eventsOfBits]
  show 0 + 0 + 30 + 0 + (2 * 5 + 0) + (3 * h.v + h.v * (h.v - 1) / 2 + 0) +
    ((3 + 5) * h.d + h.d * (h.d - 1) / 2) + (1 + (5 + h.d) + (0 + (5 + h.d + 0))) = _
  unfold eventsAt
  omega

/-- The second mark's number of events, at a shape's face with a key bit at least. -/
theorem eventsOutOfAShapeInClosedForm (h : Shape) (oneKeyBit : 1 ≤ h.v) :
    eventsOut (faceOf h) = eventsOutAt h.v h.d := by
  have hl : (spotsOut (faceOf h)).length = (h.v - 1 + 1 + 0) + (5 + h.d) + (5 + h.d) := by
    show ((((List.range (h.v - 1)).map fun l => (⟨.key 0 (h.v - 1), 1 + l, 0, true⟩ : Spot)) ++
      [(⟨.keyLine 0 (h.v - 1), 0, 0, true⟩ : Spot)] ++ []) ++
      (List.range (5 + h.d)).map (fun l => (⟨.leaves, 1 + l, 0, true⟩ : Spot)) ++
      (List.range (5 + h.d)).map fun l => (⟨.bits, 1 + l, 0, true⟩ : Spot)).length = _
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  unfold eventsOut eventsOutAt
  rw [hl]
  omega

/-- Both marks of one lookup with 2 ^ v keys and 2 ^ d rows. -/
def lookupEventsOfSizes (v d : ℕ) : ℕ := v * (v - 1) / 2 + d * (d - 1) / 2 + 5 * v + 14 * d + 72

/-- **The number of events at a site, in the letters of its shape.** No hypothesis but the site. -/
theorem lookupEventsAtSiteInClosedForm (Zp : ProofFile.Pub) (s : Site) (hs : s ∈ lookSites Zp) :
    lookupEventsAtSite s = lookupEventsOfSizes s.shape.v s.shape.d := by
  obtain ⟨h1, h2⟩ := Law.sites_shape_ok Zp s hs
  have hv := Cb.Fo.ok_v h2
  unfold lookupEventsAtSite
  rw [h1, eventsOfAShapeInClosedForm, eventsOutOfAShapeInClosedForm _ (by omega)]
  unfold eventsAt eventsOutAt lookupEventsOfSizes
  omega

/-- At most 1591 at any site. No hypothesis but the site. -/
theorem lookupEventsAtSiteAtMost (Zp : ProofFile.Pub) (s : Site) (hs : s ∈ lookSites Zp) :
    lookupEventsAtSite s ≤ 1591 := by
  rw [lookupEventsAtSiteInClosedForm Zp s hs]
  obtain ⟨_, h2⟩ := Law.sites_shape_ok Zp s hs
  unfold FoNums.ok at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hd⟩ := h2
  have hp : OnBytes.pW.toNat < 2 ^ 64 := OnBytes.pW.toNat_lt
  have hlt : s.shape.d + 32 < 64 := (Nat.pow_lt_pow_iff_right (by omega)).1 (hd.trans hp)
  have a1 : s.shape.v * (s.shape.v - 1) ≤ 31 * 30 := Nat.mul_le_mul (by omega) (by omega)
  have a2 : s.shape.d * (s.shape.d - 1) ≤ 31 * 30 := Nat.mul_le_mul (by omega) (by omega)
  unfold lookupEventsOfSizes
  omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A sum of n numbers, each at most c, is at most n c. -/
theorem sumOfBoundedNumbers {α : Type} (g : α → ℕ) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, g a ≤ c) → (l.map g).sum ≤ l.length * c
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := sumOfBoundedNumbers g c l fun b hb => h b (List.mem_cons_of_mem _ hb)
    omega

/-- Under the head: at most 79550 at the fifty sites together. -/
theorem lookupEventsInAllAtMost (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ((lookSites Zp).map lookupEventsAtSite).sum ≤ 79550 := by
  have a := sumOfBoundedNumbers lookupEventsAtSite 1591 (lookSites Zp) (lookupEventsAtSiteAtMost Zp)
  rw [sites_fifty h] at a
  exact a

/-- A number of events times the bound at one value, as a quotient of two naturals. -/
theorem shareAsAQuotient (n a b q k : ℕ) (hb : b ≠ 0) :
    (n : ℝ≥0∞) * (((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ k / (q : ℝ≥0∞)) =
      ((n * a ^ k : ℕ) : ℝ≥0∞) / ((b ^ k * q : ℕ) : ℝ≥0∞) := by
  have h0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have ht : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  generalize (a : ℝ≥0∞) = A
  generalize (b : ℝ≥0∞) = B at h0 ht
  generalize (q : ℝ≥0∞) = Q
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (pow_ne_zero _ h0)) (Or.inl (ENNReal.pow_ne_top ht)), mul_pow, ENNReal.inv_pow]
  ring

/-- Arithmetic: 79550 (1 + 2 ^ -128) ^ 108 / p ^ 3 ≤ 1 / 2 ^ 175. -/
theorem allLookupMarksTogetherAreSmall : (79550 : ℝ≥0∞) * shareOfOneValue 36 ≤ 1 / 2 ^ 175 := by
  unfold shareOfOneValue
  rw [P1K8.kap_val, OnBytes.Slice.two_p, Code.pGold_eq]
  have e := shareAsAQuotient 79550 (2 ^ 128 + 1) (2 ^ 128) (18446744069414584321 ^ 3) (3 * 36) (by positivity)
  rw [Nat.cast_ofNat] at e
  rw [e]
  have e1 : (1 : ℝ≥0∞) / 2 ^ 175 = ((1 : ℕ) : ℝ≥0∞) / ((2 ^ 175 : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [e1]
  exact P1K8.frac_le _ _ _ _ (by norm_num) (by positivity) (by positivity)

/-- The numbers of the marks of a list of sites add up to the sites' events times the bound at one value. -/
theorem marksOfSitesSumTo (oneValue : ℝ≥0∞) : ∀ sites : List Site,
    ((sites.flatMap fun t => [markK3 t.at_.place t.at_.face, markOut t.at_.place t.at_.face]).map
      fun mk => (mk.share.num : ℝ≥0∞) * oneValue).sum =
      (((sites.map lookupEventsAtSite).sum : ℕ) : ℝ≥0∞) * oneValue
  | [] => by
    show (0 : ℝ≥0∞) = ((0 : ℕ) : ℝ≥0∞) * oneValue
    rw [Nat.cast_zero, zero_mul]
  | t :: rest => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, marksOfSitesSumTo oneValue rest]
    show ((events t.at_.face : ℕ) : ℝ≥0∞) * oneValue + (((eventsOut t.at_.face : ℕ) : ℝ≥0∞) * oneValue + 0) +
      (((rest.map lookupEventsAtSite).sum : ℕ) : ℝ≥0∞) * oneValue =
      (((events t.at_.face + eventsOut t.at_.face) + (rest.map lookupEventsAtSite).sum : ℕ) : ℝ≥0∞) * oneValue
    rw [add_zero, Nat.cast_add, Nat.cast_add, add_mul, add_mul]

/-- **UNDER THE HEAD: THE NUMBERS AT WHICH THE LOOKUPS' HUNDRED MARKS PAY ADD UP TO AT MOST 1 / 2 ^ 175.** -/
theorem lookupMarksWholeShare (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    ((k3Marks Zp G₀).map fun mk => (mk.share.num : ℝ≥0∞) * shareOfOneValue 36).sum ≤ 1 / 2 ^ 175 := by
  have e : ((k3Marks Zp G₀).map fun mk => (mk.share.num : ℝ≥0∞) * shareOfOneValue 36).sum =
      ((((lookSites Zp).map lookupEventsAtSite).sum : ℕ) : ℝ≥0∞) * shareOfOneValue 36 :=
    marksOfSitesSumTo (shareOfOneValue 36) (lookSites Zp)
  rw [e]
  refine le_trans (mul_le_mul' ?_ le_rfl) allLookupMarksTogetherAreSmall
  exact_mod_cast lookupEventsInAllAtMost h

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.eventsOfAShapeInClosedForm
#print axioms ProofFile.Honest.K3.Term.eventsOutOfAShapeInClosedForm
#print axioms ProofFile.Honest.K3.Term.lookupEventsAtSiteInClosedForm
#print axioms ProofFile.Honest.K3.Term.lookupEventsAtSiteAtMost
#print axioms ProofFile.Honest.K3.Term.lookupEventsInAllAtMost
#print axioms ProofFile.Honest.K3.Term.allLookupMarksTogetherAreSmall
#print axioms ProofFile.Honest.K3.Term.lookupMarksWholeShare
