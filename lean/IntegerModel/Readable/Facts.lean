-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Model

/-!
# Small proved facts about `IntegerModel/Model.lean`

- Worked examples of the roundings and clamps, which Lean checks when it compiles this file.
- The helpers `tabulate`, `integerSquareRoot`, `roundShift`, `balancedLowByte`, `maxUpTo` and `firstArgmax` of
  part 1 of `IntegerModel/Model.lean` are, under the hypotheses of the statements, what their
  comments, and section 1 of docs/model.md, say they are.
- The gate's key and the router's logit as functions of one number, with examples at their ends.
- How the layers are chained, and what `model .. = some y` means.
- At one norm with `eps ≥ 0`, condition 8 follows from condition 1 (docs/model.md, section 9).

Limit: nothing here says that the model equals any other program. Axioms: this file has no
`#print axioms` line; scripts/check.py, when it is run, audits in its step `build` the axioms of
every declaration of the library. What has been run: lean/CHECK-RESULTS.md.
-/

namespace IntegerTransformer

/-! ## Worked examples -/

/-! Rounding: to nearest, ties upwards, also for negative numbers. -/
example : roundShift 5 1 = 3 := by decide          -- 2.5 goes to 3
example : roundShift (-5) 1 = -2 := by decide      -- -2.5 goes to -2
example : roundShift 11 2 = 3 := by decide         -- 2.75 goes to 3
example : roundShift (-11) 2 = -3 := by decide     -- -2.75 goes to -3
example : roundShift 7 0 = 8 := by decide          -- outside rq's definition: so wellFormed asks for shifts ≥ 1

/-! Clamp and balanced low byte. -/
example : clamp 5000 activationBound = 2047 := by decide
example : clamp (-5000) activationBound = -2047 := by decide
example : balancedLowByte 127 = 127 := by decide
example : balancedLowByte 128 = -128 := by decide
example : balancedLowByte (-129) = 127 := by decide

/-! Ties go to the lowest index. -/
example : firstArgmax (fun v => (#[1, 7, 7, 3] : IntegerVector).entry v) 4 = 1 := by decide

/-! ## The helpers of part 1 -/

/-- Inside the array, `v.entry k` is Lean's own checked read `v[k]`. -/
theorem entry_inside {α : Type} [Inhabited α] (v : Array α) (k : Nat) (h : k < v.size) :
    v.entry k = v[k] := by
  simp [Array.entry, h]

/-- Outside the array, `v.entry k` is the default value. -/
theorem entry_outside {α : Type} [Inhabited α] (v : Array α) (k : Nat) (h : ¬ k < v.size) :
    v.entry k = default := by
  simp [Array.entry, h]

/-- `tabulate n f` has `n` entries. -/
theorem size_tabulate {α : Type} (n : Nat) (f : Nat → α) : (tabulate n f).size = n := by
  simp [tabulate]

/-- For `i < n`, entry `i` of `tabulate n f` is `f i`. -/
theorem tabulate_read {α : Type} [Inhabited α] (n : Nat) (f : Nat → α) (i : Nat) (h : i < n) :
    (tabulate n f).entry i = f i := by
  simp [tabulate, Array.entry, h]

/-- `integerSquareRoot a` is the largest number whose square is at most `a`. -/
theorem isqrt_spec (a : Nat) : integerSquareRoot a * integerSquareRoot a ≤ a ∧ a < (integerSquareRoot a + 1) * (integerSquareRoot a + 1) := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    unfold integerSquareRoot
    by_cases h0 : a = 0
    · simp [h0]
    · have ⟨lo, hi⟩ := ih (a / 4) (by omega)
      simp only [h0, if_false]
      generalize integerSquareRoot (a / 4) = q at lo hi ⊢
      have e1 : (2 * q) * (2 * q) = 4 * (q * q) := by grind
      have e2 : (2 * q + 1) * (2 * q + 1) = 4 * (q * q) + 4 * q + 1 := by grind
      have e3 : (2 * q + 1 + 1) * (2 * q + 1 + 1) = 4 * (q * q) + 8 * q + 4 := by grind
      have e4 : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by grind
      split <;> omega

/-- `roundShift a k` is the whole number `r` with `r 2^k ≤ a + 2^(k-1) < (r + 1) 2^k`: the floor in
the definition of rq. -/
theorem roundShift_spec (a : Int) (k : Nat) :
    roundShift a k * 2 ^ k ≤ a + 2 ^ (k - 1) ∧ a + 2 ^ (k - 1) < (roundShift a k + 1) * 2 ^ k := by
  have pos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  unfold roundShift
  generalize a + 2 ^ (k - 1) = b
  generalize (2 : Int) ^ k = m at pos
  have h1 := Int.ediv_mul_le b (Int.ne_of_gt pos)
  have h2 := Int.lt_ediv_add_one_mul_self b pos
  exact ⟨h1, h2⟩

/-- For `b ≥ 0`, `clamp a b` is in `-b .. b`, and it is `a` if `a` is in that interval. -/
theorem clamp_spec (a b : Int) (h : 0 ≤ b) :
    -b ≤ clamp a b ∧ clamp a b ≤ b ∧ (-b ≤ a → a ≤ b → clamp a b = a) := by
  unfold clamp
  omega

/-- The balanced low byte is in `-128 .. 127` and differs from `a` by a multiple of 256. -/
theorem balancedLowByte_spec (a : Int) :
    -128 ≤ balancedLowByte a ∧ balancedLowByte a ≤ 127 ∧ (a - balancedLowByte a) % 256 = 0 := by
  unfold balancedLowByte
  omega

/-- `maxUpTo f i` is at least every one of `f 0, .., f i` and equals one of them. -/
theorem maxUpTo_spec (f : Nat → Int) (i : Nat) :
    (∀ j, j ≤ i → f j ≤ maxUpTo f i) ∧ ∃ j, j ≤ i ∧ f j = maxUpTo f i := by
  induction i with
  | zero =>
    refine ⟨fun j hj => ?_, 0, Nat.le_refl 0, rfl⟩
    have : j = 0 := by omega
    subst this
    exact Int.le_refl _
  | succ i ih =>
    obtain ⟨above, j0, hj0, attained⟩ := ih
    simp only [maxUpTo]
    constructor
    · intro j hj
      by_cases last : j = i + 1
      · subst last; omega
      · have := above j (by omega); omega
    · by_cases larger : maxUpTo f i ≤ f (i + 1)
      · exact ⟨i + 1, Nat.le_refl _, by omega⟩
      · exact ⟨j0, by omega, by omega⟩

/-- For `n > 0`, `firstArgmax f n` is the argmax of docs/model.md, section 1: an index below `n` at
which `f` is largest, and the least such index. -/
theorem firstArgmax_spec (f : Nat → Int) (n : Nat) (h : 0 < n) :
    firstArgmax f n < n ∧ (∀ v, v < n → f v ≤ f (firstArgmax f n)) ∧
      (∀ v, v < firstArgmax f n → f v < f (firstArgmax f n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n = 0
    · subst first
      simp only [firstArgmax, Int.lt_irrefl, if_false]
      refine ⟨by omega, fun v hv => ?_, fun v hv => by omega⟩
      have : v = 0 := by omega
      subst this
      exact Int.le_refl _
    · obtain ⟨inside, largest, least⟩ := ih (by omega)
      simp only [firstArgmax]
      split
      · next larger =>
        refine ⟨by omega, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases last : v = n
          · subst last; exact Int.le_refl _
          · have := largest v (by omega); omega
        · have := largest v hv; omega
      · next notLarger =>
        refine ⟨by omega, fun v hv => ?_, least⟩
        by_cases last : v = n
        · subst last; omega
        · exact largest v (by omega)

/-- For `j` below the size of `v`, entry `j` of `v.map f` is `f` of entry `j` of `v`. -/
theorem map_read {α β : Type} [Inhabited α] [Inhabited β] (v : Array α) (f : α → β)
    (j : Nat) (h : j < v.size) :
    (v.map f).entry j = f (v.entry j) := by
  simp [Array.entry, h]

/-- `product x W n` has `n` entries. -/
theorem size_product (x : IntegerVector) (W : Matrix) (n : Nat) : (product x W n).size = n := by
  simp [product, size_tabulate]

/-! ## The gate's key and the router's logit, as functions of one number -/

/-- The key at which the SiLU table is read, as a function of the wide gate key `gw`. -/
def gateKeyOf (gw : Int) : Int :=
  256 * clamp ((gw - balancedLowByte gw) / 256) 127 + balancedLowByte gw

/-- The key of hidden unit `j < hidden` in `IntegerModel/Model.lean` is `gateKeyOf` of that unit's
wide gate key. -/
theorem hiddenUnits_key (tables : Tables) (w : GatedWeights) (hidden gateShift upShift : Nat)
    (z : IntegerVector) (j : Nat) (h : j < hidden) :
    (hiddenUnits tables w hidden gateShift upShift z).key.entry j =
      gateKeyOf ((hiddenUnits tables w hidden gateShift upShift z).wideGate.entry j) := by
  simp only [hiddenUnits, gateKeyOf, tabulate_read, map_read, size_tabulate,
    size_product, Array.size_map, h]

/-! The key is unchanged from -32,640 to 32,639. Beyond, the high part saturates and the low byte
stays, so the key is at least 32,384 in size and keeps its sign. (The examples test six numbers; no
theorem here says it
of every number.) -/
example : gateKeyOf 32639 = 32639 := by decide
example : gateKeyOf 32640 = 32384 := by decide
example : gateKeyOf (-32640) = -32640 := by decide
example : gateKeyOf (-32641) = -32385 := by decide
example : gateKeyOf 40000 = 32576 := by decide
example : gateKeyOf (-40000) = -32576 := by decide

/-- A router logit after its clamp, as a function of the wide logit `lw`. -/
def routerLogitOf (lw : Int) : Int :=
  8 * clamp (lw / 8) 2047 + lw % 8

/-- The logit of expert `e < s.experts` in `IntegerModel/Model.lean` is `routerLogitOf` of that
expert's wide logit. -/
theorem routedExpert_logits (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (m : IntegerVector) (e : Nat) (h : e < s.experts) :
    (routedExpert s p tables w m).logits.entry e =
      routerLogitOf ((routedExpert s p tables w m).wide.entry e) := by
  simp only [routedExpert, routerLogitOf, tabulate_read, map_read, size_product, Array.size_map, h]

/-! The router's clamp is not monotone at its ends (docs/model.md, section 7): 16,384 ranks below
16,383. -/
example : routerLogitOf 16383 = 16383 := by decide
example : routerLogitOf 16384 = 16376 := by decide
example : routerLogitOf (-16377) = -16369 := by decide

/-! ## The chain of layers, and what `model .. = some y` means -/

/-- Reading an array to which one entry was added: the new entry is at the old size, and the others
are unchanged. -/
theorem read_push {α : Type} [Inhabited α] (a : Array α) (x : α) (i : Nat) :
    (a.push x).entry i = if i = a.size then x else a.entry i := by
  simp only [Array.entry, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases last : i = a.size <;> simp [last]

/-- `firstLayers .. n` has `n` entries. -/
theorem size_firstLayers (s : Settings) (tables : Tables) (weights : Weights)
    (x0 : Matrix) (n : Nat) :
    (firstLayers s tables weights x0 n).size = n := by
  induction n with
  | zero => simp [firstLayers]
  | succ n ih => simp [firstLayers, ih]

/-- For `l < n`, entry `l` of `firstLayers .. n` is layer `l`, fed with the stream above the first
`l` layers. -/
theorem firstLayers_read (s : Settings) (tables : Tables) (weights : Weights) (x0 : Matrix)
    (n l : Nat) (h : l < n) :
    (firstLayers s tables weights x0 n).entry l =
      layer s tables weights l (streamAbove x0 (firstLayers s tables weights x0 l)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have size := size_firstLayers s tables weights x0 n
    simp only [firstLayers, read_push, size]
    by_cases last : l = n
    · subst last; simp
    · simp only [last, if_false]
      exact ih (by omega)

/-- Above no layer the stream is the embedded tokens. -/
theorem streamAbove_zero (s : Settings) (tables : Tables) (weights : Weights) (x0 : Matrix) :
    streamAbove x0 (firstLayers s tables weights x0 0) = x0 := by
  simp [streamAbove, firstLayers]

/-- Above `l + 1` layers the stream is the output of layer `l`, fed with the stream above `l`
layers. -/
theorem streamAbove_succ (s : Settings) (tables : Tables) (weights : Weights)
    (x0 : Matrix) (l : Nat) :
    streamAbove x0 (firstLayers s tables weights x0 (l + 1)) =
      (layer s tables weights l (streamAbove x0 (firstLayers s tables weights x0 l))).out := by
  simp [streamAbove, firstLayers]

/-- What `model .. = some y` means: the arguments fit together, the tokens are a prompt, all range
conditions hold, and
`y` is the greedy choice at the last position. -/
theorem model_eq_some (s : Settings) (tables : Tables) (weights : Weights)
    (prompt : Array Nat) (y : Nat) :
    model s tables weights prompt = some y ↔
    wellFormed s tables weights = true ∧
    isPrompt s prompt = true ∧
    allConditionsHold s (trace s tables weights prompt) = true ∧
    (trace s tables weights prompt).choices.entry (prompt.size - 1) = y := by
  unfold model
  by_cases formed : wellFormed s tables weights = true
  · by_cases prompt_ok : isPrompt s prompt = true
    · by_cases hold : allConditionsHold s (trace s tables weights prompt) = true
      · simp [formed, prompt_ok, hold]
      · simp [formed, prompt_ok, hold]
    · simp [formed, prompt_ok]
  · simp [formed]

/-- On weights that do not fit the settings, for example on no weights at all, the model gives
nothing. -/
theorem model_eq_none_of_not_wellFormed (s : Settings) (tables : Tables) (weights : Weights)
    (prompt : Array Nat) (h : wellFormed s tables weights = false) :
    model s tables weights prompt = none := by
  simp [model, h]

/-! ## At one norm with `eps ≥ 0`, condition 8 follows from condition 1 -/

/-- A sum of terms that are not negative is not negative. -/
theorem sumOver_nonneg (f : Nat → Int) (nonneg : ∀ k, 0 ≤ f k) (n : Nat) : 0 ≤ sumOver n f := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [sumOver]
    have := nonneg n
    omega

/-- A sum of terms that are not negative is at least each of its terms. -/
theorem term_le_sumOver (f : Nat → Int) (nonneg : ∀ k, 0 ≤ f k) (n k : Nat) (h : k < n) :
    f k ≤ sumOver n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumOver]
    by_cases last : k = n
    · subst last
      have := sumOver_nonneg f nonneg k
      omega
    · have := ih (by omega)
      have := nonneg n
      omega

/-- A square is not negative. -/
theorem square_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have : 0 ≤ -a := by omega
    have := Int.mul_nonneg this this
    rwa [Int.neg_mul_neg] at this

/-- For `b ≥ 0`, a number whose square is below `b * b` is strictly between `-b` and `b`. -/
theorem bounded_of_square_lt (a b : Int) (hb : 0 ≤ b) (h : a * a < b * b) : -b < a ∧ a < b := by
  constructor
  · apply Int.lt_of_not_ge
    intro low
    have le : b ≤ -a := by omega
    have := Int.mul_le_mul le le hb (by omega)
    rw [Int.neg_mul_neg] at this
    omega
  · apply Int.lt_of_not_ge
    intro high
    have := Int.mul_le_mul high high hb (by omega)
    omega

/-- Condition 8 at one norm (docs/model.md, section 9): if `eps ≥ 0` and condition 1 holds at a
norm (`Vx + eps < 2^78`), every entry of the row that the norm reads is below `2^39` in absolute
value. -/
theorem stream_bounded_by_condition_1 (bits shift : Nat) (eps : Int) (x : IntegerVector) (k : Nat)
    (inside : k < x.size) (eps_nonneg : 0 ≤ eps)
    (condition1 : (rmsNorm bits shift eps x).sumSquares + eps < 2 ^ 78) :
    -(2 ^ 39) < x.entry k ∧ x.entry k < 2 ^ 39 := by
  have term : x.entry k * x.entry k ≤ sumOver x.size fun k => x.entry k * x.entry k :=
    term_le_sumOver (fun k => x.entry k * x.entry k) (fun k => square_nonneg _) x.size k inside
  have sum : (rmsNorm bits shift eps x).sumSquares =
      sumOver x.size fun k => x.entry k * x.entry k := rfl
  have power : (2 : Int) ^ 78 = 2 ^ 39 * 2 ^ 39 := by decide
  apply bounded_of_square_lt _ _ (by decide)
  omega

end IntegerTransformer
