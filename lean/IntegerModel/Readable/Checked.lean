-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Model
import IntegerModel.Readable.Facts
import IntegerModel.Readable.Reads

/-!
# A checked version of the model

`IntegerModel/Model.lean` reads arrays with `v.entry k`, which gives a default value outside the
array. This file writes the model a second time, with Lean's checked read `v[k]?`, which gives
`none` outside. The names are those of `IntegerModel/Model.lean` with a question mark, but for
`wellFormedChecked` and the helpers `map?`, `all?` and `rotaryRow?`. In this checked version one
failed read makes the whole result `none`. There is one exception: `wellFormedChecked` turns a
failed read into the answer `false`, "the arguments do not fit together".

What is proved. Stage by stage, the checked version gives `some` of exactly what
`IntegerModel/Model.lean`'s definition gives, under the hypotheses of each statement (sizes, bounds
on indices, parts of `wellFormed`). `trace?_eq_some` says it of the whole trace, for arguments with
`wellFormed` and a prompt with `isPrompt`. `model?_eq_some` says it of `model`, for all arguments:
`model? .. = some (model ..)`. `wellFormedChecked_eq` says that `wellFormedChecked` is `wellFormed`,
for all arguments.

Limit: what is not proved. That the checked version falls back on no default value, except as said
above, is a property of the text of its 26 definitions and of those of `IntegerModel/Model.lean`
that they use as they are. No theorem states it, and nothing in this repository tests it. Only
together with that property do the theorems show that no result of `model` or `wellFormed`, and, for
arguments with `wellFormed` and a prompt with `isPrompt`, no value of the trace, rests on a read
outside an array, but for the exception above. This file does not say that the checked version has
the same reads as `IntegerModel/Model.lean`, and it need not.
-/

namespace IntegerTransformer

/-! ## 1. The helpers, checked -/

/-- Inside the array the checked read gives `some` of what `entry` gives. -/
theorem read?_inside {α : Type} [Inhabited α] (v : Array α) (k : Nat) (h : k < v.size) :
    v[k]? = some (v.entry k) := by
  simp [Array.entry, h]

/-- The array `f 0, .., f (n - 1)`, if each of them is `some`. -/
def tabulate? {α : Type} : Nat → (Nat → Option α) → Option (Array α)
  | 0, _ => some #[]
  | n + 1, f => do
    let before ← tabulate? n f
    let last ← f n
    pure (before.push last)

/-- The sum `f 0 + .. + f (n - 1)`, if each term is `some`. -/
def sumOver? : Nat → (Nat → Option Int) → Option Int
  | 0, _ => some 0
  | n + 1, f => do
    let before ← sumOver? n f
    let last ← f n
    pure (before + last)

/-- `v.map f`, if each result is `some`. -/
def map? {α β : Type} (v : Array α) (f : α → Option β) : Option (Array β) :=
  tabulate? v.size fun i => do f (← v[i]?)

/-- One more entry: `tabulate (n + 1) g` is `tabulate n g` with `g n` added. -/
theorem tabulate_succ {α : Type} (n : Nat) (g : Nat → α) :
    tabulate (n + 1) g = (tabulate n g).push (g n) := by
  apply Array.ext
  · simp [tabulate]
  · intro i h1 h2
    simp only [tabulate, Array.getElem_ofFn, Array.getElem_push, Array.size_ofFn]
    split
    · rfl
    · have : i = n := by simp [tabulate] at h1; omega
      rw [this]

theorem tabulate?_some {α : Type} (n : Nat) (f : Nat → Option α)
    (g : Nat → α) (h : ∀ i, i < n → f i = some (g i)) :
    tabulate? n f = some (tabulate n g) := by
  induction n with
  | zero => simp [tabulate?, tabulate]
  | succ n ih =>
    simp only [tabulate?, ih (fun i hi => h i (by omega)), h n (by omega), tabulate_succ]
    rfl

theorem sumOver?_some (n : Nat) (f : Nat → Option Int)
    (g : Nat → Int) (h : ∀ i, i < n → f i = some (g i)) :
    sumOver? n f = some (sumOver n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumOver?, ih (fun i hi => h i (by omega)), h n (by omega), sumOver]
    rfl

/-- `v.map g` is the array of `g` of the entries. -/
theorem map_eq_tabulate {α β : Type} [Inhabited α] (v : Array α) (g : α → β) :
    v.map g = tabulate v.size fun i => g (v.entry i) := by
  apply Array.ext
  · simp [tabulate]
  · intro i h1 h2
    have inside : i < v.size := by simpa using h1
    simp [tabulate, entry_inside v i inside]

theorem map?_some {α β : Type} [Inhabited α] (v : Array α) (f : α → Option β) (g : α → β)
    (h : ∀ i, i < v.size → f (v.entry i) = some (g (v.entry i))) : map? v f = some (v.map g) := by
  rw [map_eq_tabulate]
  apply tabulate?_some
  intro i hi
  rw [read?_inside v i hi]
  exact h i hi

/-- The largest of `f 0, .., f i`, if each of them is `some`. -/
def maxUpTo? (f : Nat → Option Int) : Nat → Option Int
  | 0 => f 0
  | i + 1 => do
    let before ← maxUpTo? f i
    let last ← f (i + 1)
    pure (max before last)

theorem maxUpTo?_some (f : Nat → Option Int) (g : Nat → Int)
    (i : Nat) (h : ∀ j, j ≤ i → f j = some (g j)) :
    maxUpTo? f i = some (maxUpTo g i) := by
  induction i with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ i ih =>
    simp only [maxUpTo?, ih (fun j hj => h j (by omega)), h (i + 1) (Nat.le_refl _), maxUpTo]
    rfl

/-- The argmax below `n`, if each value that it compares is `some`. -/
def firstArgmax? (f : Nat → Option Int) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let best ← firstArgmax? f n
    let atBest ← f best
    let last ← f n
    pure (if atBest < last then n else best)

theorem firstArgmax?_some (f : Nat → Option Int) (g : Nat → Int)
    (n : Nat) (h : ∀ v, v < n → f v = some (g v)) :
    firstArgmax? f n = some (firstArgmax g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have best : firstArgmax g n < n + 1 := by
      by_cases zero : n = 0
      · subst zero; exact Nat.zero_lt_one
      · have := (firstArgmax_spec g n (by omega)).1; omega
    simp only [firstArgmax?, ih (fun v hv => h v (by omega)), h n (by omega), firstArgmax]
    show (do let atBest ← f (firstArgmax g n); pure (if atBest < g n then n else firstArgmax g n)) = _
    rw [h _ best]
    rfl

/-! ## 2. The stages, checked -/

def addVec? (x y : IntegerVector) : Option IntegerVector :=
  tabulate? x.size fun k => do pure ((← x[k]?) + (← y[k]?))

theorem addVec?_some (x y : IntegerVector) (h : y.size = x.size) : addVec? x y = some (addVectors x y) := by
  apply tabulate?_some
  intro k hk
  rw [read?_inside x k hk, read?_inside y k (by omega)]
  rfl

def product? (x : IntegerVector) (W : Matrix) (outputs : Nat) : Option IntegerVector :=
  tabulate? outputs fun j => sumOver? x.size fun k => do pure ((← x[k]?) * (← (← W[k]?)[j]?))

theorem product?_some (x : IntegerVector) (W : Matrix) (outputs : Nat) (rows : W.size = x.size)
    (columns : ∀ k, k < x.size → (W.entry k).size = outputs) :
    product? x W outputs = some (product x W outputs) := by
  apply tabulate?_some
  intro j hj
  apply sumOver?_some
  intro k hk
  rw [read?_inside x k hk, read?_inside W k (by omega)]
  show (do pure (x.entry k * (← (W.entry k)[j]?))) = _
  rw [read?_inside (W.entry k) j (by rw [columns k hk]; exact hj)]
  rfl

def rmsNorm? (bits shift : Nat) (eps : Int) (x : IntegerVector) : Option Norm := do
  let sumSquares ← sumOver? x.size fun k => do pure ((← x[k]?) * (← x[k]?))
  let root : Int := integerSquareRoot (sumSquares + eps).toNat
  let reciprocal := (2 ^ bits + root / 2) / root
  let quotient := x.map fun xk => roundShift (xk * reciprocal) shift
  let out := quotient.map fun wk => clamp wk activationBound
  pure { sumSquares, root, reciprocal, quotient, out }

theorem rmsNorm?_some (bits shift : Nat) (eps : Int) (x : IntegerVector) :
    rmsNorm? bits shift eps x = some (rmsNorm bits shift eps x) := by
  have sum : (sumOver? x.size fun k => do pure ((← x[k]?) * (← x[k]?))) =
      some (sumOver x.size fun k => x.entry k * x.entry k) := by
    apply sumOver?_some
    intro k hk
    rw [read?_inside x k hk]
    rfl
  simp only [rmsNorm?, sum]
  rfl

def rotate? (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector) : Option IntegerVector :=
  tabulate? A.size fun j =>
    let i := (j % headDim) / 2
    if j % 2 = 0 then do pure ((← cosine[i]?) * (← A[j]?) - (← sine[i]?) * (← A[j + 1]?))
    else do pure ((← sine[i]?) * (← A[j - 1]?) + (← cosine[i]?) * (← A[j]?))

theorem rotate?_some (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector)
    (cosines : cosine.size = headDim / 2) (sines : sine.size = headDim / 2) (positive : 0 < headDim)
    (even : headDim % 2 = 0) (heads : A.size % headDim = 0) :
    rotate? cosine sine headDim A = some (rotate cosine sine headDim A) := by
  apply tabulate?_some
  intro j hj
  have index := rotate_index A.size headDim j positive even heads hj
  simp only []
  split
  · next first =>
    rw [read?_inside cosine _ (by rw [cosines]; exact index.1),
      read?_inside sine _ (by rw [sines]; exact index.1), read?_inside A j hj,
      read?_inside A (j + 1) (index.2.1 first)]
    rfl
  · next second =>
    have := index.2.2 second
    rw [read?_inside cosine _ (by rw [cosines]; exact index.1),
      read?_inside sine _ (by rw [sines]; exact index.1),
      read?_inside A j hj, read?_inside A (j - 1) (by omega)]
    rfl

/-- A step that is `some` passes its value on. -/
theorem some_bind {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

/-- Row `t` of a rotary table, or in a layer without rotary step the row that replaces it. -/
def rotaryRow? (rotary : Bool) (table : Matrix) (t : Nat) (otherwise : IntegerVector) : Option IntegerVector :=
  if rotary then table[t]? else some otherwise

theorem rotaryRow?_some (rotary : Bool) (table : Matrix) (t : Nat)
    (otherwise : IntegerVector) (h : t < table.size) :
    rotaryRow? rotary table t otherwise = some (if rotary then table.entry t else otherwise) := by
  unfold rotaryRow?
  split
  · exact read?_inside _ _ h
  · rfl

def projections? (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) :
    Option Projections := do
  let cosine ← rotaryRow? p.rotary tables.cosine t
    (tabulate (s.headDim / 2) fun _ => 2 ^ s.rotaryScale)
  let sine ← rotaryRow? p.rotary tables.sine t (tabulate (s.headDim / 2) fun _ => 0)
  let queryProducts ← product? a w.query s.queryWidth
  let keyProducts ← product? a w.key s.keyValueWidth
  let rotatedQuery ← rotate? cosine sine s.headDim queryProducts
  let rotatedKey ← rotate? cosine sine s.headDim keyProducts
  let valueProducts ← product? a w.value s.keyValueWidth
  let wideQuery := rotatedQuery.map fun e => roundShift e p.queryShift
  let wideKey := rotatedKey.map fun e => roundShift e p.keyShift
  let query := wideQuery.map fun e => clamp e activationBound
  let key := wideKey.map fun e => clamp e activationBound
  let wideValue := valueProducts.map fun e => roundShift e p.valueShift
  let value := wideValue.map fun e => clamp e activationBound
  pure { queryProducts, keyProducts, rotatedQuery, rotatedKey, wideQuery, wideKey,
         query, key, wideValue, value }

theorem projections?_some (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (t : Nat) (a : IntegerVector) (row : a.size = s.width)
    (queries : w.query.size = s.width ∧ ∀ k, k < s.width → (w.query.entry k).size = s.queryWidth)
    (keys : w.key.size = s.width ∧ ∀ k, k < s.width → (w.key.entry k).size = s.keyValueWidth)
    (values : w.value.size = s.width ∧ ∀ k, k < s.width → (w.value.entry k).size = s.keyValueWidth)
    (cosines : t < tables.cosine.size ∧ (tables.cosine.entry t).size = s.headDim / 2)
    (sines : t < tables.sine.size ∧ (tables.sine.entry t).size = s.headDim / 2)
    (positive : 0 < s.headDim) (even : s.headDim % 2 = 0) :
    projections? s p tables w t a = some (projections s p tables w t a) := by
  have cosine := rotaryRow?_some
    p.rotary tables.cosine t (tabulate (s.headDim / 2) fun _ => 2 ^ s.rotaryScale) cosines.1
  have sine := rotaryRow?_some p.rotary tables.sine t (tabulate (s.headDim / 2) fun _ => 0) sines.1
  have cosineSize : (if p.rotary then tables.cosine.entry t
      else tabulate (s.headDim / 2) fun _ => (2 : Int) ^ s.rotaryScale).size = s.headDim / 2 := by
    split
    · exact cosines.2
    · exact size_tabulate _ _
  have sineSize : (if p.rotary then tables.sine.entry t
      else tabulate (s.headDim / 2) fun _ => (0 : Int)).size = s.headDim / 2 := by
    split
    · exact sines.2
    · exact size_tabulate _ _
  have q :=
    product?_some a w.query s.queryWidth (by rw [queries.1, row]) (by rw [row]; exact queries.2)
  have k := product?_some a w.key s.keyValueWidth (by rw [keys.1, row]) (by rw [row]; exact keys.2)
  have v :=
    product?_some a w.value s.keyValueWidth (by rw [values.1, row]) (by rw [row]; exact values.2)
  have rq := rotate?_some _ _ s.headDim (product a w.query s.queryWidth) cosineSize sineSize
    positive even (by rw [size_product]; exact Nat.mul_mod_left _ _)
  have rk := rotate?_some _ _ s.headDim (product a w.key s.keyValueWidth) cosineSize sineSize
    positive even (by rw [size_product]; exact Nat.mul_mod_left _ _)
  simp only [projections?, cosine, sine, q, k, v, rq, rk, some_bind]
  rfl

def attendHead? (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) :
    Option Head := do
  let dh := s.headDim
  let g := h / (s.queryHeads / s.keyValueHeads)
  let scores ← tabulate? (i + 1) fun j =>
    sumOver? dh fun c => do pure ((← (← projected[i]?).query[h * dh + c]?) * (← (← projected[j]?).key[g * dh + c]?))
  let top ← maxUpTo? (fun j => scores[j]?) i
  let distances := scores.map fun sj => (top - sj) / 2 ^ p.softmaxShift
  let exponentials ← map? distances fun (u : Int) =>
    if u < tables.exponential.size then tables.exponential[u.toNat]? else some 0
  let total ← sumOver? (i + 1) fun j => exponentials[j]?
  let mix ← tabulate? dh fun c =>
    sumOver? (i + 1) fun j => do pure ((← exponentials[j]?) * (← (← projected[j]?).value[g * dh + c]?))
  let out := mix.map fun acc => (2 * acc + total) / (2 * total)
  pure { scores, top, distances, exponentials, total, mix, out }

theorem attendHead?_some (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) (position : i < projected.size)
    (queries : (projected.entry i).query.size = s.queryWidth)
    (keys : ∀ j, j ≤ i → (projected.entry j).key.size = s.keyValueWidth)
    (values : ∀ j, j ≤ i → (projected.entry j).value.size = s.keyValueWidth)
    (head : h < s.queryHeads) (divides : s.queryHeads % s.keyValueHeads = 0) :
    attendHead? s p tables projected i h = some (attendHead s p tables projected i h) := by
  have group := group_index _ _ h divides head
  have sizes := (size_attendHead s p tables projected i h).1
  have scores : (tabulate? (i + 1) fun j => sumOver? s.headDim fun c => do
      pure ((← (← projected[i]?).query[h * s.headDim + c]?) *
        (← (← projected[j]?).key[h / (s.queryHeads / s.keyValueHeads) * s.headDim + c]?))) =
      some (attendHead s p tables projected i h).scores := by
    have made : (attendHead s p tables projected i h).scores = tabulate (i + 1) fun j => sumOver s.headDim fun c =>
        (projected.entry i).query.entry (h * s.headDim + c) *
            (projected.entry j).key.entry (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c) :=
          rfl
    rw [made]
    apply tabulate?_some
    intro j hj
    apply sumOver?_some
    intro c hc
    simp only [read?_inside projected i position, read?_inside projected j (by omega), some_bind,
      read?_inside (projected.entry i).query _ (by rw [queries]; exact head_index _ _ _ _ head hc),
      read?_inside (projected.entry j).key _
        (by rw [keys j (by omega)]; exact head_index _ _ _ _ group hc)]
    rfl
  have top : maxUpTo? (fun j => (attendHead s p tables projected i h).scores[j]?) i =
      some (attendHead s p tables projected i h).top :=
    maxUpTo?_some _ (fun j => (attendHead s p tables projected i h).scores.entry j) i
      (fun j hj => read?_inside _ _ (by rw [sizes.1]; omega))
  have exponentials : (map? (attendHead s p tables projected i h).distances fun (u : Int) =>
      if u < tables.exponential.size then tables.exponential[u.toNat]? else some 0) =
      some (attendHead s p tables projected i h).exponentials := by
    apply map?_some _ _
      (fun (u : Int) => if u < tables.exponential.size then tables.exponential.entry u.toNat else 0)
    intro j hj
    have nonneg : 0 ≤ (attendHead s p tables projected i h).distances.entry j := by
      have made : (attendHead s p tables projected i h).distances =
          (attendHead s p tables projected i h).scores.map fun sj =>
            ((attendHead s p tables projected i h).top - sj) / 2 ^ p.softmaxShift := rfl
      rw [made, map_read _ _ _ (by rw [sizes.1]; rw [sizes.2.1] at hj; exact hj)]
      exact distance_nonneg (fun j => (attendHead s p tables projected i h).scores.entry j) i j _
        (by rw [sizes.2.1] at hj; omega)
    split
    · next below => exact read?_inside _ _ (by omega)
    · rfl
  have total : (sumOver? (i + 1) fun j => (attendHead s p tables projected i h).exponentials[j]?) =
      some (attendHead s p tables projected i h).total :=
    sumOver?_some _ _ (fun j => (attendHead s p tables projected i h).exponentials.entry j)
      (fun j hj => read?_inside _ _ (by rw [sizes.2.2]; exact hj))
  have mix : (tabulate? s.headDim fun c => sumOver? (i + 1) fun j => do
      pure ((← (attendHead s p tables projected i h).exponentials[j]?) *
        (← (← projected[j]?).value[h / (s.queryHeads / s.keyValueHeads) * s.headDim + c]?))) =
      some (attendHead s p tables projected i h).mix := by
    have made : (attendHead s p tables projected i h).mix = tabulate s.headDim fun c => sumOver (i + 1) fun j =>
        (attendHead s p tables projected i h).exponentials.entry j *
            (projected.entry j).value.entry
              (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c) := rfl
    rw [made]
    apply tabulate?_some
    intro c hc
    apply sumOver?_some
    intro j hj
    simp only [read?_inside (attendHead s p tables projected i h).exponentials
          j (by rw [sizes.2.2]; exact hj),
      read?_inside projected j (by omega), some_bind,
      read?_inside (projected.entry j).value _
        (by rw [values j (by omega)]; exact head_index _ _ _ _ group hc)]
    rfl
  have distances : (attendHead s p tables projected i h).distances =
      (attendHead s p tables projected i h).scores.map fun sj =>
        ((attendHead s p tables projected i h).top - sj) / 2 ^ p.softmaxShift := rfl
  simp only [attendHead?, scores, some_bind, top, ← distances, exponentials, total, mix]
  rfl

def attention? (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) :
    Option Attention := do
  let norm ← map? x fun row => rmsNorm? p.attentionBits p.attentionShift p.attentionEps row
  let projected ← tabulate? x.size fun t => do projections? s p tables w t (← norm[t]?).out
  let heads ← tabulate? x.size fun i =>
    tabulate? s.queryHeads fun h => attendHead? s p tables projected i h
  let mixed ← tabulate? x.size fun i => tabulate? s.queryWidth fun j => do
    (← (← heads[i]?)[j / s.headDim]?).out[j % s.headDim]?
  let addition ← map? mixed fun o => do
    pure ((← product? o w.output s.width).map fun e => roundShift e p.outputShift)
  let out ← tabulate? x.size fun t => do addVec? (← x[t]?) (← addition[t]?)
  pure { norm, projected, heads, mixed, addition, out }

theorem attention?_some (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : Matrix) (formed : layerWellFormed s p w mixture = true)
    (divides : s.queryHeads % s.keyValueHeads = 0) (positive : 0 < s.headDim)
    (even : s.headDim % 2 = 0) (cosines : hasSize s.positions (s.headDim / 2) tables.cosine = true)
    (sines : hasSize s.positions (s.headDim / 2) tables.sine = true) (few : x.size ≤ s.positions)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width) :
    attention? s p tables w x = some (attention s p tables w x) := by
  have reads := attention_reads s p tables w mixture x formed divides cosines sines few rows
  have sizes := size_attention s p tables w x
  have atRow := size_attention_rows s p tables w x
  have projectedAt : ∀ j, j < x.size → (attention s p tables w x).projected.entry j =
      projections s p tables w j ((attention s p tables w x).norm.entry j).out := by
    intro j hj
    simp only [attention, tabulate_read, hj]
  have norm : (map? x fun row => rmsNorm? p.attentionBits p.attentionShift p.attentionEps row) =
      some (attention s p tables w x).norm :=
    map?_some x _ (fun row => rmsNorm p.attentionBits p.attentionShift p.attentionEps row)
      (fun i _ => rmsNorm?_some _ _ _ _)
  have projected : (tabulate? x.size fun t => do
      projections? s p tables w t (← (attention s p tables w x).norm[t]?).out) =
      some (attention s p tables w x).projected := by
    have made : (attention s p tables w x).projected = tabulate x.size fun t =>
        projections s p tables w t ((attention s p tables w x).norm.entry t).out := rfl
    rw [made]
    apply tabulate?_some
    intro t ht
    have r := reads t ht
    simp only [read?_inside (attention s p tables w x).norm t (by rw [sizes.1]; exact ht),
      some_bind]
    exact projections?_some s p tables w t _ r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1
      r.2.2.2.2.2.1 positive even
  have heads : (tabulate? x.size fun i =>
        tabulate? s.queryHeads fun h =>
          attendHead? s p tables (attention s p tables w x).projected i h) =
      some (attention s p tables w x).heads := by
    have made : (attention s p tables w x).heads = tabulate x.size fun i => tabulate s.queryHeads fun h =>
        attendHead s p tables (attention s p tables w x).projected i h := rfl
    rw [made]
    apply tabulate?_some
    intro i hi
    apply tabulate?_some
    intro h hh
    apply attendHead?_some s p tables _ i h (by rw [sizes.2.1]; exact hi) _ _ _ hh divides
    · rw [projectedAt i hi]; exact (size_projections _ _ _ _ _ _).1.2.2.2
    · intro j hj; rw [projectedAt j (by omega)]; exact (size_projections _ _ _ _ _ _).2.1.2.2.2
    · intro j hj; rw [projectedAt j (by omega)]; exact (size_projections _ _ _ _ _ _).2.2.2
  have mixed : (tabulate? x.size fun i => tabulate? s.queryWidth fun j => do
      (← (← (attention s p tables w x).heads[i]?)[j / s.headDim]?).out[j % s.headDim]?) =
      some (attention s p tables w x).mixed := by
    have made : (attention s p tables w x).mixed = tabulate x.size fun i => tabulate s.queryWidth fun j =>
        (((attention s p tables w x).heads.entry i).entry (j / s.headDim)).out.entry
            (j % s.headDim) := rfl
    rw [made]
    apply tabulate?_some
    intro i hi
    apply tabulate?_some
    intro j hj
    have r := (reads i hi).2.2.2.2.2.2.2.2.1 j hj
    simp only [read?_inside (attention s p tables w x).heads i (by rw [sizes.2.2.1]; exact hi),
      some_bind, read?_inside ((attention s p tables w x).heads.entry i) _ r.1]
    exact read?_inside _ _ r.2
  have addition : (map? (attention s p tables w x).mixed fun o => do
      pure ((← product? o w.output s.width).map fun e => roundShift e p.outputShift)) =
      some (attention s p tables w x).addition := by
    apply map?_some _ _
      (fun o => (product o w.output s.width).map fun e => roundShift e p.outputShift)
    intro i hi
    have r := (reads i (by rw [← sizes.2.2.2.1]; exact hi)).2.2.2.2.2.2.2.2.2.1
    rw [product?_some _ w.output s.width (by rw [r.1, r.2.1]) (by rw [r.1]; exact r.2.2)]
    rfl
  have out : (tabulate? x.size fun t => do addVec? (← x[t]?) (← (attention s p tables w x).addition[t]?)) =
      some (attention s p tables w x).out := by
    have made : (attention s p tables w x).out = tabulate x.size fun t =>
        addVectors (x.entry t) ((attention s p tables w x).addition.entry t) := rfl
    rw [made]
    apply tabulate?_some
    intro t ht
    simp only [read?_inside x t ht, some_bind,
      read?_inside (attention s p tables w x).addition t (by rw [sizes.2.2.2.2.1]; exact ht)]
    exact addVec?_some _ _ (reads t ht).2.2.2.2.2.2.2.2.2.2
  simp only [attention?, norm, some_bind, projected, heads, mixed, addition, out]
  rfl

/-- The table's entry at a key, if the table has the key. -/
def KeyedTable.read? (table : KeyedTable) (key : Int) : Option Int :=
  if table.lowestKey ≤ key then table.entries[(key - table.lowestKey).toNat]? else none

theorem keyed_read?_some (table : KeyedTable) (low high key : Int)
    (covers : table.covers low high = true) (h1 : low ≤ key) (h2 : key ≤ high) :
    table.read? key = some (table.read key) := by
  have inside := read_inside table low high key covers h1 h2
  simp only [KeyedTable.read?, KeyedTable.read, inside.1, if_true]
  exact read?_inside _ _ inside.2

def hiddenUnits? (tables : Tables) (w : GatedWeights) (hidden gateShift upShift : Nat) (z : IntegerVector) :
    Option HiddenUnits := do
  let gateProducts ← product? z w.gate hidden
  let upProducts ← product? z w.up hidden
  let wideGate := gateProducts.map fun e => roundShift e gateShift
  let lowByte := wideGate.map balancedLowByte
  let highPart ← tabulate? hidden fun j => do pure (((← wideGate[j]?) - (← lowByte[j]?)) / 256)
  let clampedHigh := highPart.map fun gh => clamp gh 127
  let key ← tabulate? hidden fun j => do pure (256 * (← clampedHigh[j]?) + (← lowByte[j]?))
  let activation ← map? key tables.silu.read?
  let up := upProducts.map fun e => roundShift e upShift
  pure { wideGate, lowByte, highPart, clampedHigh, key, activation, up }

theorem hiddenUnits?_some (tables : Tables) (w : GatedWeights) (hidden gateShift upShift : Nat)
    (z : IntegerVector) (sizes : w.hasSizes z.size hidden = true)
    (covers : tables.silu.covers (-32768) 32767 = true) :
    hiddenUnits? tables w hidden gateShift upShift z =
      some (hiddenUnits tables w hidden gateShift upShift z) := by
  have matrices := hasSizes_spec _ _ _ sizes
  have size := size_hiddenUnits tables w hidden gateShift upShift z
  have gate := product?_some z w.gate hidden matrices.1.1 matrices.1.2
  have up := product?_some z w.up hidden matrices.2.1.1 matrices.2.1.2
  have highPart : (tabulate? hidden fun j => do
      pure (((← (hiddenUnits tables w hidden gateShift upShift z).wideGate[j]?) -
        (← (hiddenUnits tables w hidden gateShift upShift z).lowByte[j]?)) / 256)) =
      some (hiddenUnits tables w hidden gateShift upShift z).highPart := by
    have made : (hiddenUnits tables w hidden gateShift upShift z).highPart = tabulate hidden fun j =>
        ((hiddenUnits tables w hidden gateShift upShift z).wideGate.entry j -
          (hiddenUnits tables w hidden gateShift upShift z).lowByte.entry j) / 256 := rfl
    rw [made]
    apply tabulate?_some
    intro j hj
    simp only [read?_inside (hiddenUnits tables w hidden gateShift upShift z).wideGate
          j (by rw [size.1]; exact hj),
      read?_inside (hiddenUnits tables w hidden gateShift upShift z).lowByte
        j (by rw [size.2.1]; exact hj), some_bind]
    rfl
  have key : (tabulate? hidden fun j => do
      pure (256 * (← (hiddenUnits tables w hidden gateShift upShift z).clampedHigh[j]?) +
        (← (hiddenUnits tables w hidden gateShift upShift z).lowByte[j]?))) =
      some (hiddenUnits tables w hidden gateShift upShift z).key := by
    have made : (hiddenUnits tables w hidden gateShift upShift z).key = tabulate hidden fun j =>
        256 * (hiddenUnits tables w hidden gateShift upShift z).clampedHigh.entry j +
          (hiddenUnits tables w hidden gateShift upShift z).lowByte.entry j := rfl
    rw [made]
    apply tabulate?_some
    intro j hj
    simp only [read?_inside (hiddenUnits tables w hidden gateShift upShift z).clampedHigh
          j (by rw [size.2.2.2.1]; exact hj),
      read?_inside (hiddenUnits tables w hidden gateShift upShift z).lowByte
        j (by rw [size.2.1]; exact hj), some_bind]
    rfl
  have activation : map? (hiddenUnits tables w hidden gateShift upShift z).key tables.silu.read? =
      some (hiddenUnits tables w hidden gateShift upShift z).activation := by
    apply map?_some _ _ tables.silu.read
    intro j hj
    have range :=
      gateKeyOf_range ((hiddenUnits tables w hidden gateShift upShift z).wideGate.entry j)
    rw [hiddenUnits_key tables w hidden gateShift upShift z j
        (by rw [size.2.2.2.2.1] at hj; exact hj)]
    exact keyed_read?_some _ _ _ _ covers (by omega) (by omega)
  have wideGate : (hiddenUnits tables w hidden gateShift upShift z).wideGate =
      (product z w.gate hidden).map fun e => roundShift e gateShift := rfl
  have lowByte : (hiddenUnits tables w hidden gateShift upShift z).lowByte =
      (hiddenUnits tables w hidden gateShift upShift z).wideGate.map balancedLowByte := rfl
  have clampedHigh : (hiddenUnits tables w hidden gateShift upShift z).clampedHigh =
      (hiddenUnits tables w hidden gateShift upShift z).highPart.map fun gh => clamp gh 127 := rfl
  simp only [hiddenUnits?, gate, up, some_bind, ← wideGate, ← lowByte, highPart,
    ← clampedHigh, key, activation]
  rfl

def downSum? (units : HiddenUnits) (down : Matrix) (k : Nat) : Option Int :=
  sumOver? units.up.size fun j => do
    pure ((← units.activation[j]?) * (← units.up[j]?) * (← (← down[j]?)[k]?))

theorem downSum?_some (units : HiddenUnits) (down : Matrix) (k d : Nat)
    (same : units.activation.size = units.up.size) (rows : down.size = units.up.size)
    (columns : ∀ j, j < units.up.size → (down.entry j).size = d) (hk : k < d) :
    downSum? units down k = some (downSum units down k) := by
  apply sumOver?_some
  intro j hj
  simp only [read?_inside units.activation j (by omega), read?_inside units.up j hj,
    read?_inside down j (by omega), some_bind,
    read?_inside (down.entry j) k (by rw [columns j hj]; exact hk)]
  rfl

def routedExpert? (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) :
    Option Routed := do
  let products ← product? m w.router s.experts
  let wide := products.map fun e => roundShift e p.routerShift
  let high := wide.map fun lw => lw / 8
  let low := wide.map fun lw => lw % 8
  let logits ← tabulate? s.experts fun e => do pure (8 * clamp (← high[e]?) 2047 + (← low[e]?))
  let chosen ← firstArgmax? (fun e => logits[e]?) s.experts
  let scale ← tables.sigmoid.read? (← logits[chosen]?)
  let input := m.map fun mk => roundShift (scale * mk) 16
  let units ← hiddenUnits? tables (← w.routed[chosen]?)
    s.expertHidden p.routedGateShift p.routedUpShift input
  pure { wide, high, low, logits, chosen, scale, input, units }

theorem routedExpert?_some (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (m : IntegerVector)
    (router : w.router.size = m.size ∧ ∀ k, k < m.size → (w.router.entry k).size = s.experts)
    (some_expert : 0 < s.experts) (count : w.routed.size = s.experts)
    (each : ∀ e, e < s.experts → (w.routed.entry e).hasSizes m.size s.expertHidden = true)
    (silu : tables.silu.covers (-32768) 32767 = true)
    (sigmoid : tables.sigmoid.covers (-16384) 16383 = true) :
    routedExpert? s p tables w m = some (routedExpert s p tables w m) := by
  have size := size_routedExpert s p tables w m
  have chosenInside := chosen_index s p tables w m some_expert
  have products := product?_some m w.router s.experts router.1 router.2
  have wide : (routedExpert s p tables w m).wide =
      (product m w.router s.experts).map fun e => roundShift e p.routerShift := rfl
  have high : (routedExpert s p tables w m).high =
      (routedExpert s p tables w m).wide.map fun lw => lw / 8 := rfl
  have low : (routedExpert s p tables w m).low =
      (routedExpert s p tables w m).wide.map fun lw => lw % 8 := rfl
  have logits : (tabulate? s.experts fun e => do
      pure (8 * clamp (← (routedExpert s p tables w m).high[e]?) 2047 +
        (← (routedExpert s p tables w m).low[e]?))) =
      some (routedExpert s p tables w m).logits := by
    have made : (routedExpert s p tables w m).logits = tabulate s.experts fun e =>
        8 * clamp ((routedExpert s p tables w m).high.entry e) 2047 +
            (routedExpert s p tables w m).low.entry e := rfl
    rw [made]
    apply tabulate?_some
    intro e he
    simp only [read?_inside (routedExpert s p tables w m).high e (by rw [size.2.1]; exact he),
      read?_inside (routedExpert s p tables w m).low e (by rw [size.2.2.1]; exact he), some_bind]
    rfl
  have chosen : firstArgmax? (fun e => (routedExpert s p tables w m).logits[e]?) s.experts =
      some (routedExpert s p tables w m).chosen :=
    firstArgmax?_some _ (fun e => (routedExpert s p tables w m).logits.entry e) s.experts
      (fun e he => read?_inside _ _ (by rw [size.2.2.2.1]; exact he))
  have logit := read?_inside (routedExpert s p tables w m).logits
    (routedExpert s p tables w m).chosen (by rw [size.2.2.2.1]; exact chosenInside)
  have scale : tables.sigmoid.read?
        ((routedExpert s p tables w m).logits.entry (routedExpert s p tables w m).chosen) =
      some (routedExpert s p tables w m).scale := by
    have range := routerLogitOf_range
      ((routedExpert s p tables w m).wide.entry (routedExpert s p tables w m).chosen)
    have made : (routedExpert s p tables w m).scale = tables.sigmoid.read
        ((routedExpert s p tables w m).logits.entry (routedExpert s p tables w m).chosen) := rfl
    rw [made, routedExpert_logits s p tables w m _ chosenInside]
    exact keyed_read?_some _ _ _ _ sigmoid (by omega) (by omega)
  have input : (routedExpert s p tables w m).input =
      m.map fun mk => roundShift ((routedExpert s p tables w m).scale * mk) 16 := rfl
  have expert :=
    read?_inside w.routed (routedExpert s p tables w m).chosen (by rw [count]; exact chosenInside)
  have units := hiddenUnits?_some tables (w.routed.entry (routedExpert s p tables w m).chosen)
    s.expertHidden p.routedGateShift p.routedUpShift (routedExpert s p tables w m).input
    (by rw [size.2.2.2.2]; exact each _ chosenInside) silu
  simp only [routedExpert?, products, some_bind, ← wide, ← high, ← low, logits, chosen, logit,
    scale, ← input, expert, units]
  rfl

def feedForward? (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : IntegerVector) :
    Option FeedForward := do
  let norm ← rmsNorm? p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  let m := norm.out
  if mixture then
    let sharedUnits ← hiddenUnits? tables w.shared s.expertHidden p.gateShift p.upShift m
    let route ← routedExpert? s p tables w m
    let expert ← w.routed[route.chosen]?
    let addition ← tabulate? s.width fun k => do
      pure (roundShift
        ((← downSum? sharedUnits w.shared.down k) + (← downSum? route.units expert.down k))
        p.downShift)
    let out ← addVec? x addition
    pure { norm, shared := sharedUnits, routed := route, addition, out }
  else
    let sharedUnits ← hiddenUnits? tables w.shared s.hidden p.gateShift p.upShift m
    let addition ← tabulate? s.width fun k => do
      pure (roundShift (← downSum? sharedUnits w.shared.down k) p.downShift)
    let out ← addVec? x addition
    pure { norm, shared := sharedUnits, routed := noRoute, addition, out }

theorem feedForward?_some (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : IntegerVector) (formed : layerWellFormed s p w mixture = true)
    (some_expert : mixture = true → 0 < s.experts) (row : x.size = s.width)
    (silu : tables.silu.covers (-32768) 32767 = true)
    (sigmoid : tables.sigmoid.covers (-16384) 16383 = true) :
    feedForward? s p tables w mixture x = some (feedForward s p tables w mixture x) := by
  have reads := feedForward_reads s p tables w mixture x formed some_expert row
  have norm := rmsNorm?_some p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have spec := layerWellFormed_spec s p w mixture formed
  cases mixture with
  | false =>
    have sizes := reads.2.1 rfl
    have matrices := hasSizes_spec _ _ _ sizes
    have shared := hiddenUnits?_some tables w.shared s.hidden p.gateShift p.upShift
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
      (by rw [reads.1]; exact sizes) silu
    have size := size_hiddenUnits tables w.shared s.hidden p.gateShift p.upShift
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
    have addition : (tabulate? s.width fun k => do
        pure (roundShift (← downSum? (hiddenUnits tables w.shared s.hidden p.gateShift p.upShift
          (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out) w.shared.down k) p.downShift)) =
        some (feedForward s p tables w false x).addition := by
      have made : (feedForward s p tables w false x).addition = tabulate s.width fun k =>
          roundShift (downSum
                (hiddenUnits tables w.shared s.hidden p.gateShift p.upShift
                  (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out)
                w.shared.down k) p.downShift := rfl
      rw [made]
      apply tabulate?_some
      intro k hk
      rw [downSum?_some _ _ k s.width (by rw [size.2.2.2.2.2.1, size.2.2.2.2.2.2])
          (by rw [size.2.2.2.2.2.2]; exact matrices.2.2.1)
          (by rw [size.2.2.2.2.2.2]; exact matrices.2.2.2) hk]
      rfl
    have out := addVec?_some x (feedForward s p tables w false x).addition reads.2.2.2
    simp only [feedForward?, norm, some_bind, Bool.false_eq_true, if_false, shared, addition, out]
    rfl
  | true =>
    obtain ⟨sharedSizes, router, chosenInside, expertSizes, inputSize⟩ := reads.2.2.1 rfl
    obtain ⟨_, _, count, each⟩ := spec.2.2.2.2.2.2 rfl
    have sharedMatrices := hasSizes_spec _ _ _ sharedSizes
    have expertMatrices := hasSizes_spec _ _ _ expertSizes
    have shared := hiddenUnits?_some tables w.shared s.expertHidden p.gateShift p.upShift
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
      (by rw [reads.1]; exact sharedSizes) silu
    have route := routedExpert?_some s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
      (by rw [reads.1]; exact router) (some_expert rfl) count
      (by rw [reads.1]; exact each) silu sigmoid
    have expert := read?_inside w.routed _ chosenInside
    have size := size_hiddenUnits tables w.shared s.expertHidden p.gateShift p.upShift
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
    have routedSize := size_hiddenUnits tables
      (w.routed.entry
        (routedExpert s p tables w
          (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).chosen)
      s.expertHidden p.routedGateShift p.routedUpShift
      (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input
    have addition : (tabulate? s.width fun k => do
        pure (roundShift
            ((← downSum? (hiddenUnits tables w.shared s.expertHidden p.gateShift p.upShift
            (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out) w.shared.down k) +
          (← downSum? (routedExpert s p tables w
              (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).units
            (w.routed.entry (routedExpert s p tables w
              (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).chosen).down k)) p.downShift)) =
        some (feedForward s p tables w true x).addition := by
      have made : (feedForward s p tables w true x).addition = tabulate s.width fun k =>
          roundShift (downSum
              (hiddenUnits tables w.shared s.expertHidden p.gateShift p.upShift
                (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out)
              w.shared.down k +
            downSum (routedExpert s p tables w
                (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).units
              (w.routed.entry
                (routedExpert s p tables w
                  (rmsNorm p.feedForwardBits p.feedForwardShift
                    p.feedForwardEps x).out).chosen).down k)
            p.downShift := rfl
      rw [made]
      apply tabulate?_some
      intro k hk
      rw [downSum?_some _ w.shared.down k s.width (by rw [size.2.2.2.2.2.1, size.2.2.2.2.2.2])
          (by rw [size.2.2.2.2.2.2]; exact sharedMatrices.2.2.1)
          (by rw [size.2.2.2.2.2.2]; exact sharedMatrices.2.2.2) hk]
      rw [downSum?_some (routedExpert s p tables w
          (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).units _ k s.width
        (by exact routedSize.2.2.2.2.2.1.trans routedSize.2.2.2.2.2.2.symm)
        (by exact expertMatrices.2.2.1.trans routedSize.2.2.2.2.2.2.symm)
        (fun j hj => expertMatrices.2.2.2 j (by rw [← routedSize.2.2.2.2.2.2]; exact hj)) hk]
      rfl
    have out := addVec?_some x (feedForward s p tables w true x).addition reads.2.2.2
    simp only [feedForward?, norm, some_bind, if_true, shared, route, expert, addition, out]
    rfl

def layer? (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (x : Matrix) :
    Option Layer := do
  let p ← s.perLayer[l]?
  let w ← weights.perLayer[l]?
  let attended ← attention? s p tables w x
  let fed ← map? attended.out fun row => feedForward? s p tables w (s.isMixture l) row
  pure { input := x, attention := attended, feedForward := fed, out := fed.map fun ff => ff.out }

/-- For arguments that fit together, `l < s.layers` and a stream of at most `s.positions` rows of
`s.width` entries, `layer?` gives `some` of `layer`. -/
theorem layer?_some (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (x : Matrix)
    (formed : wellFormed s tables weights = true) (hl : l < s.layers) (few : x.size ≤ s.positions)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width) :
    layer? s tables weights l x = some (layer s tables weights l x) := by
  have parts := wellFormed_spec s tables weights formed
  have thisLayer := parts.2.2.2.2.2.2 l hl
  have p := read?_inside s.perLayer l (by rw [parts.2.2.2.2.1]; exact hl)
  have w := read?_inside weights.perLayer l (by rw [parts.2.2.2.2.2.1]; exact hl)
  have attended := attention?_some s (s.perLayer.entry l) tables (weights.perLayer.entry l)
    (s.isMixture l) x thisLayer parts.1.2.2.1 parts.1.2.2.2.1 parts.1.2.2.2.2.1 parts.2.2.1.1
    parts.2.2.1.2.1 few rows
  have some_expert : s.isMixture l = true → 0 < s.experts := by
    intro mix
    simp only [Settings.isMixture, Bool.and_eq_true, decide_eq_true_eq] at mix
    exact mix.1
  have fed : (map?
    (attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) x).out fun row =>
      feedForward? s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l) row) =
      some (layer s tables weights l x).feedForward := by
    apply map?_some _ _ (fun row =>
      feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l) row)
    intro t ht
    have inside : t < x.size := by rw [(size_attention _ _ _ _ _).2.2.2.2.2] at ht; exact ht
    exact feedForward?_some _ _ _ _ _ _ thisLayer some_expert
      (by rw [(size_attention_rows _ _ _ _ _ t inside).2.2.2]; exact rows t inside)
      parts.2.2.1.2.2.2.2.2.1 parts.2.2.1.2.2.2.2.2.2
  simp only [layer?, p, w, some_bind, attended, fed]
  rfl

def firstLayers? (s : Settings) (tables : Tables) (weights : Weights) (embedded : Matrix) :
    Nat → Option (Array Layer)
  | 0 => some #[]
  | l + 1 => do
    let below ← firstLayers? s tables weights embedded l
    let next ← layer? s tables weights l (streamAbove embedded below)
    pure (below.push next)

theorem firstLayers?_some (s : Settings) (tables : Tables) (weights : Weights) (x0 : Matrix)
    (n : Nat) (formed : wellFormed s tables weights = true) (hn : n ≤ s.layers)
    (few : x0.size ≤ s.positions) (rows : ∀ t, t < x0.size → (x0.entry t).size = s.width) :
    firstLayers? s tables weights x0 n = some (firstLayers s tables weights x0 n) := by
  induction n with
  | zero => rfl
  | succ l ih =>
    have shape := stream_shape s tables weights x0 s.width l rows
    have next := layer?_some s tables weights l (streamAbove x0 (firstLayers s tables weights x0 l))
      formed (by omega) (by rw [shape.1]; exact few) (by rw [shape.1]; exact shape.2)
    simp only [firstLayers?, ih (by omega), some_bind, next]
    rfl

def trace? (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat) :
    Option Trace := do
  let embedded ← map? prompt fun token => weights.embedding[token]?
  let layers ← firstLayers? s tables weights embedded s.layers
  let last := streamAbove embedded layers
  let finalNorm ← map? last fun row => rmsNorm? s.finalBits s.finalShift s.finalEps row
  let logits ← map? finalNorm fun norm => product? norm.out weights.head s.vocabulary
  let choices ← map? logits fun lam => firstArgmax? (fun v => lam[v]?) s.vocabulary
  pure { embedded, layer := layers, last, finalNorm, logits, choices }

/-- **The checked trace is the trace.** For arguments that fit together and a prompt, `trace?` gives
`some` of exactly the trace of `IntegerModel/Model.lean`. The module docstring says what follows for
reads outside an array. -/
theorem trace?_eq_some (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat)
    (formed : wellFormed s tables weights = true) (prompt_ok : isPrompt s prompt = true) :
    trace? s tables weights prompt = some (trace s tables weights prompt) := by
  have parts := wellFormed_spec s tables weights formed
  have tokens := isPrompt_spec s prompt prompt_ok
  have shape := trace_shape s tables weights prompt formed prompt_ok
  have more := head_and_condition_reads s tables weights prompt formed prompt_ok
  have start := embedded_shape s tables weights prompt formed prompt_ok
  have embedded : (map? prompt fun token => weights.embedding[token]?) =
      some (trace s tables weights prompt).embedded := by
    apply map?_some _ _ (fun token => weights.embedding.entry token)
    intro t ht
    exact read?_inside _ _ (by rw [(hasSize_spec _ _ _ parts.2.2.2.1.1).1]; exact tokens.2.2 t ht)
  have layers : firstLayers? s tables weights (trace s tables weights prompt).embedded s.layers =
      some (trace s tables weights prompt).layer :=
    firstLayers?_some s tables weights _ s.layers formed (Nat.le_refl _)
      (by rw [shape.1]; exact tokens.2.1) (by rw [shape.1]; exact start.2)
  have last : (trace s tables weights prompt).last =
      streamAbove (trace s tables weights prompt).embedded (trace s tables weights prompt).layer :=
    rfl
  have finalNorm : (map? (trace s tables weights prompt).last fun row =>
        rmsNorm? s.finalBits s.finalShift s.finalEps row) =
      some (trace s tables weights prompt).finalNorm :=
    map?_some _ _ (fun row => rmsNorm s.finalBits s.finalShift s.finalEps row)
      (fun _ _ => rmsNorm?_some _ _ _ _)
  have logits : (map? (trace s tables weights prompt).finalNorm fun norm =>
        product? norm.out weights.head s.vocabulary) =
      some (trace s tables weights prompt).logits := by
    apply map?_some _ _ (fun (norm : Norm) => product norm.out weights.head s.vocabulary)
    intro t ht
    have size := more.1 t (by rw [← shape.2.2.2.2.1]; exact ht)
    exact product?_some _ _ _ (by rw [size]; exact more.2.1.1) (by rw [size]; exact more.2.1.2)
  have choices : (map? (trace s tables weights prompt).logits fun lam =>
        firstArgmax? (fun v => lam[v]?) s.vocabulary) =
      some (trace s tables weights prompt).choices := by
    apply map?_some _ _ (fun (lam : IntegerVector) => firstArgmax (fun v => lam.entry v) s.vocabulary)
    intro t ht
    have size := shape.2.2.2.2.2.1.2 t (by rw [← shape.2.2.2.2.2.1.1]; exact ht)
    exact firstArgmax?_some _ _ _ (fun v hv => read?_inside _ _ (by rw [size]; exact hv))
  simp only [trace?, embedded, some_bind, layers, ← last, finalNorm, logits, choices]
  rfl

/-! ## 3. The range conditions and the model, checked -/

/-- Do `f 0, .., f (n - 1)` all hold, if each of them is `some`? -/
def all? : Nat → (Nat → Option Bool) → Option Bool
  | 0, _ => some true
  | n + 1, f => do
    let before ← all? n f
    let last ← f n
    pure (before && last)

theorem all?_some (n : Nat) (f : Nat → Option Bool)
    (g : Nat → Bool) (h : ∀ i, i < n → f i = some (g i)) :
    all? n f = some ((List.range n).all g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [all?, ih (fun i hi => h i (by omega)), h n (by omega), some_bind, List.range_succ,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    rfl

def attentionOk? (p : LayerSettings) (a : Attention) (t : Nat) : Option Bool := do
  let norm ← a.norm[t]?
  let projected ← a.projected[t]?
  pure (normOk p.attentionEps norm && fits16 projected.wideQuery && fits16 projected.wideKey
    && fits16 projected.wideValue)

def allConditionsHold? (s : Settings) (values : Trace) : Option Bool :=
  all? values.embedded.size fun t => do
    let inLayers ← all? s.layers fun l => do
      let p ← s.perLayer[l]?
      let layer ← values.layer[l]?
      pure ((← attentionOk? p layer.attention t) && feedForwardOk p (← layer.feedForward[t]?))
    pure (inLayers && normOk s.finalEps (← values.finalNorm[t]?))

theorem allConditionsHold?_some (s : Settings) (tables : Tables) (weights : Weights)
    (prompt : Array Nat) (formed : wellFormed s tables weights = true)
    (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold? s (trace s tables weights prompt) =
      some (allConditionsHold s (trace s tables weights prompt)) := by
  have parts := wellFormed_spec s tables weights formed
  have shape := trace_shape s tables weights prompt formed prompt_ok
  have more := head_and_condition_reads s tables weights prompt formed prompt_ok
  apply all?_some
  intro t ht
  rw [shape.1] at ht
  have inLayers : (all? s.layers fun l => do
      let p ← s.perLayer[l]?
      let layer ← (trace s tables weights prompt).layer[l]?
      pure ((← attentionOk? p layer.attention t) && feedForwardOk p (← layer.feedForward[t]?))) =
      some ((List.range s.layers).all fun l =>
        attentionOk (s.perLayer.entry l) ((trace s tables weights prompt).layer.entry l).attention t
        && feedForwardOk (s.perLayer.entry l)
            (((trace s tables weights prompt).layer.entry l).feedForward.entry t)) := by
    apply all?_some
    intro l hl
    have sizes := more.2.2.1 l hl
    simp only [read?_inside s.perLayer l (by rw [parts.2.2.2.2.1]; exact hl),
      read?_inside (trace s tables weights prompt).layer l (by rw [shape.2.1]; exact hl),
      some_bind, attentionOk?,
      read?_inside ((trace s tables weights prompt).layer.entry l).attention.norm
        t (by rw [sizes.1]; exact ht),
      read?_inside ((trace s tables weights prompt).layer.entry l).attention.projected
        t (by rw [sizes.2.1]; exact ht),
      read?_inside ((trace s tables weights prompt).layer.entry l).feedForward
        t (by rw [sizes.2.2]; exact ht)]
    rfl
  simp only [inLayers, some_bind,
    read?_inside (trace s tables weights prompt).finalNorm t (by rw [shape.2.2.2.2.1]; exact ht)]
  rfl

/-- `wellFormed` with checked reads: where a read would be outside, the answer is `false`. -/
def wellFormedChecked (s : Settings) (tables : Tables) (weights : Weights) : Bool :=
  0 < s.keyValueHeads && 0 < s.queryHeads && s.queryHeads % s.keyValueHeads == 0
  && 0 < s.headDim && s.headDim % 2 == 0 && 0 < s.vocabulary
  && (s.experts == 0 || s.hidden == 2 * s.expertHidden)
  && 1 ≤ s.finalEps && 1 ≤ s.finalShift
  && hasSize s.positions (s.headDim / 2) tables.cosine &&
    hasSize s.positions (s.headDim / 2) tables.sine
  && 0 < tables.exponential.size
  && (match tables.exponential[0]? with
      | some first => 0 < first
      | none => false)
  && (tables.exponential.all fun e => 0 ≤ e)
  && tables.silu.covers (-32768) 32767 && tables.sigmoid.covers (-16384) 16383
  && hasSize s.vocabulary s.width weights.embedding && hasSize s.width s.vocabulary weights.head
  && s.perLayer.size == s.layers && weights.perLayer.size == s.layers
  && (List.range s.layers).all fun l =>
    match s.perLayer[l]?, weights.perLayer[l]? with
    | some p, some w => layerWellFormed s p w (s.isMixture l)
    | _, _ => false

/-- `wellFormedChecked` is `wellFormed`, for all arguments. -/
theorem wellFormedChecked_eq (s : Settings) (tables : Tables) (weights : Weights) :
    wellFormedChecked s tables weights = wellFormed s tables weights := by
  rw [Bool.eq_iff_iff]
  simp only [wellFormedChecked, wellFormed, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨before, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, d1⟩, d2⟩, e1⟩, e2⟩, e3⟩
    have inside : 0 < tables.exponential.size := of_decide_eq_true c3
    rw [read?_inside _ 0 inside] at c4
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨before, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, d1⟩, d2⟩, e1⟩, e2⟩, fun l hl => ?_⟩
    have this := e3 l hl
    rw [read?_inside s.perLayer l (by rw [beq_iff_eq.mp e1]; exact hl),
      read?_inside weights.perLayer l (by rw [beq_iff_eq.mp e2]; exact hl)] at this
    exact this
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨before, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, d1⟩, d2⟩, e1⟩, e2⟩, e3⟩
    have inside : 0 < tables.exponential.size := of_decide_eq_true c3
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨before, c3⟩, ?_⟩, c5⟩, c6⟩, c7⟩, d1⟩, d2⟩, e1⟩, e2⟩, fun l hl => ?_⟩
    · rw [read?_inside _ 0 inside]
      exact c4
    · rw [read?_inside s.perLayer l (by rw [beq_iff_eq.mp e1]; exact hl),
        read?_inside weights.perLayer l (by rw [beq_iff_eq.mp e2]; exact hl)]
      exact e3 l hl

/-- The model, checked. The outer `none` would mean that a read was outside an array; the inner one
is `IntegerModel/Model.lean`'s
"not defined". `isPrompt`, `layerWellFormed` and the conditions on single records are taken as they
are: they read no array by an index. -/
def model? (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat) :
    Option (Option Nat) :=
  if wellFormedChecked s tables weights && isPrompt s prompt then do
    let values ← trace? s tables weights prompt
    let hold ← allConditionsHold? s values
    let choice ← values.choices[prompt.size - 1]?
    pure (if hold then some choice else none)
  else some none

/-- **The checked version is the model, whatever the arguments are.** It never gives the outer
`none`, and what it gives is `model`. The theorem has no hypothesis: where the arguments do not fit
together or the tokens are not a prompt, it stops before it reads further. The module docstring says
what follows for reads outside an array. -/
theorem model?_eq_some (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat) :
    model? s tables weights prompt = some (model s tables weights prompt) := by
  unfold model? model
  rw [wellFormedChecked_eq]
  by_cases fit : (wellFormed s tables weights && isPrompt s prompt) = true
  · have both : wellFormed s tables weights = true ∧ isPrompt s prompt = true := by
      simpa only [Bool.and_eq_true] using fit
    have last := (head_and_condition_reads s tables weights prompt both.1 both.2).2.2.2
    simp only [fit, if_true, trace?_eq_some s tables weights prompt both.1 both.2, some_bind,
      allConditionsHold?_some s tables weights prompt both.1 both.2, read?_inside _ _ last]
    rfl
  · simp only [fit, Bool.false_eq_true, if_false]

end IntegerTransformer
