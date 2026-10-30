-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorTensor.lean: A TERM OF THE ONE EQUATION ON ONE BLOCK OF THE
LAYOUT (K9.blockTensor, Johnson/Desc/First/Batch/Lay.lean) RETURNS WHERE ONE TEST ON SIZES ACCEPTS.
The test reads of the two weights their three sizes alone, and no field element. A general law;
nothing is evaluated.

How. The text builds a tensor pair by pair. Its last test (tensorFits) asks of each dense variable
that its pair is (1, 1): a comparison of values. These pairs are laid as (1, 1) by the text itself.
So the test on sizes walks the same road with a list of marks in place of the pairs: a mark is set
where the text lays (1, 1) for a dense variable. Where the marks pass, the pairs pass.

  `WSh`, `wSh`: the three sizes of weights on an index: the two lists of factors; the written-out
    vector, if there is one.
  `Fl ps fl`: the pairs ps stand under the marks fl: as many; and (1, 1) wherever a mark is set.
  `bitVarS`, `bitVarsS`: the text's bitVar and bitVars on marks. `bitVar_sim`, `bitVars_sim`.
  `aboveB`: the test of aboveBlock. `above_returns`.
  `blockB b tR tP onI onC`: THE TEST ON SIZES.
  **`blockTensor_returns`**: blockB b tR tP (wSh onI) (wSh onC) = true: then K9.blockTensor b tR tP
    onI onC scalar returns, whatever the scalar and the field elements.

Limits. ONE WAY: the test on sizes may reject where the text returns (a pair that is (1, 1) by its
values bears no mark). No sizes are shown at which blockB accepts. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (LaidBlock)

/-! ## 1 Sizes and marks -/

/-- The three sizes of weights on an index. -/
structure WSh where
  lo : Nat
  hi : Nat
  values : Option Nat

def wSh (w : IndexWeights) : WSh := ⟨w.lo.size, w.hi.size, w.values.map (·.size)⟩

/-- The pairs stand under the marks. -/
def Fl (ps : List (E × E)) (fl : List Bool) : Prop :=
  ps.length = fl.length ∧ ∀ i : Nat, fl[i]? = some true → ps[i]? = some (oneE, oneE)

theorem Fl.nil : Fl [] [] := ⟨rfl, fun _ h => (nomatch h)⟩

theorem Fl.one {ps : List (E × E)} {fl : List Bool} (h : Fl ps fl) :
    Fl (ps ++ [(oneE, oneE)]) (fl ++ [true]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases hl : i < fl.length
  · rw [List.getElem?_append_left hl] at hi
    rw [List.getElem?_append_left (by rw [h.1]; exact hl)]
    exact h.2 i hi
  · have hl' : fl.length ≤ i := Nat.le_of_not_lt hl
    rw [List.getElem?_append_right hl'] at hi
    rw [List.getElem?_append_right (by rw [h.1]; exact hl'), h.1]
    cases hk : i - fl.length with
    | zero => rfl
    | succ k => rw [hk] at hi; exact nomatch hi

theorem Fl.more {ps : List (E × E)} {fl : List Bool} (h : Fl ps fl) (qs : List (E × E)) :
    Fl (ps ++ qs) (fl ++ List.replicate qs.length false) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases hl : i < fl.length
  · rw [List.getElem?_append_left hl] at hi
    rw [List.getElem?_append_left (by rw [h.1]; exact hl)]
    exact h.2 i hi
  · have hl' : fl.length ≤ i := Nat.le_of_not_lt hl
    rw [List.getElem?_append_right hl', List.getElem?_replicate] at hi
    split at hi
    · exact nomatch hi
    · exact nomatch hi

/-- A draft, on marks. -/
structure DraftSh where
  flags : List Bool
  dense : List (Nat × Nat)

/-- A draft stands under a draft on marks. -/
def Rd (d : LaidDraft) (e : DraftSh) : Prop :=
  Fl d.t.pairs e.flags ∧ d.dense = e.dense ∧ d.t.denseVars = []

/-! ## 2 The variables -/

def bitVarS (e : DraftSh) (b : LaidBlock) (onI onC : WSh) (xBit : Nat) : Option DraftSh :=
  let lowBits := if b.iIsLow then b.bitsI else b.bitsC
  let ofI := decide (xBit < lowBits) == b.iIsLow
  let bit := if xBit < lowBits then xBit else xBit - lowBits
  let w := if ofI then onI else onC
  if w.values.isSome then
    some { flags := e.flags ++ [true], dense := e.dense ++ [(bit, e.flags.length)] }
  else if bit < w.lo ∧ bit < w.hi then some { e with flags := e.flags ++ [false] }
  else none

def bitVarsS (e : DraftSh) (b : LaidBlock) (onI onC : WSh) : List Nat → Option DraftSh
  | [] => some e
  | x :: xs => (bitVarS e b onI onC x).bind fun e' => bitVarsS e' b onI onC xs

theorem bitVar_sim {d : LaidDraft} {e e' : DraftSh} (b : LaidBlock) (onI onC : IndexWeights)
    (x : Nat) (h : Rd d e) (hs : bitVarS e b (wSh onI) (wSh onC) x = some e') :
    ∃ d', bitVar d b onI onC x = .ok d' ∧ Rd d' e' := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold bitVarS at hs
  unfold bitVar
  simp only at hs ⊢
  generalize hw : (if (decide (x < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
    then onI else onC) = w
  have hw' : (if (decide (x < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
    then wSh onI else wSh onC) = wSh w := by
    rw [← hw]
    exact (apply_ite wSh _ _ _).symm
  rw [hw'] at hs
  generalize (if x < (if b.iIsLow = true then b.bitsI else b.bitsC) then x
    else x - (if b.iIsLow = true then b.bitsI else b.bitsC)) = bit at hs ⊢
  by_cases hv : w.values.isSome = true
  · have hv' : (wSh w).values.isSome = true := by
      show (w.values.map (·.size)).isSome = true
      rw [Option.isSome_map]
      exact hv
    rw [if_pos hv'] at hs
    rw [if_pos hv]
    obtain rfl := Option.some.inj hs
    refine ⟨_, rfl, h1.one, ?_, h3⟩
    show d.dense ++ [(bit, d.t.vars)] = e.dense ++ [(bit, e.flags.length)]
    rw [h2, show d.t.vars = e.flags.length from h1.1]
  · have hv' : ¬ (wSh w).values.isSome = true := by
      show ¬ (w.values.map (·.size)).isSome = true
      rw [Option.isSome_map]
      exact hv
    rw [if_neg hv'] at hs
    rw [if_neg hv]
    by_cases hb : bit < (wSh w).lo ∧ bit < (wSh w).hi
    · rw [if_pos hb] at hs
      obtain rfl := Option.some.inj hs
      have hb1 : bit < w.lo.size := hb.1
      have hb2 : bit < w.hi.size := hb.2
      have e1 : w.lo[bit]? = some w.lo[bit] := Array.getElem?_eq_getElem hb1
      have e2 : w.hi[bit]? = some w.hi[bit] := Array.getElem?_eq_getElem hb2
      rw [e1, e2]
      exact ⟨_, rfl, h1.more [(w.lo[bit], w.hi[bit])], h2, h3⟩
    · rw [if_neg hb] at hs
      exact nomatch hs

theorem bitVars_sim (b : LaidBlock) (onI onC : IndexWeights) :
    ∀ (xs : List Nat) (d : LaidDraft) (e e' : DraftSh), Rd d e →
      bitVarsS e b (wSh onI) (wSh onC) xs = some e' →
      ∃ d', bitVars d b onI onC xs = .ok d' ∧ Rd d' e'
  | [], d, e, e', h, hs => by
    obtain rfl := Option.some.inj hs
    exact ⟨d, rfl, h⟩
  | x :: xs, d, e, e', h, hs => by
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 hs
    obtain ⟨d1, c1, r1⟩ := bitVar_sim b onI onC x h h1
    obtain ⟨d', c2, r2⟩ := bitVars_sim b onI onC xs d1 e1 e' r1 h2
    refine ⟨d', ?_, r2⟩
    show (bitVar d b onI onC x).bind (fun e => bitVars e b onI onC xs) = _
    rw [c1]
    exact c2

/-! ## 3 Above the block -/

def aboveB (w : WSh) (first : Nat) : Bool :=
  w.values.isSome || !(decide (w.lo < 64) && first / 2 ^ w.lo != 0)

theorem above_returns (w : IndexWeights) (first bits : Nat) (h : aboveB (wSh w) first = true) :
    ∃ a, aboveBlock w first bits = .ok a := by
  unfold aboveBlock
  by_cases hv : w.values.isSome = true
  · rw [if_pos hv]
    exact ⟨_, rfl⟩
  · rw [if_neg hv]
    unfold aboveB at h
    have hv' : (wSh w).values.isSome = false := by
      show (w.values.map (·.size)).isSome = false
      rw [Option.isSome_map]
      simpa using hv
    rw [hv', Bool.false_or] at h
    have h' : (!(decide (w.lo.size < 64) && first / 2 ^ w.lo.size != 0)) = true := h
    rw [h']
    exact ⟨_, rfl⟩

/-! ## 4 The block -/

/-- The same law stands in Johnson/Desc/First/Shape/Makes.lean (choicePairs_length), under another
namespace. -/
theorem choice_length : ∀ (n v : Nat), (choicePairs n v).length = n
  | 0, _ => rfl
  | n + 1, v => by
    show (choicePairs n (v / 2)).length + 1 = n + 1
    rw [choice_length n (v / 2)]

/-- The choice of bits laid behind all variables. -/
theorem Rd.choice {d : LaidDraft} {e : DraftSh} (h : Rd d e) (c v : Nat) :
    Rd { d with t := d.t.insertChoice d.t.vars c v }
      { e with flags := e.flags ++ List.replicate c false } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩
  · show Fl (d.t.pairs.take d.t.vars ++ choicePairs c v ++ d.t.pairs.drop d.t.vars) _
    have e1 : d.t.pairs.take d.t.vars = d.t.pairs := List.take_length
    have e2 : d.t.pairs.drop d.t.vars = [] := List.drop_length
    rw [e1, e2, List.append_nil]
    have := h1.more (choicePairs c v)
    rw [choice_length] at this
    exact this
  · show d.t.denseVars.map _ = []
    rw [h3]
    rfl

/-- The dense variables, in the order of the slice's bits. -/
def denseOf (dense : List (Nat × Nat)) : List Nat :=
  (List.range dense.length).map fun i => ((dense.find? fun x => x.1 == i).map (·.2)).getD 0

/-- The last tests, on marks. n: the size of the written-out vector, if there is one. -/
def lastB (flags : List Bool) (dense : List (Nat × Nat)) (n : Option Nat) (first : Nat) : Bool :=
  decide (flags.length ≤ 63) &&
    match n with
    | none => true
    | some n =>
      if dense.isEmpty then decide (first < n)
      else
        decide (first + 2 ^ (denseOf dense).length ≤ n) &&
          ((denseOf dense).all fun d => flags[d]? == some true) && noTwice (denseOf dense)

/-- **THE TEST ON SIZES.** -/
def blockB (b : LaidBlock) (tR tP : Nat) (onI onC : WSh) : Bool :=
  blockFits b tR tP && !(onI.values.isSome && onC.values.isSome) &&
    (onI.lo == onI.hi && onC.lo == onC.hi) && aboveB onI b.firstI && aboveB onC b.firstC &&
    match bitVarsS ⟨[], []⟩ b onI onC ((List.range b.rowBits).map (· + b.placeBits)) with
    | none => false
    | some e₁ =>
      match bitVarsS { e₁ with flags := e₁.flags ++ List.replicate (tR - b.rowBits) false } b onI
          onC (List.range b.placeBits) with
      | none => false
      | some e₂ =>
        lastB (e₂.flags ++ List.replicate (tP - b.placeBits) false) e₂.dense
          (if onI.values.isSome then onI.values else onC.values)
          (if onI.values.isSome then b.firstI else b.firstC)

theorem isSome_wSh (w : IndexWeights) : (wSh w).values.isSome = w.values.isSome := by
  show (w.values.map (·.size)).isSome = _
  rw [Option.isSome_map]

theorem fits_of (t : Tensor) (h1 : t.pairs.length ≤ 63) (h2 : t.denseVars = []) :
    tensorFits t = true := by
  have h1' : decide (t.vars ≤ 63) = true := decide_eq_true h1
  unfold tensorFits
  rw [h1', h2]
  rfl

theorem fits_scale (t : Tensor) (x : E) (h1 : t.pairs.length ≤ 63) (h2 : t.denseVars = []) :
    tensorFits (t.scale x) = true := by
  obtain ⟨s, ps, ds, vs, f⟩ := t
  exact fits_of ⟨mulE s x, ps, ds, vs, f⟩ h1 h2

/-- The last step of the text and its last test, under the marks. -/
theorem last_returns (t : Tensor) (flags : List Bool) (dense : List (Nat × Nat))
    (vals : Option (Array E)) (first : Nat) (hF : Fl t.pairs flags) (hD : t.denseVars = [])
    (h : lastB flags dense (vals.map (·.size)) first = true) :
    ∃ u, ((match vals with
      | none => (pure t : Ans Tensor)
      | some values =>
        if dense.isEmpty then (there "K9.written-value-there" values[first]?).map t.scale
        else pure ({ t with denseVars := denseOf dense }.setValues values first)) >>= fun t' =>
      need "K9.tensor-fits" (tensorFits t') >>= fun _ => pure t') = .ok u := by
  unfold lastB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h63, h⟩ := h
  have hv : decide (t.vars ≤ 63) = true := by
    rw [show t.vars = flags.length from hF.1]
    exact h63
  have hle : t.pairs.length ≤ 63 := by
    rw [hF.1]
    exact of_decide_eq_true h63
  have hft : tensorFits t = true := fits_of t hle hD
  cases vals with
  | none =>
    have hf : tensorFits t = true := hft
    refine ⟨t, ?_⟩
    show (need "K9.tensor-fits" (tensorFits t) >>= fun _ => (pure t : Ans Tensor)) = _
    rw [hf]
    rfl
  | some values =>
    have h' : (if dense.isEmpty then decide (first < values.size)
      else decide (first + 2 ^ (denseOf dense).length ≤ values.size) &&
        ((denseOf dense).all fun d => flags[d]? == some true) && noTwice (denseOf dense)) = true :=
      h
    by_cases he : dense.isEmpty = true
    · rw [if_pos he] at h'
      have hlt : first < values.size := by simpa using h'
      obtain ⟨x, e1⟩ : ∃ x, values[first]? = some x := ⟨_, Array.getElem?_eq_getElem hlt⟩
      have hf : tensorFits (t.scale x) = true := fits_scale t x hle hD
      refine ⟨t.scale x, ?_⟩
      simp only [he, if_true, e1]
      show (need "K9.tensor-fits" (tensorFits (t.scale x)) >>= fun _ =>
        (pure (t.scale x) : Ans Tensor)) = _
      rw [hf]
      rfl
    · rw [if_neg he] at h'
      simp only [Bool.and_eq_true] at h'
      obtain ⟨⟨g1, g2⟩, g3⟩ := h'
      have hf : tensorFits ({ t with denseVars := denseOf dense }.setValues values first) =
          true := by
        unfold tensorFits
        show (decide (t.vars ≤ 63) && ((denseOf dense).isEmpty ||
          decide (first + 2 ^ (denseOf dense).length ≤ values.size)) &&
          ((denseOf dense).all fun d => t.pairs[d]? == some (oneE, oneE)) &&
          noTwice (denseOf dense)) = true
        rw [hv, g1, g3, Bool.or_true]
        simp only [Bool.true_and, Bool.and_true]
        rw [List.all_eq_true] at g2 ⊢
        intro d hd
        have := g2 d hd
        rw [hF.2 d (by simpa using this)]
        exact beq_self_eq_true _
      refine ⟨{ t with denseVars := denseOf dense }.setValues values first, ?_⟩
      simp only [he, Bool.false_eq_true, if_false]
      show (need "K9.tensor-fits"
        (tensorFits ({ t with denseVars := denseOf dense }.setValues values first)) >>= fun _ =>
        (pure ({ t with denseVars := denseOf dense }.setValues values first) : Ans Tensor)) = _
      rw [hf]
      rfl

theorem pairs_scale (t : Tensor) (x : E) : (t.scale x).pairs = t.pairs := by
  obtain ⟨s, ps, ds, vs, f⟩ := t
  rfl

theorem dense_scale (t : Tensor) (x : E) : (t.scale x).denseVars = t.denseVars := by
  obtain ⟨s, ps, ds, vs, f⟩ := t
  rfl

theorem vals_wSh (onI onC : IndexWeights) :
    (if (wSh onI).values.isSome then (wSh onI).values else (wSh onC).values) =
      (if onI.values.isSome then onI.values else onC.values).map (·.size) := by
  rw [isSome_wSh]
  split <;> rfl

/-- **A TERM ON ONE BLOCK RETURNS WHERE THE TEST ON SIZES ACCEPTS.** -/
theorem blockTensor_returns (b : LaidBlock) (tR tP : Nat) (onI onC : IndexWeights) (sc : E)
    (h : blockB b tR tP (wSh onI) (wSh onC) = true) :
    ∃ t, blockTensor b tR tP onI onC sc = .ok t := by
  unfold blockB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := h
  rw [isSome_wSh, isSome_wSh] at g2
  have g3' : (onI.lo.size == onI.hi.size && onC.lo.size == onC.hi.size) = true := by
    rw [Bool.and_eq_true]
    exact g3
  cases k1 : bitVarsS ⟨[], []⟩ b (wSh onI) (wSh onC)
      ((List.range b.rowBits).map (· + b.placeBits)) with
  | none => rw [k1] at g6; exact nomatch g6
  | some e₁ =>
    rw [k1] at g6
    simp only at g6
    cases k2 : bitVarsS { e₁ with flags := e₁.flags ++ List.replicate (tR - b.rowBits) false } b
        (wSh onI) (wSh onC) (List.range b.placeBits) with
    | none => rw [k2] at g6; exact nomatch g6
    | some e₂ =>
      rw [k2] at g6
      simp only at g6
      rw [vals_wSh, isSome_wSh] at g6
      obtain ⟨d1, c1, r1⟩ := bitVars_sim b onI onC _ { t := { scalar := sc } } ⟨[], []⟩ e₁
        ⟨Fl.nil, rfl, rfl⟩ k1
      have r1' := r1.choice (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits)
      obtain ⟨d2, c2, r2⟩ := bitVars_sim b onI onC _ _ _ e₂ r1' k2
      have r2' := r2.choice (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits)
      obtain ⟨aI, hI⟩ := above_returns onI b.firstI b.bitsI g4
      obtain ⟨aC, hC⟩ := above_returns onC b.firstC b.bitsC g5
      obtain ⟨u, hu⟩ := last_returns
        (((d2.t.insertChoice d2.t.vars (tP - b.placeBits)
          (b.firstPlace / 2 ^ b.placeBits)).scale aI).scale aC)
        _ e₂.dense (if onI.values.isSome then onI.values else onC.values)
        (if onI.values.isSome then b.firstI else b.firstC)
        (by rw [pairs_scale, pairs_scale]; exact r2'.1)
        (by rw [dense_scale, dense_scale]; exact r2'.2.2) g6
      rw [← r2.2.1] at hu
      refine ⟨u, ?_⟩
      unfold blockTensor
      rw [g1, g2, g3']
      show (bitVars { t := { scalar := sc } } b onI onC
        ((List.range b.rowBits).map (· + b.placeBits)) >>= fun d => _) = _
      rw [c1]
      show (bitVars { d1 with t := (d1.t.insertChoice d1.t.vars (tR - b.rowBits)
        (b.firstRow / 2 ^ b.rowBits)) } b onI onC (List.range b.placeBits) >>= fun d => _) = _
      rw [c2]
      show (aboveBlock onI b.firstI b.bitsI >>= fun aI => _) = _
      rw [hI]
      show (aboveBlock onC b.firstC b.bitsC >>= fun aC => _) = _
      rw [hC]
      revert hu
      generalize (if onI.values.isSome = true then onI.values else onC.values) = vals
      intro hu
      cases vals with
      | none => exact hu
      | some values =>
        by_cases he : d2.dense.isEmpty = true
        · simp only [he, if_true] at hu
          show (if d2.dense.isEmpty = true then _ else _) = _
          rw [if_pos he]
          exact hu
        · simp only [he, Bool.false_eq_true, if_false] at hu
          show (if d2.dense.isEmpty = true then _ else _) = _
          rw [if_neg he]
          exact hu

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.blockTensor_returns
#print axioms VerifiableInference.Desc.K9.Shape.last_returns
#print axioms VerifiableInference.Desc.K9.Shape.above_returns
#print axioms VerifiableInference.Desc.K9.Shape.bitVar_sim
#print axioms VerifiableInference.Desc.K9.Shape.bitVars_sim
