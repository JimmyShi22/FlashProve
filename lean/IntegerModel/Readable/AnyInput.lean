-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/AnyInput.lean: model_eq (IntegerModel/Readable/Main.lean), stated with the
arguments of IntegerTransformer.model (IntegerModel/Model.lean) as the variables.
  model_eq_any   on arguments that pass wellFormed and have an expert, and on an array of 1 ..
                 s.positions numbers below the vocabulary's size, IntegerTransformer.model is the
                 library's program at the renamed arguments (none on an empty or a longer array)
  model_none_of_wellFormed, model_none_of_token   none where wellFormed says no, and where a number
                                                  is not a token
So where the function gives some y at such arguments, RunsK holds and y is the first arg-max of lgK
at the last position (Inst/Model/Program.lean), at the arguments written here.
IntegerModel.programNextToken is defined by the same lgK, RunsK at Maverick's sizes
(IntegerModel/Reply.lean).
-/
import IntegerModel.Readable.Main

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

/-! ## The renamings: arrays as functions

No arithmetic except the tables' key - 2^15, the softmax key's toNat and the rotary if-then-else,
with 2 ^ s.rotaryScale and 0 in a layer without the rotary step.
-/

/-- the sizes, at T positions.  The scales that a Params carries are set to 0: XK, lgK, RunsK do not
read them -/
def paramsTo (s : IntegerTransformer.Settings) (T : ℕ) : Params :=
  { T := T, V := s.vocabulary, layers := s.layers, d := s.width, nq := s.queryHeads,
    nkv := s.keyValueHeads, ch := s.headDim, f := s.hidden, fe := s.expertHidden, nexp := s.experts,
    kq := 0, kk := 0, kv := 0, ko := 0, kg := 0, ku := 0, kd := 0, kr := 0, kg' := 0, ku' := 0,
    n1 := ⟨0, 0, 0⟩, n2 := ⟨0, 0, 0⟩, nf := ⟨0, 0, 0⟩, expRows := 0, sh := 0 }
def scaleTo (rows : ℤ) (p : IntegerTransformer.LayerSettings) : LayerScale :=
  { kq := p.queryShift, kk := p.keyShift, kv := p.valueShift, ko := p.outputShift,
    kg := p.gateShift, ku := p.upShift, kd := p.downShift, kr := p.routerShift,
    kg' := p.routedGateShift, ku' := p.routedUpShift,
    n1 := { M := p.attentionBits, K := p.attentionShift, eps := p.attentionEps },
    n2 := { M := p.feedForwardBits, K := p.feedForwardShift, eps := p.feedForwardEps },
    expRows := rows, sh := p.softmaxShift }
def kapTo (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables) : ℕ → LayerScale :=
  fun L => scaleTo tables.exponential.size (s.perLayer.entry L)
def nfTo (s : IntegerTransformer.Settings) : NormPar :=
  { M := s.finalBits, K := s.finalShift, eps := s.finalEps }
def tablesTo (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables) : Tables :=
  { SILU := fun a => tables.silu.read (a - 2 ^ 15),
    SIGM := fun a => tables.sigmoid.read (a - 2 ^ 15),
    Exp := fun u => tables.exponential.entry u.toNat,
    C := fun L i j =>
        if (s.perLayer.entry L).rotary = true then (tables.cosine.entry i).entry j
        else 2 ^ s.rotaryScale,
    S := fun L i j =>
        if (s.perLayer.entry L).rotary = true then (tables.sine.entry i).entry j else 0 }
def layerTo (W : IntegerTransformer.LayerWeights) : LayerW :=
  { Wq := fun j c => (W.query.entry j).entry c, Wk := fun j c => (W.key.entry j).entry c,
    Wv := fun j c => (W.value.entry j).entry c, Wo := fun j c => (W.output.entry j).entry c,
    Wg := fun j c => (W.shared.gate.entry j).entry c,
    Wu := fun j c => (W.shared.up.entry j).entry c,
    Wd := fun j c => (W.shared.down.entry j).entry c, Wr := fun j e => (W.router.entry j).entry e,
    Eg := fun e j c => ((W.routed.entry e).gate.entry j).entry c,
    Eu := fun e j c => ((W.routed.entry e).up.entry j).entry c,
    Ed := fun e j c => ((W.routed.entry e).down.entry j).entry c }
def weightsTo (weights : IntegerTransformer.Weights) : Weights :=
  { layer := fun L => layerTo (weights.perLayer.entry L),
    Emb := fun a j => (weights.embedding.entry a).entry j,
    H := fun j v => (weights.head.entry j).entry v }

/-! ## What wellFormed gives; the theorem; where the function gives none -/

theorem entry_mem {α : Type} [Inhabited α] (v : Array α) {k : ℕ} (h : k < v.size) :
    v.entry k ∈ v := by
  have e : v.entry k = v[k] := by simp [Array.entry, Array.getD, h]
  rw [e]
  exact Array.getElem_mem h

theorem hasSize_row {r c : ℕ} {W : Array (Array ℤ)}
    (h : IntegerTransformer.hasSize r c W = true) {a : ℕ} (ha : a < r) : (W.entry a).size = c := by
  unfold IntegerTransformer.hasSize at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  have := Array.all_eq_true_iff_forall_mem.1 h.2 (W.entry a) (entry_mem W (h.1 ▸ ha))
  exact beq_iff_eq.1 this

theorem row_eq (v : Array ℤ) {n : ℕ} (h : v.size = n) : v = tabl n fun j => v.entry j := by
  apply Array.ext
  · simp [tabl, h]
  · intro i h1 _
    simp [tabl, Array.entry, Array.getD, h1]

section Any
variable (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
  (weights : IntegerTransformer.Weights)
  (hwf : IntegerTransformer.wellFormed s tables weights = true)
include hwf

theorem good_of (hn : 0 < s.experts) (T : ℕ) : IntegerModel.Runnable.Good (paramsTo s T) := by
  simp only [IntegerTransformer.wellFormed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, -⟩, h5⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
            -⟩,
          -⟩,
        -⟩,
      -⟩ := hwf
  exact ⟨Nat.dvd_of_mod_eq_zero h5, ⟨h1, Nat.dvd_of_mod_eq_zero h3⟩, hn⟩

omit hwf in
theorem sameScales_any (L : ℕ) : SameScales L (s.perLayer.entry L) (kapTo s tables L) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

omit hwf in
theorem sameTables_any (T L : ℕ) :
    SameTables (paramsTo s T) s.positions s (s.perLayer.entry L) tables (tablesTo s tables)
      L (kapTo s tables L).expRows where
  cos _ _ _ _ := rfl
  sin _ _ _ _ := rfl
  rows := rfl
  exp u _ := by
    show _ = tables.exponential.entry ((u : ℤ).toNat)
    rw [Int.toNat_natCast]
  silu key _ _ := by
    show _ = tables.silu.read (key + 2 ^ 15 - 2 ^ 15)
    rw [add_sub_cancel_right]
  sigm key _ _ := by
    show _ = tables.sigmoid.read (key + 2 ^ 15 - 2 ^ 15)
    rw [add_sub_cancel_right]

omit hwf in
theorem sameLayer_any (T L : ℕ) (W : IntegerTransformer.LayerWeights) :
    SameLayer (paramsTo s T) L W (layerTo W) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

theorem emb_any {a : ℕ} (ha : a < s.vocabulary) :
    weights.embedding.entry a = tabl s.width fun j => (weights.embedding.entry a).entry j := by
  have hw := hwf
  unfold IntegerTransformer.wellFormed at hw
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨-, h17⟩, -⟩, -⟩, -⟩, -⟩ := hw
  exact row_eq _ (hasSize_row h17 ha)

theorem same_any (T : ℕ) :
    Same (paramsTo s T) s.positions (kapTo s tables) (nfTo s) (fun _ => tablesTo s tables)
      (weightsTo weights) s tables weights where
  sizes := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  scales L _ := sameScales_any s tables L
  finalBits := rfl
  finalShift := rfl
  finalEps := rfl
  tables L _ := sameTables_any s tables T L
  layer L _ := sameLayer_any s T L _
  emb _ ha := emb_any s tables weights hwf ha
  head _ _ _ _ := rfl

variable (hn : 0 < s.experts)
  (prompt : Array ℕ) (htok : ∀ i (h : i < prompt.size), prompt[i] < s.vocabulary)

/-- the tokens as the library takes them -/
def promptTo (s : IntegerTransformer.Settings) (prompt : Array ℕ)
    (htok : ∀ i (h : i < prompt.size), prompt[i] < s.vocabulary) :
    Fin (paramsTo s prompt.size).T → Fin (paramsTo s prompt.size).V :=
  fun i => ⟨prompt[i.val]'i.isLt, htok i.val i.isLt⟩

omit hwf in
theorem ofFn_promptTo : (Array.ofFn fun i => (promptTo s prompt htok i).val) = prompt := by
  apply Array.ext
  · simp [paramsTo]
  · intro i h1 h2
    simp [promptTo]
    rfl

include hn in
/-- The function's own arguments as the variables. Hypotheses (in the "variable" lines above):
hwf: wellFormed is true; hn: there is an expert; htok: every number of the prompt is below the
vocabulary's size. -/
theorem model_eq_any
    [Decidable (RunsK (paramsTo s prompt.size) (kapTo s tables) (nfTo s)
          (fun _ => tablesTo s tables) (weightsTo weights) (promptTo s prompt htok))] :
    IntegerTransformer.model s tables weights prompt = if 0 < prompt.size ∧
    prompt.size ≤ s.positions ∧
    RunsK (paramsTo s prompt.size) (kapTo s tables) (nfTo s) (fun _ => tablesTo s tables)
      (weightsTo weights) (promptTo s prompt htok) then
          some (argTo
            (lgK (paramsTo s prompt.size) (kapTo s tables) (nfTo s) (fun _ => tablesTo s tables)
              (weightsTo weights) (promptTo s prompt htok) (prompt.size - 1))
            (s.vocabulary - 1))
        else none := by
  have h := model_is (paramsTo s prompt.size) (good_of s tables weights hwf hn _) s.positions
    (kapTo s tables) (nfTo s) (fun _ => tablesTo s tables) (weightsTo weights) s tables weights
    (same_any s tables weights hwf _) (promptTo s prompt htok)
  unfold toks at h
  rw [ofFn_promptTo] at h
  exact (h.iff ⟨fun a => a.2, fun a => ⟨hwf, a⟩⟩).eq_ite

end Any

/-- where wellFormed says no: none -/
theorem model_none_of_wellFormed (s : IntegerTransformer.Settings)
    (tables : IntegerTransformer.Tables) (weights : IntegerTransformer.Weights) (prompt : Array ℕ)
    (h : IntegerTransformer.wellFormed s tables weights ≠ true) :
    IntegerTransformer.model s tables weights prompt = none := by
  unfold IntegerTransformer.model
  rw [if_neg]
  intro a
  rw [Bool.and_eq_true] at a
  exact h a.1

/-- a number that is no token: none -/
theorem model_none_of_token (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) (prompt : Array ℕ)
    (h : ¬ ∀ i (hi : i < prompt.size), prompt[i] < s.vocabulary) :
    IntegerTransformer.model s tables weights prompt = none := by
  unfold IntegerTransformer.model
  rw [if_neg]
  intro a
  rw [Bool.and_eq_true] at a
  have b := a.2
  unfold IntegerTransformer.isPrompt at b
  rw [Bool.and_eq_true] at b
  refine h fun i hi => ?_
  have := (Array.all_eq_true_iff_forall_mem.1 b.2) prompt[i] (Array.getElem_mem hi)
  simpa using this

end IntegerModel.Readable
