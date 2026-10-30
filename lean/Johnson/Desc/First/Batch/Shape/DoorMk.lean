-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMk.lean: THE MAKE OF THE ONE EQUATION's ROW: what the makes of
Johnson/Desc/First/Shape/Single.lean and Rows.lean (TensorSh, FormSh, RowMk: all but the field
elements) see of what K9's texts lay (Johnson/Desc/First/Batch/Lay.lean: blockTensor, blocksForm,
termsRow) is a function of the layout's blocks, of numbers of bits and of the weights' sizes.
General laws, FROM A RETURN; nothing is evaluated.

  `stepD`, `stepsD`: one more variable, on numbers: the number of variables so far, and the list of
    the variables that are written out.
  `Tr`: a draft stands under such a pair, and its tensor names no written-out vector yet.
  `bitVar_tr`, `bitVars_tr`, `Tr.choice`: the text's steps keep that.
  **`blockMk`**: THE MAKE OF A BLOCK's TENSOR, on numbers.
  **`blockTensor_mk`**: K9.blockTensor b tR tP onI onC sc = .ok t: then tensorSh t = blockMk b tR tP
    (the sizes of the two weights' written-out vectors, where there are such).
  **`blocksMk`**, **`blocksForm_mk`**: the same for the sum over a matrix's blocks: formSh c.
  `TermSh`, `termShOf`: a term without its weights: its link, its array's name, the sizes of its
    weights' written-out vectors. **`termsMk`**, **`termsRow_mk`**: where K9.termsRow returns: the
    row's forms' makes are termsMk of the terms' shapes, behind those that the row had; its kind,
    terms, single entries and runs stay.

Limits. From a return alone. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorGives
import Johnson.Desc.First.Shape.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (LaidBlock)
open VerifiableInference.Desc.First.Shape (TensorSh tensorSh FormSh formSh)

/-! ## 1 The variables, on numbers -/

/-- One more variable. vI, vC: the weights on the rows | on the columns are written out. -/
def stepD (b : LaidBlock) (vI vC : Bool) (x : Nat × List (Nat × Nat)) (xBit : Nat) :
    Nat × List (Nat × Nat) :=
  let lowBits := if b.iIsLow then b.bitsI else b.bitsC
  let ofI := decide (xBit < lowBits) == b.iIsLow
  let bit := if xBit < lowBits then xBit else xBit - lowBits
  (x.1 + 1, if (if ofI then vI else vC) then x.2 ++ [(bit, x.1)] else x.2)

def stepsD (b : LaidBlock) (vI vC : Bool) (x : Nat × List (Nat × Nat)) (xs : List Nat) :
    Nat × List (Nat × Nat) := xs.foldl (stepD b vI vC) x

/-- A draft stands under a pair of numbers; its tensor names no written-out vector yet. -/
def Tr (d : LaidDraft) (x : Nat × List (Nat × Nat)) : Prop :=
  d.t.pairs.length = x.1 ∧ d.dense = x.2 ∧ d.t.denseVars = [] ∧ d.t.values = #[] ∧ d.t.first = 0

theorem bitVar_tr {d d' : LaidDraft} {x : Nat × List (Nat × Nat)} (b : LaidBlock)
    (onI onC : IndexWeights) (xBit : Nat) (h : bitVar d b onI onC xBit = .ok d') (ht : Tr d x) :
    Tr d' (stepD b onI.values.isSome onC.values.isSome x xBit) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := ht
  unfold bitVar at h
  unfold stepD
  simp only at h ⊢
  have ew : (if (decide (xBit < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
      then onI.values.isSome else onC.values.isSome) =
      (if (decide (xBit < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
        then onI else onC).values.isSome := by
    generalize (decide (xBit < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = c
    cases c <;> rfl
  rw [ew]
  generalize (if (decide (xBit < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
    then onI else onC) = w at h ⊢
  generalize (if xBit < (if b.iIsLow = true then b.bitsI else b.bitsC) then xBit
    else xBit - (if b.iIsLow = true then b.bitsI else b.bitsC)) = bit at h ⊢
  by_cases hv : w.values.isSome = true
  · rw [if_pos hv] at h
    obtain rfl := Except.ok.inj h
    rw [if_pos hv]
    refine ⟨?_, ?_, t3, t4, t5⟩
    · show (d.t.pairs ++ [(oneE, oneE)]).length = _
      simp [t1]
    · show d.dense ++ [(bit, d.t.pairs.length)] = _
      rw [t1, t2]
  · rw [if_neg hv] at h
    rw [if_neg hv]
    cases e1 : w.lo[bit]? with
    | none => rw [e1] at h; exact nomatch h
    | some l =>
      cases e2 : w.hi[bit]? with
      | none => rw [e1, e2] at h; exact nomatch h
      | some hh =>
        rw [e1, e2] at h
        obtain rfl := Except.ok.inj h
        refine ⟨?_, t2, t3, t4, t5⟩
        show (d.t.pairs ++ [(l, hh)]).length = _
        simp [t1]

theorem bitVars_tr (b : LaidBlock) (onI onC : IndexWeights) :
    ∀ (xs : List Nat) (d d' : LaidDraft) (x : Nat × List (Nat × Nat)),
      bitVars d b onI onC xs = .ok d' → Tr d x →
      Tr d' (stepsD b onI.values.isSome onC.values.isSome x xs)
  | [], d, d', x, h, ht => by
    obtain rfl : d = d' := Except.ok.inj h
    exact ht
  | y :: xs, d, d', x, h, ht => by
    have h' : (bitVar d b onI onC y).bind (fun e => bitVars e b onI onC xs) = .ok d' := h
    cases h1 : bitVar d b onI onC y with
    | error e => rw [h1] at h'; exact nomatch h'
    | ok e =>
      rw [h1] at h'
      exact bitVars_tr b onI onC xs e d' _ h' (bitVar_tr b onI onC y h1 ht)

/-- The choice of bits laid behind all variables. -/
theorem Tr.choice {d : LaidDraft} {x : Nat × List (Nat × Nat)} (h : Tr d x) (c v : Nat) :
    Tr { d with t := d.t.insertChoice d.t.vars c v } (x.1 + c, x.2) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := h
  refine ⟨?_, t2, ?_, t4, t5⟩
  · show (d.t.insertChoice d.t.vars c v).pairs.length = _
    rw [ins_len, t1]
  · show d.t.denseVars.map _ = []
    rw [t3]
    rfl

/-! ## 2 A block's tensor -/

/-- **THE MAKE OF A BLOCK's TENSOR.** nI, nC: the sizes of the written-out vectors of the weights on
the rows | on the columns, where there are such. -/
def blockMk (b : LaidBlock) (tR tP : Nat) (nI nC : Option Nat) : TensorSh :=
  let x₁ := stepsD b nI.isSome nC.isSome (0, []) ((List.range b.rowBits).map (· + b.placeBits))
  let x₂ := stepsD b nI.isSome nC.isSome (x₁.1 + (tR - b.rowBits), x₁.2) (List.range b.placeBits)
  let len := x₂.1 + (tP - b.placeBits)
  match (if nI.isSome then nI else nC) with
  | none => ⟨len, [], 0, 0⟩
  | some n =>
    if x₂.2.isEmpty then ⟨len, [], 0, 0⟩
    else ⟨len, denseOf x₂.2, n, if nI.isSome then b.firstI else b.firstC⟩

/-- The text's tail, on makes. -/
theorem tail_mk (t₀ u : Tensor) (dense : List (Nat × Nat)) (vals : Option (Array E))
    (first : Nat) (h3 : t₀.denseVars = []) (h4 : t₀.values = #[]) (h5 : t₀.first = 0)
    (h : (match vals with
      | none =>
        (pure t₀ : Ans Tensor) >>= fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
      | some values =>
        if dense.isEmpty then
          (there "K9.written-value-there" values[first]?).map t₀.scale >>= fun t =>
            need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
        else
          (pure ({ t₀ with denseVars := denseOf dense }.setValues values first) : Ans Tensor) >>=
            fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t) = .ok u) :
    tensorSh u = (match vals.map (·.size) with
      | none => ⟨t₀.pairs.length, [], 0, 0⟩
      | some n =>
        if dense.isEmpty then ⟨t₀.pairs.length, [], 0, 0⟩
        else ⟨t₀.pairs.length, denseOf dense, n, first⟩) := by
  have e0 : tensorSh t₀ = ⟨t₀.pairs.length, [], 0, 0⟩ := by
    unfold tensorSh
    rw [h3, h4, h5]
    rfl
  cases vals with
  | none =>
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨t, e, -, e2⟩ := h
    obtain rfl := Except.ok.inj e
    obtain rfl := Except.ok.inj e2
    exact e0
  | some values =>
    by_cases he : dense.isEmpty = true
    · simp only [he, if_true, ans_bind, need_ok, exists_const] at h
      obtain ⟨t, e, -, e2⟩ := h
      obtain rfl := Except.ok.inj e2
      cases hx : values[first]? with
      | none => rw [hx] at e; exact nomatch e
      | some x =>
        rw [hx] at e
        obtain rfl : t₀.scale x = t := Except.ok.inj e
        show tensorSh (t₀.scale x) = (if dense.isEmpty then _ else _)
        rw [if_pos he, VerifiableInference.Desc.First.Shape.tensorSh_scale]
        exact e0
    · simp only [he, Bool.false_eq_true, if_false, ans_bind, need_ok, exists_const] at h
      obtain ⟨t, e, -, e2⟩ := h
      obtain rfl := Except.ok.inj e
      obtain rfl := Except.ok.inj e2
      show _ = (if dense.isEmpty then _ else _)
      rw [if_neg he]
      rfl

theorem scale_rest (t : Tensor) (x : E) :
    (t.scale x).denseVars = t.denseVars ∧ (t.scale x).values = t.values ∧
      (t.scale x).first = t.first := by
  cases t
  exact ⟨rfl, rfl, rfl⟩

theorem blockTensor_mk (b : LaidBlock) (tR tP : Nat) (onI onC : IndexWeights) (sc : E)
    (t : Tensor) (h : blockTensor b tR tP onI onC sc = .ok t) :
    tensorSh t = blockMk b tR tP (onI.values.map (·.size)) (onC.values.map (·.size)) := by
  unfold blockTensor at h
  simp only [ans_bind, need_ok, exists_const] at h
  obtain ⟨-, -, -, d1, c1, d2, c2, aI, -, aC, -, h⟩ := h
  have r0 : Tr { t := { scalar := sc } } (0, []) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have r1 := bitVars_tr b onI onC _ _ _ _ c1 r0
  have r2 := bitVars_tr b onI onC _ _ _ _ c2
    (r1.choice (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits))
  have r3 := r2.choice (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits)
  obtain ⟨q1, -, q3, q4, q5⟩ := r3
  generalize hT : d2.t.insertChoice d2.t.vars (tP - b.placeBits)
    (b.firstPlace / 2 ^ b.placeBits) = T₀ at h
  have q1' := q1
  dsimp only at q1'
  rw [hT] at q1'
  have q3' : T₀.denseVars = [] := by rw [← hT]; exact q3
  have q4' : T₀.values = #[] := by rw [← hT]; exact q4
  have q5' : T₀.first = 0 := by rw [← hT]; exact q5
  have hm := tail_mk
    ((T₀.scale aI).scale aC) t d2.dense (if onI.values.isSome then onI.values else onC.values)
    (if onI.values.isSome then b.firstI else b.firstC)
    (by rw [(scale_rest _ _).1, (scale_rest _ _).1]; exact q3')
    (by rw [(scale_rest _ _).2.1, (scale_rest _ _).2.1]; exact q4')
    (by rw [(scale_rest _ _).2.2, (scale_rest _ _).2.2]; exact q5') (by
      revert h
      generalize (if onI.values.isSome = true then onI.values else onC.values) = vals
      intro h
      cases vals with
      | none => simpa only [ans_bind, need_ok, exists_const] using h
      | some values =>
        by_cases he : d2.dense.isEmpty = true
        · simpa only [he, if_true, ans_bind, need_ok, exists_const] using h
        · simpa only [he, Bool.false_eq_true, if_false, ans_bind, need_ok, exists_const] using h)
  rw [hm, pairs_scale, pairs_scale]
  rw [q1', r2.2.1]
  unfold blockMk
  simp only [Option.isSome_map]
  have ev : (if onI.values.isSome = true then onI.values else onC.values).map (·.size) =
      (if onI.values.isSome = true then onI.values.map (·.size)
        else onC.values.map (·.size)) := by
    split <;> rfl
  rw [ev]

/-! ## 3 The sum over a matrix's blocks -/

/-- **THE MAKE OF THE SUM OVER A MATRIX's BLOCKS**, from a make f on. -/
def blocksFrom (tR tP : Nat) (nI nC : Option Nat) (f : FormSh) (blocks : List LaidBlock) : FormSh :=
  blocks.foldl (fun f b => f.add (blockMk b tR tP nI nC)) f

def blocksMk (blocks : List LaidBlock) (tR tP : Nat) (nI nC : Option Nat) : FormSh :=
  blocksFrom tR tP nI nC ⟨[], []⟩ blocks

theorem blocks_from (tR tP : Nat) (onI onC : IndexWeights) (sc : E) :
    ∀ (blocks : List LaidBlock) (f c : Form),
      blocks.foldlM (fun (f : Form) b => (blockTensor b tR tP onI onC sc).map f.add) f = .ok c →
      formSh c = blocksFrom tR tP (onI.values.map (·.size)) (onC.values.map (·.size)) (formSh f)
        blocks
  | [], f, c, h => by
    obtain rfl : f = c := Except.ok.inj h
    rfl
  | b :: bs, f, c, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨f₁, h1, h2⟩ := (ans_bind _ _ _).1 h
    cases ht : blockTensor b tR tP onI onC sc with
    | error e => rw [ht] at h1; exact nomatch h1
    | ok t =>
      rw [ht] at h1
      obtain rfl : f.add t = f₁ := Except.ok.inj h1
      rw [blocks_from tR tP onI onC sc bs _ c h2,
        VerifiableInference.Desc.First.Shape.formSh_add, blockTensor_mk b tR tP onI onC sc t ht]
      rfl

theorem blocksForm_mk (blocks : List LaidBlock) (tR tP : Nat) (onI onC : IndexWeights) (sc : E)
    (c : Form) (h : blocksForm blocks tR tP onI onC sc = .ok c) :
    formSh c = blocksMk blocks tR tP (onI.values.map (·.size)) (onC.values.map (·.size)) :=
  blocks_from tR tP onI onC sc blocks {} c h

/-! ## 4 The terms as a row -/

open VerifiableInference.Desc.First.Shape (RowMk rowMk MainMk mainMk)
open OnBytes.Params (ReqLayout)

/-- A term of the one equation without its weights: the link in which its array was born; the
array's name; the sizes of the written-out vectors of its weights, where there are such. -/
structure TermSh where
  born : Nat
  array : String
  nI : Option Nat
  nC : Option Nat

def termShOf (t : ReqTerm) : TermSh :=
  ⟨t.born, t.array, t.onRows.values.map (·.size), t.onColumns.values.map (·.size)⟩

/-- **THE MAKES OF THE TERMS' FORMS**, behind those in acc. rb, pb: the numbers of row bits and of
place bits of a message's main table. -/
def termsMk (layout : ReqLayout) (f : ReqFrame) (rb pb : Nat → Nat) :
    List TermSh → List MainMk → Option (List MainMk)
  | [], acc => some acc
  | t :: ts, acc =>
    ((layout.link[t.born]?).bind fun arrays => arrays.find? fun a => a.name == t.array).bind
      fun a => (messageNow f t.born a.message).bind fun o =>
        termsMk layout f rb pb ts (acc ++ [⟨o, blocksMk a.blocks (rb o) (pb o) t.nI t.nC⟩])

theorem termsRow_mk (layout : ReqLayout) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), termsRow layout f S ts row = .ok row' →
      termsMk layout f (S.rowBits · .main) (S.placeBits · .main) (ts.map termShOf)
        (rowMk row).forms = some (rowMk row').forms ∧
      (rowMk row').kind = (rowMk row).kind ∧ (rowMk row').terms = (rowMk row).terms ∧
      (rowMk row').units = (rowMk row).units ∧ (rowMk row').runs = (rowMk row).runs
  | [], row, row', h => by
    obtain rfl : row = row' := Except.ok.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, row, row', h => by
    unfold termsRow at h
    simp only [ans_bind, there_ok] at h
    obtain ⟨a, ha, o, ho, c, hc, h⟩ := h
    obtain ⟨r1, r2, r3, r4, r5⟩ := termsRow_mk layout f S ts _ row' h
    refine ⟨?_, r2, r3, r4, r5⟩
    show (((layout.link[t.born]?).bind fun arrays => arrays.find? fun a => a.name == t.array).bind
      fun a => (messageNow f t.born a.message).bind fun o =>
        termsMk layout f (S.rowBits · .main) (S.placeBits · .main) (ts.map termShOf)
          ((rowMk row).forms ++ [⟨o, blocksMk a.blocks (S.rowBits o .main) (S.placeBits o .main)
            (termShOf t).nI (termShOf t).nC⟩])) = _
    rw [ha]
    show ((messageNow f t.born a.message).bind fun o => _) = _
    rw [ho]
    show termsMk layout f (S.rowBits · .main) (S.placeBits · .main) (ts.map termShOf)
      ((rowMk row).forms ++ [⟨o, blocksMk a.blocks (S.rowBits o .main) (S.placeBits o .main)
        (termShOf t).nI (termShOf t).nC⟩]) = _
    rw [← r1]
    congr 1
    show _ = ((row.forms.push ⟨o, c⟩).toList.map mainMk)
    rw [Array.toList_push, List.map_append]
    show _ = (rowMk row).forms ++ [⟨o, formSh c⟩]
    rw [blocksForm_mk _ _ _ _ _ _ c hc]
    rfl

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.blocksForm_mk
#print axioms VerifiableInference.Desc.K9.Shape.termsRow_mk
#print axioms VerifiableInference.Desc.K9.Shape.bitVars_tr
#print axioms VerifiableInference.Desc.K9.Shape.tail_mk
#print axioms VerifiableInference.Desc.K9.Shape.blockTensor_mk
