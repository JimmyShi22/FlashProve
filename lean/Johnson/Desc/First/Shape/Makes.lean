-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Makes.lean: THE MAKE OF A TENSOR AND OF A FORM UNDER THE LIBRARY's
OPERATIONS: what Single.lean's TensorSh and FormSh see of a result is a function of what they see
of the arguments, and of numbers. General laws; nothing is evaluated.

What it is for. The batching of a group's rows and the fold lay forms that later guards read (how
many variables a tensor has, which are written out, a slice's size, an entry's index). That these
makes hang on no field element is what lets such a guard be written on a shape.

  1 Tensors. `tensorSh_scale`. `choicePairs_length`, `TensorSh.insertChoice`,
    `tensorSh_insertChoice`. `fixPairs_length` (by the library's fixPairs_drop). `fold_push_size`,
    `foldBit_size`, `sliceStep`, `sliceSize`, `sliceLoop`, `slice_loop`, `foldedSlice_size`: the
    size of a folded slice, off sizes. `TensorSh.fixLow`, **`tensorSh_fixLow`**: fixing the lowest
    variables.
  2 Forms. `FormSh.add`, `addEntry`, `plus`, `insertChoice` with `formSh_add`, `formSh_addEntry`,
    `formSh_scale`, `formSh_plus`, `formSh_addForm`, `formSh_insertChoice`. `mergeIdx`,
    `merge_loop`, `mergeEntries_idx`: the single entries' indices behind a merging: sorted, each
    once. `FormSh.fixLow`, **`formSh_fixLow`**: by the library's Form.fixLow_eq_plain
    (OnBytes/Iop/FixExact.lean): the road that shares folded slices returns what the plain road
    returns.

Limits. The library's tensorBelow, which can drop a term by a value, has no law here: it is called
by none of these operations. mergeIdx sorts (List.mergeSort): a closed term with such a sort can be
dear for Lean's kernel (it has run out of memory at a list of 31 members). Nothing on what a form is
worth. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Single
import OnBytes.Iop.FixExact
import OnBytes.Iop.SpreadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes

/-! ## 1 Tensors -/

theorem tensorSh_scale (v : Tensor) (x : E) : tensorSh (v.scale x) = tensorSh v := by
  cases v
  simp only [Tensor.scale, tensorSh]

theorem choicePairs_length : ∀ (n value : Nat), (choicePairs n value).length = n
  | 0, _ => rfl
  | n + 1, value => by
    show (choicePairs n (value / 2)).length + 1 = n + 1
    rw [choicePairs_length n]

/-- Tensor.insertChoice on makes. -/
def TensorSh.insertChoice (v : TensorSh) (pos count : Nat) : TensorSh :=
  { v with
    pairs := v.pairs + count
    denseVars := v.denseVars.map fun d => if pos ≤ d then d + count else d }

theorem tensorSh_insertChoice (v : Tensor) (pos count value : Nat) :
    tensorSh (v.insertChoice pos count value) = (tensorSh v).insertChoice pos count := by
  cases v with
  | mk scalar pairs denseVars values first =>
    have h : (pairs.take pos ++ choicePairs count value ++ pairs.drop pos).length =
        pairs.length + count := by
      simp only [List.length_append, List.length_take, List.length_drop, choicePairs_length]
      omega
    simp only [Tensor.insertChoice, tensorSh, TensorSh.insertChoice, h]

theorem fixPairs_length (ps : List (E × E)) (g : List E) (s : E) :
    (fixPairs ps g s).2.length = ps.length - g.length := by
  rw [fixPairs_drop, List.length_drop]

theorem fold_push_size {α : Type} (f : Nat → α) : ∀ (n : Nat) (out : Array α),
    (Nat.fold n (fun idx _ (o : Array α) => o.push (f idx)) out).size = out.size + n
  | 0, _ => rfl
  | n + 1, out => by
    rw [Nat.fold_succ, Array.size_push, fold_push_size f n out]
    omega

theorem foldBit_size (a : Array E) (start size i : Nat) (x : E) :
    (foldBit a start size i x).size = size / 2 := by
  unfold foldBit
  have := fold_push_size (fun idx =>
    foldPairE (a.getD (start + idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i)) zeroE)
      (a.getD (start + idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i) + 2 ^ i) zeroE) x) (size / 2)
    (Array.mkEmpty (size / 2))
  simpa using this

/-- One step of the loop of Tensor.foldedSlice, on sizes: the vector's size, where the slice begins,
the slice's size. -/
def sliceStep (dv : List Nat) (glen : Nat) (s : Nat × Nat × Nat) (i : Nat) : Nat × Nat × Nat :=
  match dv[i]? with
  | some d => if d < glen then (s.2.2 / 2, 0, s.2.2 / 2) else s
  | none => s

/-- The size of Tensor.foldedSlice, off sizes. -/
def sliceSize (dv : List Nat) (values first glen : Nat) : Nat :=
  let s := (List.range dv.length).reverse.foldl (sliceStep dv glen) (values, first, 2 ^ dv.length)
  if s.2.1 == 0 && s.1 == s.2.2 then s.1 else min (s.2.1 + s.2.2) s.1 - s.2.1

/-- The loop of Tensor.foldedSlice. -/
def sliceLoop (v : Tensor) (g : List E) (l : List Nat) (s : Array E × Nat × Nat) :
    Array E × Nat × Nat :=
  l.foldl (fun (s : Array E × Nat × Nat) i =>
    match v.denseVars[i]? with
    | some d =>
      if d < g.length then (foldBit s.1 s.2.1 s.2.2 i (g.getD d zeroE), 0, s.2.2 / 2) else s
    | none => s) s

theorem slice_loop (v : Tensor) (g : List E) : ∀ (l : List Nat) (s : Array E × Nat × Nat),
    ((sliceLoop v g l s).1.size, (sliceLoop v g l s).2.1, (sliceLoop v g l s).2.2) =
      l.foldl (sliceStep v.denseVars g.length) (s.1.size, s.2.1, s.2.2)
  | [], _ => rfl
  | i :: l, s => by
    unfold sliceLoop
    rw [List.foldl_cons, List.foldl_cons]
    refine (slice_loop v g l _).trans ?_
    congr 1
    unfold sliceStep
    cases v.denseVars[i]? with
    | none => rfl
    | some d =>
      dsimp only
      split
      · rw [foldBit_size]
      · rfl

theorem foldedSlice_size (v : Tensor) (g : List E) :
    (v.foldedSlice g).size = sliceSize v.denseVars v.values.size v.first g.length := by
  have h := slice_loop v g (List.range v.denseVars.length).reverse
    (v.values, v.first, 2 ^ v.denseVars.length)
  have e : v.foldedSlice g =
      (if (sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).2.1 == 0 &&
          (sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).1.size ==
          (sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).2.2 then
        (sliceLoop v g (List.range v.denseVars.length).reverse
          (v.values, v.first, 2 ^ v.denseVars.length)).1
      else
        (sliceLoop v g (List.range v.denseVars.length).reverse
          (v.values, v.first, 2 ^ v.denseVars.length)).1.extract
          (sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).2.1
          ((sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).2.1 +
           (sliceLoop v g (List.range v.denseVars.length).reverse
            (v.values, v.first, 2 ^ v.denseVars.length)).2.2)) := rfl
  rw [e]
  unfold sliceSize
  dsimp only at h ⊢
  rw [← h]
  dsimp only
  generalize sliceLoop v g (List.range v.denseVars.length).reverse
    (v.values, v.first, 2 ^ v.denseVars.length) = s
  by_cases hc : (s.2.1 == 0 && s.1.size == s.2.2) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, Array.size_extract]

/-- Tensor.fixLow on makes. glen: the number of coordinates. -/
def TensorSh.fixLow (v : TensorSh) (glen : Nat) : TensorSh :=
  if v.denseVars.any (· < glen) then
    let dv := (v.denseVars.filter (glen ≤ ·)).map (· - glen)
    if dv.isEmpty then { pairs := v.pairs - glen, denseVars := [], values := 0, first := 0 }
    else
      { pairs := v.pairs - glen, denseVars := dv
        values := sliceSize v.denseVars v.values v.first glen, first := 0 }
  else { v with pairs := v.pairs - glen, denseVars := v.denseVars.map (· - glen) }

theorem tensorSh_fixLow (v : Tensor) (g : List E) :
    tensorSh (v.fixLow g) = (tensorSh v).fixLow g.length := by
  unfold Tensor.fixLow TensorSh.fixLow Tensor.sliceIsCut
  show tensorSh (if v.denseVars.any (· < g.length) = true then _ else _) =
    if v.denseVars.any (· < g.length) = true then _ else _
  split
  · unfold Tensor.fixLowWith
    dsimp only
    show tensorSh (if ((v.denseVars.filter (g.length ≤ ·)).map (· - g.length)).isEmpty = true
      then _ else _) =
      if ((v.denseVars.filter (g.length ≤ ·)).map (· - g.length)).isEmpty = true then _ else _
    split
    · show TensorSh.mk _ _ _ _ = _
      rw [fixPairs_length]
      rfl
    · show TensorSh.mk _ _ _ _ = _
      rw [fixPairs_length, foldedSlice_size]
      rfl
  · show TensorSh.mk _ _ _ _ = _
    rw [fixPairs_length]
    rfl

/-! ## 2 Forms -/

def FormSh.add (f : FormSh) (v : TensorSh) : FormSh := { f with tensors := v :: f.tensors }
def FormSh.addEntry (f : FormSh) (index : Nat) : FormSh := { f with entries := index :: f.entries }
def FormSh.plus (f other : FormSh) : FormSh :=
  { tensors := other.tensors ++ f.tensors, entries := other.entries ++ f.entries }
def FormSh.insertChoice (f : FormSh) (pos count value : Nat) : FormSh :=
  { tensors := f.tensors.map (·.insertChoice pos count)
    entries := f.entries.map fun e =>
      e % 2 ^ pos + (value % 2 ^ count) * 2 ^ pos + (e / 2 ^ pos) * 2 ^ (pos + count) }

theorem formSh_add (f : Form) (v : Tensor) : formSh (f.add v) = (formSh f).add (tensorSh v) := rfl
theorem formSh_addEntry (f : Form) (i : Nat) (c : E) :
    formSh (f.addEntry i c) = (formSh f).addEntry i := rfl

theorem formSh_scale (f : Form) (x : E) : formSh (f.scale x) = formSh f := by
  cases f with
  | mk ts es =>
    have h1 : (ts.map (·.scale x)).map tensorSh = ts.map tensorSh := by
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      exact tensorSh_scale v x
    have h2 : (es.map fun e => (e.1, mulE e.2 x)).map (·.1) = es.map (·.1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      rfl
    simp only [Form.scale, formSh, h1, h2]

theorem formSh_plus (f other : Form) : formSh (f.plus other) = (formSh f).plus (formSh other) := by
  unfold Form.plus formSh FormSh.plus
  simp only [List.map_append]

theorem formSh_addForm (f other : Form) (x : E) :
    formSh (f.addForm other x) = (formSh f).plus (formSh other) := by
  unfold Form.addForm
  rw [formSh_plus, formSh_scale]

theorem formSh_insertChoice (f : Form) (pos count value : Nat) :
    formSh (f.insertChoice pos count value) = (formSh f).insertChoice pos count value := by
  unfold Form.insertChoice formSh FormSh.insertChoice
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  exact tensorSh_insertChoice v pos count value

/-- mergeEntries on indices. -/
def mergeIdx (l : List Nat) : List Nat :=
  ((l.mergeSort fun a b => a ≤ b).foldl
    (fun acc a =>
      match acc with
      | b :: r => if a == b then b :: r else a :: acc
      | [] => [a])
    []).reverse

theorem merge_loop : ∀ (l : List (Nat × E)) (acc : List (Nat × E)),
    (l.foldl (fun acc a =>
      match acc with
      | b :: r => if a.1 == b.1 then (b.1, addE b.2 a.2) :: r else a :: acc
      | [] => [a]) acc).map (·.1) =
    (l.map (·.1)).foldl (fun acc a =>
      match acc with
      | b :: r => if a == b then b :: r else a :: acc
      | [] => [a]) (acc.map (·.1))
  | [], _ => rfl
  | a :: l, acc => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, merge_loop l]
    congr 1
    cases acc with
    | nil => rfl
    | cons b r =>
      dsimp only [List.map_cons]
      split <;> rfl

theorem mergeEntries_idx (l : List (Nat × E)) :
    (mergeEntries l).map (·.1) = mergeIdx (l.map (·.1)) := by
  unfold mergeEntries mergeIdx
  rw [List.map_reverse]
  congr 1
  refine (merge_loop _ []).trans ?_
  congr 1
  exact List.map_mergeSort (fun _ _ _ _ => rfl)

/-- Form.fixLow on makes. -/
def FormSh.fixLow (f : FormSh) (glen : Nat) : FormSh :=
  { tensors := f.tensors.map (·.fixLow glen), entries := mergeIdx (f.entries.map (· / 2 ^ glen)) }

theorem formSh_fixLow (f : Form) (g : List E) (times : E) :
    formSh (f.fixLow g times) = (formSh f).fixLow g.length := by
  rw [Form.fixLow_eq_plain]
  unfold Form.fixLowPlain formSh FormSh.fixLow
  dsimp only
  rw [mergeEntries_idx]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  show tensorSh ((v.scale times).fixLow g) = _
  rw [tensorSh_fixLow, tensorSh_scale]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.tensorSh_insertChoice
#print axioms VerifiableInference.Desc.First.Shape.foldedSlice_size
#print axioms VerifiableInference.Desc.First.Shape.tensorSh_fixLow
#print axioms VerifiableInference.Desc.First.Shape.formSh_addForm
#print axioms VerifiableInference.Desc.First.Shape.formSh_insertChoice
#print axioms VerifiableInference.Desc.First.Shape.mergeEntries_idx
#print axioms VerifiableInference.Desc.First.Shape.formSh_fixLow
#print axioms VerifiableInference.Desc.First.Shape.formSh_addEntry
