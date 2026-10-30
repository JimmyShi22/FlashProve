-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/FoldMake.lean: "A FORM FITS" AND "THE BATCHED ROW FITS THE FOLD" CUT INTO
A HALF ON THE MAKE AND ONE TEST ON VALUES; AND THE MAKE OF WHAT THE FOLD LEAVES. General laws;
nothing is evaluated.

  1 `tensorOrderS`, `onesT`, `tensorInOrder_split`; `formFitsS`, `onesF`, `all_and`,
    **`formFits_split`**: Own.formFits f vars = (formFitsS (formSh f) vars && onesF f)
    (Johnson/Desc/Own/Shapes.lean). onesT IS THE ONE COMPARISON OF FIELD ELEMENTS: at each
    written-out variable the pair is (1, 1).
  2 `weights_size`, `foldOutS`, **`foldOutput_mk`**: singleSh (foldOutput S F row fresh eps gamma
    claim) is foldOutS of: each message's number of main rows, the mask code's message length, the
    fold's shape, the batched row's make, the fresh mask's number and the number of challenges
    (OnBytes/Iop/Fold.lean:335). The two vectors' sizes by foldMaskForm_size and later_length of
    Johnson/Desc/First/Close/Law/CarriedRows.lean.
  3 `foldRowFitsS`, `onesG`, **`foldRowFits_split`**: Own.foldRowFits
    (Johnson/Desc/Own/Fold.lean:98) likewise.

Limits. That the pairs are (1, 1) in what a chain's steps lay is not shown here: no law of this
file carries onesT through the operations. No state is shown at which a half on the make accepts.
Nothing on what a form is worth. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Rows
import Johnson.Desc.First.Close.Law.CarriedRows
import Johnson.Desc.Own.Fold
import Johnson.Desc.Own.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc

/-! ## 1 "A form fits": its half on the make, and its one test on values -/

/-- Own.tensorInOrder without the test on the pairs. -/
def tensorOrderS (v : TensorSh) : Bool :=
  decide (v.pairs ≤ 63) &&
    (v.denseVars.isEmpty || decide (v.first + 2 ^ v.denseVars.length ≤ v.values)) &&
    decide v.denseVars.Nodup

/-- THE TEST ON VALUES: at each written-out variable the pair is (1, 1). -/
def onesT (v : Tensor) : Bool := v.denseVars.all fun d => v.pairs[d]? == some (oneE, oneE)

theorem tensorInOrder_split (v : Tensor) :
    Own.tensorInOrder v = (tensorOrderS (tensorSh v) && onesT v) := by
  unfold Own.tensorInOrder tensorOrderS onesT tensorSh
  dsimp only
  generalize decide (v.pairs.length ≤ 63) = a
  generalize (v.denseVars.isEmpty ||
    decide (v.first + 2 ^ v.denseVars.length ≤ v.values.size)) = b
  generalize (v.denseVars.all fun d => v.pairs[d]? == some (oneE, oneE)) = c
  generalize decide v.denseVars.Nodup = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Own.formFits on the make. -/
def formFitsS (f : FormSh) (vars : Nat) : Bool :=
  (f.tensors.all fun v => v.pairs == vars && tensorOrderS v) &&
    f.entries.all fun e => decide (e < 2 ^ vars)

def onesF (f : Form) : Bool := f.tensors.all onesT

theorem all_and {α : Type} (p q : α → Bool) : ∀ (l : List α),
    (l.all fun x => p x && q x) = (l.all p && l.all q)
  | [] => rfl
  | x :: l => by
    simp only [List.all_cons, all_and p q l]
    cases p x <;> cases q x <;> cases l.all p <;> cases l.all q <;> rfl

/-- **A form fits just if its make fits and the pairs at its written-out variables are (1, 1).** -/
theorem formFits_split (f : Form) (vars : Nat) :
    Own.formFits f vars = (formFitsS (formSh f) vars && onesF f) := by
  unfold Own.formFits formFitsS onesF formSh
  dsimp only
  rw [List.all_map, List.all_map]
  have h : (f.tensors.all fun v => v.pairs.length == vars && Own.tensorInOrder v) =
      ((f.tensors.all ((fun v => v.pairs == vars && tensorOrderS v) ∘ tensorSh)) &&
        f.tensors.all onesT) := by
    rw [← all_and]
    apply List.all_congr rfl
    intro v
    rw [tensorInOrder_split]
    show _ = ((v.pairs.length == vars && tensorOrderS (tensorSh v)) && onesT v)
    rw [Bool.and_assoc]
  rw [h]
  generalize f.tensors.all ((fun v => v.pairs == vars && tensorOrderS v) ∘ tensorSh) = a
  generalize f.tensors.all onesT = b
  have hc : (f.entries.all fun e => decide (e.1 < 2 ^ vars)) =
      f.entries.all ((fun e => decide (e < 2 ^ vars)) ∘ fun x => x.1) := rfl
  rw [hc]
  generalize f.entries.all ((fun e => decide (e < 2 ^ vars)) ∘ fun x => x.1) = c
  cases a <;> cases b <;> cases c <;> rfl

/-! ## 2 What the fold leaves -/

theorem weights_size (k h len : Nat) (g : Array E) :
    (foldMaskWeights k h len g).size =
      (1 + h + (2 * (k - h) - 1) + (if h < k then 1 else 0)) +
        (len - (1 + h + (2 * (k - h) - 1) + (if h < k then 1 else 0))) := by
  unfold foldMaskWeights
  simp only [List.size_toArray, List.length_append, List.length_replicate, List.length_cons,
    List.length_map, List.length_range, First.Close.later_length]
  by_cases e : h < k
  · simp only [e, if_true, List.length_cons, List.length_nil]
    omega
  · simp only [e, if_false, List.length_nil]
    omega

/-- foldOutput on makes. mainRows: each message's number of main rows; ell: the mask code's message
length; glen: the number of the fold's challenges. -/
def foldOutS (mainRows : Nat → Option Nat) (ell : Nat) (F : FoldShape) (row : GroupMk)
    (fresh glen : Nat) : SingleSh :=
  { code := F.code, maskCode := F.maskCode, layout := F.layout, gamma := glen, masks := 2
    fresh := fresh, c := row.c.fixLow glen, kept := row.kept
    d := [row.d / 2 ^ min F.layout.h glen,
      (1 + F.layout.h + (2 * (F.layout.k - F.layout.h) - 1) +
          (if F.layout.h < F.layout.k then 1 else 0)) +
        (ell - (1 + F.layout.h + (2 * (F.layout.k - F.layout.h) - 1) +
          (if F.layout.h < F.layout.k then 1 else 0)))]
    keptRows := (List.range F.layout.members.size).foldl (fun n i =>
      if F.layout.kept.getD i false then n + (mainRows (F.layout.members.getD i noId)).getD 0
      else n) 0 }

/-- **The make of what the fold leaves is a function of the batched row's make, the fold's shape,
the messages' numbers of main rows, the mask code's message length and the number of challenges.**
-/
theorem foldOutput_mk (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : Nat) (eps : E)
    (gamma : List E) (claim : E) :
    singleSh (foldOutput S F row fresh eps gamma claim) =
      foldOutS (fun o => (S.oracles[o]?).map (·.shape.mainRows))
        (S.codes.mask.getD F.maskCode default).ell F (groupMk row) fresh gamma.length := by
  have hk : (row.kept.map fun f => ({ f with c := f.c.scale (foldKeptFactor eps gamma) } :
      KeptForm)).toList.map (fun k => (k.oracle, formSh k.c)) = row.kept.toList.map keptMk := by
    rw [Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro f _
    show (f.oracle, formSh (f.c.scale _)) = (f.oracle, formSh f.c)
    rw [formSh_scale]
  unfold foldOutput singleSh foldOutS
  dsimp only
  rw [formSh_fixLow, hk]
  simp only [List.map_cons, List.map_nil, First.Close.foldMaskForm_size, weights_size]
  rfl

/-! ## 3 "The batched row fits the fold" -/

/-- Own.foldRowFits on makes. ell, ellZk: the two codes' message lengths; tb: each message's main
table's index bits. -/
def foldRowFitsS (ell ellZk : Nat) (tb : Nat → Nat) (F : FoldShape) (row : GroupMk) : Bool :=
  formFitsS row.c (F.layout.k + ceilLog2 ell) && row.d == ellZk * 2 ^ F.layout.h &&
    row.kept.all fun f =>
      (match F.layout.members.idxOf? f.1 with
        | some i => F.layout.kept.getD i false
        | none => false) && formFitsS f.2 (tb f.1)

/-- THE TEST ON VALUES in it. -/
def onesG (row : GroupRow) : Bool := onesF row.c && row.kept.toList.all fun f => onesF f.c

/-- **The batched row fits the fold just if its make fits and the pairs at the written-out variables
of its forms are (1, 1).** -/
theorem foldRowFits_split (S : Statement) (F : FoldShape) (row : GroupRow) :
    Own.foldRowFits S F row =
      (foldRowFitsS (S.codes.base.getD F.code default).ell
        (S.codes.mask.getD F.maskCode default).ell (fun o => S.tableBits o .main) F (groupMk row) &&
        onesG row) := by
  unfold Own.foldRowFits foldRowFitsS onesG
  dsimp only
  rw [formFits_split]
  have hk : (row.kept.all fun f =>
      (match F.layout.members.idxOf? f.oracle with
        | some i => F.layout.kept.getD i false
        | none => false) && Own.formFits f.c (S.tableBits f.oracle .main)) =
      (((groupMk row).kept.all fun f =>
        (match F.layout.members.idxOf? f.1 with
          | some i => F.layout.kept.getD i false
          | none => false) && formFitsS f.2 (S.tableBits f.1 .main)) &&
        row.kept.toList.all fun f => onesF f.c) := by
    show _ = (((row.kept.toList.map keptMk).all _) && _)
    rw [List.all_map, ← all_and, ← Array.all_toList]
    apply List.all_congr rfl
    intro f
    rw [formFits_split]
    exact (Bool.and_assoc _ _ _).symm
  show (formFitsS (formSh row.c) (F.layout.k + ceilLog2 (S.codes.base.getD F.code default).ell) &&
      onesF row.c && (row.d.size == (S.codes.mask.getD F.maskCode default).ell * 2 ^ F.layout.h) &&
      (row.kept.all fun f =>
        (match F.layout.members.idxOf? f.oracle with
          | some i => F.layout.kept.getD i false
          | none => false) && Own.formFits f.c (S.tableBits f.oracle .main))) = _
  rw [hk]
  show (formFitsS (formSh row.c) _ && onesF row.c && (row.d.size == _) && (_ && _)) =
    (formFitsS (formSh row.c) _ && (row.d.size == _) && _ && (onesF row.c && _))
  generalize formFitsS (formSh row.c) _ = a
  generalize onesF row.c = b
  generalize (row.d.size == _) = c
  generalize ((groupMk row).kept.all _) = d
  generalize (row.kept.toList.all fun f => onesF f.c) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.foldRowFits_split
#print axioms VerifiableInference.Desc.First.Shape.tensorInOrder_split
#print axioms VerifiableInference.Desc.First.Shape.formFits_split
#print axioms VerifiableInference.Desc.First.Shape.weights_size
#print axioms VerifiableInference.Desc.First.Shape.foldOutput_mk
