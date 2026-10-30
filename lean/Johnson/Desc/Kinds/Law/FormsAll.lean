-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FormsAll.lean: A TOOL: WHATEVER PROPERTY OF A LINEAR FORM IS KEPT BY THE FORMS' ARITHMETIC, HOLDS OF THE READS' ENTRIES AND OF WHAT WAS HEARD, HOLDS OF ALL 35 FORMS OF THE OUTPUT HEAD's THREE RUNS
OF CLAIMS. (All of the forms' arithmetic is Aff.addMul.) One proof in place of one for each property (Law/Covered.lean and Law/CoveredNorm.lean go the same way by hand, with bounds on the entries' numbers, which
this tool does not carry).
  Kept P       P (a + k b) of P a and P b; P of every form that names no entry and no slot.
  ReadsHave P  P of every entry of the twelve reads, as a variable.
  HeardHas P   P of the variables of what was heard that the 35 forms name, and of the four sumchecks' own forms.
  all35        Kept P → ReadsHave P → HeardHas P → every form of every run of claims has P.
WHAT IT IS NOT. A tool: no law by itself. The five and four keys and "join"'s form are not among the 35.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Statement
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.NormSquares

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open Norm (lt ls d lPd T S2)

/-- The property is kept by the forms' arithmetic. -/
structure Kept (P : Form → Prop) : Prop where
  addMul : ∀ {a b : Form} (k : E), P a → P b → P (Aff.addMul a b k)
  bare : ∀ f : Form, f.ents = #[] → f.slots = #[] → P f

namespace Kept

variable {P : Form → Prop} (C : Kept P)
include C

theorem const (v : E) : P (Aff.ofConst v) := C.bare _ rfl rfl
theorem add {f g : Form} (hf : P f) (hg : P g) : P (f + g) := C.addMul _ hf hg
theorem sub {f g : Form} (hf : P f) (hg : P g) : P (f - g) := C.addMul _ hf hg
theorem scale {f : Form} (hf : P f) (k : E) : P (Aff.scale f k) :=
  C.addMul _ (C.bare _ rfl rfl) hf
theorem smulE (k : E) {f : Form} (hf : P f) : P (k • f) := C.scale hf _
theorem smulN (n : Nat) {f : Form} (hf : P f) : P (n • f) := C.scale hf _
theorem sm (n : Nat) {f : Form} (hf : P f) : P (OnBytes.Desc.First.P6.sm n f) := C.scale hf _
theorem addN {f : Form} (hf : P f) (n : Nat) :
    P (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) := C.addMul _ hf (C.const _)
theorem subN {f : Form} (hf : P f) (n : Nat) :
    P (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) := C.addMul _ hf (C.const _)
theorem addE {f : Form} (hf : P f) (x : E) :
    P (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) := C.addMul _ hf (C.const _)
theorem Eadd (x : E) {f : Form} (hf : P f) :
    P (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) := C.addMul _ (C.const _) hf
theorem subE {f : Form} (hf : P f) (x : E) :
    P (HSub.hSub (α := Form) (β := E) (γ := Form) f x) := C.addMul _ hf (C.const _)
theorem natCast (n : Nat) : P ((n : Nat) : Form) := C.const _

theorem sums (n : Nat) (f : Nat → Form) (h : ∀ i, P (f i)) : P (sumTo n f) := by
  unfold sumTo
  induction n with
  | zero => exact C.const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact C.add ih (h n)

theorem sums6 (n : Nat) (f : Nat → Form) (h : ∀ i, P (f i)) :
    P (OnBytes.Desc.First.P6.sumTo n f) := by
  unfold OnBytes.Desc.First.P6.sumTo
  induction n with
  | zero => exact C.const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact C.add ih (h n)

theorem dig (D : Nat → Form) (hD : ∀ j, P (D j)) (j n : Nat) :
    P (OnBytes.Desc.First.P6.dig D j n) := C.sums6 n _ fun _ => C.sm _ (hD _)

end Kept

/-- Every field of the row that the forms read has P. -/
structure RowHas (P : Form → Prop) (r : P6.Row) : Prop where
  Vlo : P r.Vlo
  Vhi : P r.Vhi
  a : P r.a
  b : P r.b
  s0 : P r.s0
  sig : P r.sig
  l1 : P r.l1
  h1 : P r.h1
  Blo : P r.Blo
  Bhi : P r.Bhi
  kap : P r.kap
  Rlo : P r.Rlo
  Rhi : P r.Rhi
  R : P r.R
  q1 : P r.q1
  rr : P r.rr
  rq : P r.rq
  c : ∀ s, P (r.c s)

open OnBytes.Desc.First.P6 (sm nat dig) in
theorem rowHas {P : Form → Prop} (C : Kept P) (D : Nat → Form) (hD : ∀ j, P (D j)) :
    RowHas P (P6.Row.ofDigits D) := by
  have dg := C.dig D hD
  have ha : P (P6.Row.ofDigits D).a := by
    show P (sm 2 (D 58) + D 59 + sm (2 ^ 8) (D 60) + sm (2 ^ 16) (D 61))
    exact C.add (C.add (C.add (C.sm _ (hD 58)) (hD 59)) (C.sm _ (hD 60))) (C.sm _ (hD 61))
  have hb : P (P6.Row.ofDigits D).b := by
    show P (D 62 + sm (2 ^ 8) (D 63))
    exact C.add (hD 62) (C.sm _ (hD 63))
  have hlo : P (P6.Row.ofDigits D).Rlo := by
    show P (dig D 80 3)
    exact dg 80 3
  have hhi : P (P6.Row.ofDigits D).Rhi := by
    show P (dig D 83 3)
    exact dg 83 3
  constructor
  · show P (dig D 0 6)
    exact dg 0 6
  · show P (dig D 6 4)
    exact dg 6 4
  · exact ha
  · exact hb
  · exact hD 59
  · show P ((P6.Row.ofDigits D).a + sm (2 ^ 24) (P6.Row.ofDigits D).b)
    exact C.add ha (C.sm _ hb)
  · show P (dig D 64 5)
    exact dg 64 5
  · show P (dig D 69 5)
    exact dg 69 5
  · show P (dig D 74 3)
    exact dg 74 3
  · show P (dig D 77 2)
    exact dg 77 2
  · show P (D 79 - nat 4)
    exact C.sub (hD 79) (C.const _)
  · exact hlo
  · exact hhi
  · show P ((P6.Row.ofDigits D).Rlo + sm (2 ^ 24) (P6.Row.ofDigits D).Rhi)
    exact C.add hlo (C.sm _ hhi)
  · show P (dig D 86 3)
    exact dg 86 3
  · show P (dig D 89 5)
    exact dg 89 5
  · show P (dig D 94 5)
    exact dg 94 5
  · intro s
    show P (if s == 0 then nat 0 else if s == 9 then D 9
      else dig D (10 + 6 * (s - 1)) 6 - nat (2 ^ 47))
    split
    · exact C.const _
    · split
      · exact hD 9
      · exact C.sub (dg _ 6) (C.const _)

theorem carries_have {P : Form → Prop} (C : Kept P) (D Wf : Nat → Form) (hD : ∀ j, P (D j))
    (hW : ∀ s, P (Wf s)) :
    ∀ f, f ∈ OnBytes.Desc.First.P6.carries (P6.Row.ofDigits D) D Wf → P f := by
  intro f hf
  have R := rowHas C D hD
  rw [OnBytes.Desc.First.P6.carries_eq] at hf
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
  exact C.sub (C.sub (C.add (hW s) (R.c s)) (hD s)) (C.sm _ (R.c (s + 1)))

theorem lines_have {P : Form → Prop} (C : Kept P) (D Pr : Nat → Form) (eps : E) (two : Form)
    (hD : ∀ j, P (D j)) (hP : ∀ n, P (Pr n)) (h2 : P two) :
    ∀ f, f ∈ OnBytes.Desc.First.P6.lines (P6.Row.ofDigits D) Pr eps two → P f := by
  intro f hf
  have R := rowHas C D hD
  rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
    OnBytes.Desc.First.P6.reciprocal_eq] at hf
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact C.sub (C.sub (hP 1) R.Blo) (C.sm _ R.Bhi)
  · exact C.add (C.sub (C.sub (C.sub (C.add R.Vlo (C.const _)) (hP 0)) (C.sm _ R.Blo)) R.l1)
      (C.sm _ R.kap)
  · exact C.sub (C.sub (C.sub R.Vhi R.Bhi) (hP 2)) R.kap
  · exact C.sub (C.add R.l1 R.h1) (C.sm _ R.sig)
  · exact C.sub (C.add (hP 4) (hP 5)) R.q1
  · exact hP 6
  · exact C.sub (C.sub (C.sub (C.sub (C.add h2 R.sig) R.s0) (C.sm _ (hP 3))) (C.sm _ R.q1))
      (C.sm _ R.rr)
  · exact C.add (C.sub (C.add R.rr R.rq) R.sig) (C.const _)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard] [FinalNorm.Reads] [Reads]

/-- P of every entry of the reads. -/
structure ReadsHave (P : Form → Prop) : Prop where
  norm : ∀ r i, P (FinalNorm.entry r i)
  head : ∀ r i, P (entry r i)

/-- P of what was heard, as far as the 35 forms name it. -/
structure HeardHas (P : Form → Prop) : Prop where
  W : ∀ s, P (Norm.W.getD s {}).var
  Pr : ∀ n, P (Norm.P.getD n {}).var
  sqLeft : ∀ S0, P (Norm.squares.left S0)
  sqEnd : ∀ j, P (Norm.squares.end_ j).var
  prLeft : ∀ S0, P (Norm.products.left S0)
  prClaimed : P Norm.products.claimed.var
  prEnd : ∀ j, P (Norm.products.end_ j).var
  nmLeft : ∀ S0, P (FinalNorm.normed.left S0)
  nmEnd : ∀ j, P (FinalNorm.normed.end_ j).var
  lgLeft : ∀ S0, P (logits.left S0)
  lgEnd : ∀ j, P (logits.end_ j).var

section All

variable {P : Form → Prop} (C : Kept P) (R : ReadsHave P) (H : HeardHas P)
include C R H

theorem norm29 : ∀ f, f ∈ FinalNorm.forms → P f := by
  intro f hf
  have dPV : ∀ j, P (Norm.digit .rowsAtPV 0 j) := fun j => C.addN (R.norm .rowAtPV j) _
  have dPr : ∀ j, P (Norm.digit .rowsAtProducts 0 j) := fun j =>
    C.addN (R.norm .rowAtProducts j) _
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rw [squareForms_eq] at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact H.sqLeft _
        · exact C.sub (H.sqEnd 0) (H.sqEnd 1)
        · exact C.sub (H.sqEnd 0) (C.sums _ _ fun i => C.sums _ _ fun k => C.sums _ _ fun l =>
            C.smulE _ (R.norm .streamAtSquares _))
      · rw [productForms_eq] at hf
        have Rw := rowHas C (Norm.digit .rowsAtProducts 0) dPr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · exact C.sub H.prClaimed (C.sums _ _ fun n => C.smulE _ (H.Pr n))
        · exact H.prLeft _
        · exact C.sub (H.prEnd 0) Rw.a
        · exact C.sub (H.prEnd 1) Rw.b
        · exact C.sub (H.prEnd 2) Rw.Rlo
        · exact C.sub (H.prEnd 3) Rw.Rhi
    · rw [rowForms_eq, List.mem_append] at hf
      rcases hf with hf | hf
      · exact carries_have C _ _ dPV (fun s => H.W _) f hf
      · exact lines_have C _ _ _ _ dPV (fun n => H.Pr _) (C.const _) f hf
  · simp only [FinalNorm.normedForms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact H.nmLeft _
    · exact C.sub (H.nmEnd 0) (rowHas C _ fun j => C.addN (R.norm .rowAtNormed j) _).R
    · exact C.sub (H.nmEnd 1) (C.sums _ _ fun i => C.sums _ _ fun l =>
        C.smulE _ (R.norm .streamAtNormed _))

theorem atCosts_has (n : Number) : P (atCosts n) := by
  unfold atCosts
  exact C.sums _ _ fun l => C.smulN _ (C.addE (R.head .rowAtCosts _) _)

theorem summed_has (n : Number) : P (summed n) := by
  unfold summed
  exact C.sums _ _ fun l => C.smulN _ (C.addN (R.head .rowCount _) _)

theorem policy4 : ∀ f, f ∈ policy → P f := by
  intro f hf
  unfold policy at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · unfold mean
    exact C.subN (C.add (C.add (summed_has C R H _) (C.smulN _ (summed_has C R H _)))
      (summed_has C R H _)) _
  · unfold count
    exact C.sub (C.add (summed_has C R H _) (summed_has C R H _)) (C.natCast _)
  · unfold clip
    exact C.subE (C.add (atCosts_has C R H _) (atCosts_has C R H _)) _
  · unfold table tableValuesAtCosts
    exact C.subE (C.add (atCosts_has C R H _) (C.Eadd _ (C.sums _ _ fun l => C.sums _ _ fun i =>
      C.smulN _ (R.head .wideAtCosts _)))) _

theorem logits2 : ∀ f, f ∈ logitForms → P f := by
  intro f hf
  unfold logitForms at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact H.lgLeft _
  · refine C.sub (H.lgEnd 0) (C.sums _ _ fun k => C.smulE _ ?_)
    unfold FinalNorm.actAt
    exact C.add (R.head .actAtLogits _) (C.smulN _ (R.head .actAtLogits _))

/-- **ALL 35.** -/
theorem all35 : ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → P f := by
  intro name fs hl f hf
  have hm : (name, fs) ∈ claims := by
    unfold claims at hl ⊢
    simp only [List.lookup_cons, List.lookup_nil] at hl
    split at hl
    · rename_i h1
      have : name = "norm" := by simpa using h1
      rw [this, ← Option.some.inj hl]
      simp
    · split at hl
      · rename_i _ h2
        have : name = "policy" := by simpa using h2
        rw [this, ← Option.some.inj hl]
        simp
      · split at hl
        · rename_i _ _ h3
          have : name = "logits" := by simpa using h3
          rw [this, ← Option.some.inj hl]
          simp
        · cases hl
  unfold claims at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact norm29 C R H f hf
  · exact policy4 C R H f hf
  · exact logits2 C R H f hf

end All

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.all35
