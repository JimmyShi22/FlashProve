-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/ReqRefEx.lean: the sizes of families that are compiled from expressions (Cm/SegHeadExp.lean),
computed by rules on the expression.

Generic lemmas on data; no model. An expression (`Ex`) is a sum of monomials; `Ex1.fam v p` is the
family and `Ex0.poly v p` the sum of terms compiled from it. A family (`Fam`) and its atoms (`Atom`)
are defined in Cb/Req/ReqSpec.lean.

Main names:
  `nm p`: the number of monomials of an expression. `wt ω p`: the sum of the weights ω of the atoms
    of all monomials. `fl p` = `wt` at the weight 1: the number of atoms.
  Rules (marked simp): `nm` and `wt` of zero, pub, con, one, +, -, *, `Ex.sc`, •, pSum,
    if-then-else: nm (p * q) = nm p · nm q, wt ω (p * q) = wt ω p · nm q + nm p · wt ω q.
  `sz_fam`, `sz_poly`: the size (`sz`, Cm/ReqRefNeed.lean) of a compiled family or sum of terms is
    2 fl p.
  `sumsN_fam`: the sums among the atoms of a compiled family are those among the atoms of its
    monomials, in a row. `sS_fam`, `lS_fam`: their sizes together and their number as weights (`ωS`,
    `ωL`). `wLe_fam`: a bound on their further variables from a property of all atoms.
  `ωS_aff` to `nm_idx0`: the weights and `nm` of one-atom expressions (`aff`, `idx`, `sumA`, `aff0`,
    `idx0`): wt ωS (sumA v w q) = 2 fl q, wt ωL (sumA v w q) = 1.
  `sz_affFam` to `wLe_affFam`: the family with one affine atom (`affFam`, Cm/SegAlg.lean): size 2,
    no sum.

Terms: lean/GLOSSARY.md.
-/
import Cm.ReqRefGlueS
import Cm.SegHeadExp

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Ref
open Cb Cb.Req Cm.Seg Cm.Seg.Ex

section
variable {X E α : Type} [Field E]

/-- the number of monomials -/
def nm (p : Ex X E α) : ℕ := p.lst.length
/-- the sum of the weights of the atoms of all monomials -/
def wt (ω : α → ℕ) (p : Ex X E α) : ℕ := ((Ex.flat p).map ω).sum

variable (ω : α → ℕ)

@[simp] theorem nm_zero : nm (Ex.zero : Ex X E α) = 0 := rfl
@[simp] theorem nm_pub (c : X → ℕ → E) : nm (Ex.pub c : Ex X E α) = 1 := rfl
@[simp] theorem nm_con (k : E) : nm (Ex.con k : Ex X E α) = 1 := rfl
@[simp] theorem nm_one (a : α) : nm (Ex.one a : Ex X E α) = 1 := rfl
@[simp] theorem nm_add (p q : Ex X E α) : nm (p + q) = nm p + nm q := List.length_append
@[simp] theorem nm_sc (c : X → ℕ → E) (p : Ex X E α) : nm (Ex.sc c p) = nm p := List.length_map _
@[simp] theorem nm_smul (k : E) (p : Ex X E α) : nm (k • p) = nm p := List.length_map _
@[simp] theorem nm_sub (p q : Ex X E α) : nm (p - q) = nm p + nm q := by
  show nm (p + Ex.sc (fun _ _ => (-1 : E)) q) = _
  rw [nm_add, nm_sc]

@[simp] theorem wt_zero : wt ω (Ex.zero : Ex X E α) = 0 := rfl
@[simp] theorem wt_pub (c : X → ℕ → E) : wt ω (Ex.pub c : Ex X E α) = 0 := rfl
@[simp] theorem wt_con (k : E) : wt ω (Ex.con k : Ex X E α) = 0 := rfl
@[simp] theorem wt_one (a : α) : wt ω (Ex.one a : Ex X E α) = ω a := by simp [wt, Ex.flat, Ex.one]
@[simp] theorem wt_add (p q : Ex X E α) : wt ω (p + q) = wt ω p + wt ω q := by
  show ((List.flatMap (fun m : Mono X E α => m.atoms) (List.append p q)).map ω).sum = _
  rw [List.append_eq, List.flatMap_append, List.map_append, List.sum_append]
  rfl
@[simp] theorem wt_sc (c : X → ℕ → E) (p : Ex X E α) : wt ω (Ex.sc c p) = wt ω p := by
  show ((List.flatMap (fun m : Mono X E α => m.atoms) (List.map _ p)).map ω).sum = _
  rw [List.flatMap_map]
  rfl
@[simp] theorem wt_smul (k : E) (p : Ex X E α) : wt ω (k • p) = wt ω p := wt_sc ω _ p
@[simp] theorem wt_sub (p q : Ex X E α) : wt ω (p - q) = wt ω p + wt ω q := by
  show wt ω (p + Ex.sc (fun _ _ => (-1 : E)) q) = _
  rw [wt_add, wt_sc]

/-- one monomial times an expression -/
theorem mul1 (m : Mono X E α) :
    ∀ q : List (Mono X E α),
      ((List.flatMap (fun n : Mono X E α => n.atoms)
          (List.map
            (fun n => (⟨fun x b => m.coef x b * n.coef x b, m.atoms ++ n.atoms⟩ : Mono X E α))
            q)).map ω).sum =
        (m.atoms.map ω).sum * q.length +
          ((List.flatMap (fun n : Mono X E α => n.atoms) q).map ω).sum
  | [] => by simp
  | n :: q => by
    rw [List.map_cons, List.flatMap_cons, List.map_append, List.sum_append, mul1 m q,
      List.flatMap_cons, List.map_append, List.sum_append, List.map_append,
      List.sum_append, List.length_cons]
    ring

@[simp] theorem nm_mul (p q : Ex X E α) : nm (p * q) = nm p * nm q := by
  show (List.flatMap _ p).length = List.length p * List.length q
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_cons]
    ring

@[simp] theorem wt_mul (p q : Ex X E α) : wt ω (p * q) = wt ω p * nm q + nm p * wt ω q := by
  show ((List.flatMap (fun n : Mono X E α => n.atoms) (List.flatMap _ p)).map ω).sum =
    ((List.flatMap (fun n : Mono X E α => n.atoms) p).map ω).sum * List.length q +
      List.length p * ((List.flatMap (fun n : Mono X E α => n.atoms) q).map ω).sum
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.map_append, List.sum_append, ih, mul1 ω m q,
      List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
    ring

@[simp] theorem nm_pSum (f : ℕ → Ex X E α) : ∀ n, nm (Ex.pSum n f) = ∑ k ∈ Finset.range n, nm (f k)
  | 0 => rfl
  | n + 1 => by
    show nm (Ex.pSum n f + f n) = _
    rw [nm_add, nm_pSum f n, Finset.sum_range_succ]
@[simp] theorem wt_pSum (f : ℕ → Ex X E α) :
    ∀ n, wt ω (Ex.pSum n f) = ∑ k ∈ Finset.range n, wt ω (f k)
  | 0 => rfl
  | n + 1 => by
    show wt ω (Ex.pSum n f + f n) = _
    rw [wt_add, wt_pSum f n, Finset.sum_range_succ]
@[simp] theorem nm_ite (c : Prop) [Decidable c] (p q : Ex X E α) :
    nm (if c then p else q) = if c then nm p else nm q := by split_ifs <;> rfl
@[simp] theorem wt_ite (c : Prop) [Decidable c] (p q : Ex X E α) :
    wt ω (if c then p else q) = if c then wt ω p else wt ω q := by split_ifs <;> rfl

/-- the number of atoms -/
abbrev fl (p : Ex X E α) : ℕ := wt (fun _ => 1) p

theorem fl_eq (p : Ex X E α) : fl p = (Ex.flat p).length := by
  show ((Ex.flat p).map fun _ => 1).sum = _
  simp

/-- the terms of the compiler have as many atoms as the monomials -/
theorem tl_from :
    ∀ (p : List (Mono X E α)) (o : ℕ), tl ((Ex.termsFrom o p).map Term.atoms) =
      (List.flatMap (fun m : Mono X E α => m.atoms) p).length
  | [], _ => rfl
  | m :: p, o => by
    show ((List.range m.atoms.length).map (o + ·)).length +
        tl ((Ex.termsFrom (o + m.atoms.length) p).map Term.atoms) = _
    rw [tl_from p, List.length_map, List.length_range, List.flatMap_cons, List.length_append]

end

section
variable {X E : Type} [Field E]

/-- The size of a compiled family. -/
theorem sz_fam (v : ℕ) (p : Ex1 X E) : sz (Ex1.fam v p) = 2 * fl p := by
  rw [fl_eq]
  show (Ex.flat p).length + tl ((Ex.termsFrom 0 p).map Term.atoms) = _
  rw [tl_from]
  show (Ex.flat p).length + (Ex.flat p).length = _
  omega

theorem sz_poly (v : ℕ) (p : Ex0 X E) : sz (Ex0.poly v p).toFam = 2 * fl p := by
  rw [fl_eq]
  show (Ex.flat p).length + tl ((Ex.termsFrom 0 p).map Term.atoms) = _
  rw [tl_from]
  show (Ex.flat p).length + (Ex.flat p).length = _
  omega

theorem range_getD {α : Type} (d : α) (l : List α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- The sums among the atoms of a compiled family. -/
theorem sumsN_fam (v : ℕ) (p : Ex1 X E) : sumsN (Ex1.fam v p) = (Ex.flat p).filterMap asSum := by
  have h : ∀ (d : Atom X E) (l : List (Atom X E)),
      (List.range l.length).filterMap (fun j => asSum (l.getD j d)) =
        l.filterMap asSum := fun d l => by
    have h1 : ((List.range l.length).map fun j => l.getD j d).filterMap asSum =
        (List.range l.length).filterMap (fun j => asSum (l.getD j d)) := by
      rw [List.filterMap_map]
      rfl
    rw [← h1, range_getD]
  exact h _ _

/-- the weights: the size of a sum; 1 for a sum -/
def ωS (a : Atom X E) : ℕ := (asSum a).elim 0 fun b => sz b.2.toFam
def ωL (a : Atom X E) : ℕ := (asSum a).elim 0 fun _ => 1

theorem filterMap_sum {α β : Type} (g : α → Option β) (u : β → ℕ) :
    ∀ l : List α, ((l.filterMap g).map u).sum = (l.map fun a => (g a).elim 0 u).sum
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← filterMap_sum g u l]
    cases g a with
    | none => simp
    | some b => simp

theorem sS_fam (v : ℕ) (p : Ex1 X E) : sS (Ex1.fam v p) = wt ωS p := by
  unfold sS wt
  rw [sumsN_fam, filterMap_sum]
  rfl

theorem lS_fam (v : ℕ) (p : Ex1 X E) : lS (Ex1.fam v p) = wt ωL p := by
  unfold lS wt
  rw [sumsN_fam]
  have h := filterMap_sum (asSum (X := X) (E := E)) (fun _ => 1) (Ex.flat p)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at h
  rw [h]
  rfl

theorem wLe_fam {v Wm : ℕ} {p : Ex1 X E}
    (h : Ex.All (fun a => ∀ b, asSum a = some b → b.1 ≤ Wm) p) :
    WLe (Ex1.fam v p) Wm := fun a ha => by
  rw [sumsN_fam] at ha
  obtain ⟨c, hc, hca⟩ := List.mem_filterMap.1 ha
  obtain ⟨m, hm, hcm⟩ := List.mem_flatMap.1 hc
  exact h m hm c hcm a hca

@[simp] theorem ωS_aff (f : ℕ → CForm E) : wt ωS (aff f : Ex1 X E) = 0 := by simp [aff, ωS, asSum]
@[simp] theorem ωS_idx (a : IdxAtom E) : wt ωS (Seg.idx a : Ex1 X E) = 0 := by
  simp [Seg.idx, ωS, asSum]
@[simp] theorem ωS_sumA (v w : ℕ) (q : Ex0 X E) : wt ωS (sumA v w q : Ex1 X E) = 2 * fl q := by
  rw [← sz_poly (v + w) q]
  simp [sumA, ωS, asSum]
@[simp] theorem ωL_aff (f : ℕ → CForm E) : wt ωL (aff f : Ex1 X E) = 0 := by simp [aff, ωL, asSum]
@[simp] theorem ωL_idx (a : IdxAtom E) : wt ωL (Seg.idx a : Ex1 X E) = 0 := by
  simp [Seg.idx, ωL, asSum]
@[simp] theorem ωL_sumA (v w : ℕ) (q : Ex0 X E) : wt ωL (sumA v w q : Ex1 X E) = 1 := by
  simp [sumA, ωL, asSum]
@[simp] theorem fl_aff (f : ℕ → CForm E) : wt (fun _ => 1) (aff f : Ex1 X E) = 1 := by simp [aff]
@[simp] theorem fl_idx (a : IdxAtom E) : wt (fun _ => 1) (Seg.idx a : Ex1 X E) = 1 := by
  simp [Seg.idx]
@[simp] theorem fl_sumA (v w : ℕ) (q : Ex0 X E) : wt (fun _ => 1) (sumA v w q : Ex1 X E) = 1 := by
  simp [sumA]
@[simp] theorem fl_aff0 (f : ℕ → CForm E) : wt (fun _ => 1) (aff0 f : Ex0 X E) = 1 := by simp [aff0]
@[simp] theorem fl_idx0 (a : IdxAtom E) : wt (fun _ => 1) (idx0 a : Ex0 X E) = 1 := by simp [idx0]
@[simp] theorem nm_aff (f : ℕ → CForm E) : nm (aff f : Ex1 X E) = 1 := rfl
@[simp] theorem nm_idx (a : IdxAtom E) : nm (Seg.idx a : Ex1 X E) = 1 := rfl
@[simp] theorem nm_sumA (v w : ℕ) (q : Ex0 X E) : nm (sumA v w q : Ex1 X E) = 1 := rfl
@[simp] theorem nm_aff0 (f : ℕ → CForm E) : nm (aff0 f : Ex0 X E) = 1 := rfl
@[simp] theorem nm_idx0 (a : IdxAtom E) : nm (idx0 a : Ex0 X E) = 1 := rfl

/-! ## The family with one affine atom -/

theorem sz_affFam (v : ℕ) (f : ℕ → CForm E) : sz (affFam (X := X) v f) = 2 := rfl
theorem sS_affFam (v : ℕ) (f : ℕ → CForm E) : sS (affFam (X := X) v f) = 0 := rfl
theorem lS_affFam (v : ℕ) (f : ℕ → CForm E) : lS (affFam (X := X) v f) = 0 := rfl
theorem wLe_affFam (v : ℕ) (f : ℕ → CForm E) (Wm : ℕ) : WLe (affFam (X := X) v f) Wm := fun _ h =>
  absurd h List.not_mem_nil

end
end Cm.Ref
