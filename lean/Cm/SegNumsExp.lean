-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegNumsExp.lean: degrees of expressions: how many atoms a term of a compiled family has
(`Fam.DegLe`, Cb/Req/ReqNumsGlue.lean), read off the expression (Cm/SegHeadExp.lean) by one rule for
each operation.

Definitions and proofs.
An expression (`Ex`) is a list of monomials, each a table of coefficients (`Mono.coef`: a function
of the instance and the vertex) times a product of atoms. The lower level (`Ex0`) has atoms that
are affine in cells and index atoms (`Atom0`); the upper level (`Ex1`) has sum atoms too
(`Atom.sum`: the sum over further variables of a sum of terms, `Poly0`, Cb/Req/ReqSpec.lean; `sumA`
makes the expression of one such atom from an `Ex0`). `Ex1.fam` compiles an `Ex1` into a family,
`Ex0.poly` an `Ex0` into a sum of terms.

Main names:
  `Dg n p`, `D1 n p`, `fam_degLe`: see their doc comments.
  Rules: one theorem for each operation (`Dg.zero` to `Dg.ite`, `Dg.aff0`, `Dg.idx0`, `D1.zero` to
    `D1.ite`); `Dg.of`, `D1.of`.
  `affFam_degLe`: a family that is affine in cells: 1.

How to use: build the proof with the rules; its bound comes out as an expression in max and +, and
`D1.of _ (by decide)` then gives the wanted n.
Limits: statements on data only. Nothing here knows a segment. All bounds on numbers of atoms and on
degrees here are upper bounds.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadExp
import Cb.Req.ReqNumsGlueProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Seg
open Cb Finset Cm.Seg.Ex

/-! ## 1. Any type of atoms -/

section Gen
variable {X E α : Type} [Field E]

/-- no monomial has more than n atoms -/
def Dg (n : ℕ) (p : Ex X E α) : Prop := ∀ m ∈ p.lst, m.atoms.length ≤ n

theorem Dg.of {a n : ℕ} {p : Ex X E α} (h : Dg a p) (hle : a ≤ n) : Dg n p := fun m hm =>
  le_trans (h m hm) hle
theorem Dg.zero : Dg 0 (Ex.zero : Ex X E α) := fun _ h => absurd h List.not_mem_nil
theorem Dg.pub (c : X → ℕ → E) : Dg 0 (Ex.pub c : Ex X E α) := fun m hm => by
  have hm' : m ∈ [(⟨c, []⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  exact le_refl _
theorem Dg.con (k : E) : Dg 0 (Ex.con k : Ex X E α) := Dg.pub _
theorem Dg.one (a : α) : Dg 1 (Ex.one a : Ex X E α) := fun m hm => by
  have hm' : m ∈ [(⟨fun _ _ => 1, [a]⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  exact le_refl _
theorem Dg.add {a b : ℕ} {p q : Ex X E α} (hp : Dg a p) (hq : Dg b q) :
    Dg (max a b) (p + q) := fun m hm => by
  rcases List.mem_append.1 (show m ∈ p.lst ++ q.lst from hm) with h | h
  · exact le_trans (hp m h) (le_max_left _ _)
  · exact le_trans (hq m h) (le_max_right _ _)
theorem Dg.sc {a : ℕ} (c : X → ℕ → E) {p : Ex X E α} (hp : Dg a p) :
    Dg a (Ex.sc c p) := fun m hm => by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1
    (show m ∈ List.map (fun m => (⟨fun x b => c x b * m.coef x b, m.atoms⟩ : Mono X E α)) p.lst
      from hm)
  exact hp n hn
theorem Dg.smul {a : ℕ} (k : E) {p : Ex X E α} (hp : Dg a p) : Dg a (k • p) := Dg.sc _ hp
theorem Dg.sub {a b : ℕ} {p q : Ex X E α} (hp : Dg a p) (hq : Dg b q) : Dg (max a b) (p - q) :=
  Dg.add hp (Dg.sc _ hq)
theorem Dg.mul {a b : ℕ} {p q : Ex X E α} (hp : Dg a p) (hq : Dg b q) :
    Dg (a + b) (p * q) := fun m hm => by
  obtain ⟨m1, h1, hm⟩ := List.mem_flatMap.1
    (show m ∈ List.flatMap
        (fun m =>
          List.map
            (fun n => (⟨fun x b => m.coef x b * n.coef x b, m.atoms ++ n.atoms⟩ : Mono X E α))
            q.lst) p.lst from hm)
  obtain ⟨m2, h2, rfl⟩ := List.mem_map.1 hm
  show (m1.atoms ++ m2.atoms).length ≤ a + b
  rw [List.length_append]
  exact Nat.add_le_add (hp m1 h1) (hq m2 h2)
theorem Dg.pSum {a n : ℕ} {f : ℕ → Ex X E α} (h : ∀ k < n, Dg a (f k)) : Dg a (Ex.pSum n f) := by
  induction n with
  | zero => exact Dg.zero.of (Nat.zero_le _)
  | succ n ih =>
    exact (Dg.add (ih fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))).of
      (by rw [max_self])
theorem Dg.ite {a b : ℕ} {c : Prop} [Decidable c] {p q : Ex X E α}
    (hp : c → Dg a p) (hq : ¬ c → Dg b q) :
    Dg (max a b) (if c then p else q) := by
  split_ifs with h
  · exact (hp h).of (le_max_left _ _)
  · exact (hq h).of (le_max_right _ _)

/-- a compiled term has as many atoms as some monomial of the list -/
theorem from_len (o : ℕ) (p : List (Mono X E α)) :
    ∀ t ∈ Ex.termsFrom o p, ∃ m ∈ p, t.atoms.length = m.atoms.length := by
  induction p generalizing o with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons m p ih =>
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨m, List.mem_cons_self, by simp⟩
    · obtain ⟨m', hm', e⟩ := ih _ t ht
      exact ⟨m', List.mem_cons_of_mem _ hm', e⟩

theorem terms_len {n : ℕ} {p : Ex X E α} (h : Dg n p) :
    ∀ t ∈ p.terms, t.atoms.length ≤ n := fun t ht => by
  obtain ⟨m, hm, e⟩ := from_len 0 p t ht
  rw [e]
  exact h m hm

/-- beyond the last atom stands the default -/
theorem atomAt_ge (d : α) (p : Ex X E α) {j : ℕ} (hj : p.na ≤ j) : p.atomAt d j = d := by
  unfold Ex.atomAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  rfl

theorem All.imp {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) {p : Ex X E α} (hp : Ex.All Q p) :
    Ex.All Q' p :=
  fun m hm a ha => h a (hp m hm a ha)

end Gen

/-! ## 2. The two levels -/

section Levels
variable {X E : Type} [Field E]

theorem Dg.aff0 (f : ℕ → CForm E) : Dg (X := X) 1 (aff0 f) := Dg.one _
theorem Dg.idx0 (a : IdxAtom E) : Dg (X := X) 1 (idx0 a) := Dg.one _

theorem poly_deg {n v : ℕ} {q : Ex0 X E} (h : Dg n q) : (Ex0.poly v q).toFam.deg ≤ n :=
  (Req.deg_le_iff X E _ n).2 (terms_len h)

/-- the sums among the atoms have degree at most n -/
def In (n : ℕ) (p : Ex1 X E) : Prop := Ex.All (fun a => ∀ w P, a = Atom.sum w P → P.toFam.deg ≤ n) p

/-- no term has more than n atoms, in the expression and under its sum atoms -/
structure D1 (n : ℕ) (p : Ex1 X E) : Prop where
  out : Dg n p
  inn : In n p

theorem In.of {a n : ℕ} {p : Ex1 X E} (h : In a p) (hle : a ≤ n) : In n p :=
  All.imp (fun _ ha w P e => le_trans (ha w P e) hle) h

theorem D1.of {a n : ℕ} {p : Ex1 X E} (h : D1 a p) (hle : a ≤ n) : D1 n p :=
  ⟨h.out.of hle, h.inn.of hle⟩
theorem D1.zero : D1 0 (Ex.zero : Ex1 X E) := ⟨Dg.zero, All.zero⟩
theorem D1.pub (c : X → ℕ → E) : D1 0 (Ex.pub c : Ex1 X E) := ⟨Dg.pub c, All.pub c⟩
theorem D1.con (k : E) : D1 0 (Ex.con k : Ex1 X E) := D1.pub _
theorem D1.aff (f : ℕ → CForm E) : D1 (X := X) 1 (aff f) :=
  ⟨Dg.one _, All.one fun _ _ e => by cases e⟩
theorem D1.idx (a : IdxAtom E) : D1 (X := X) 1 (Seg.idx a) :=
  ⟨Dg.one _, All.one fun _ _ e => by cases e⟩
theorem D1.sumA {a : ℕ} (v w : ℕ) {q : Ex0 X E} (h : Dg a q) : D1 (max 1 a) (sumA v w q) :=
  ⟨(Dg.one _).of (le_max_left _ _), All.one fun _ _ e => by
    cases e
    exact le_trans (poly_deg h) (le_max_right _ _)⟩
theorem D1.add {a b : ℕ} {p q : Ex1 X E} (hp : D1 a p) (hq : D1 b q) : D1 (max a b) (p + q) :=
  ⟨Dg.add hp.out hq.out, All.add (hp.inn.of (le_max_left _ _)) (hq.inn.of (le_max_right _ _))⟩
theorem D1.sub {a b : ℕ} {p q : Ex1 X E} (hp : D1 a p) (hq : D1 b q) : D1 (max a b) (p - q) :=
  ⟨Dg.sub hp.out hq.out, All.sub (hp.inn.of (le_max_left _ _)) (hq.inn.of (le_max_right _ _))⟩
theorem D1.sc {a : ℕ} (c : X → ℕ → E) {p : Ex1 X E} (hp : D1 a p) : D1 a (Ex.sc c p) :=
  ⟨Dg.sc c hp.out, All.sc c hp.inn⟩
theorem D1.smul {a : ℕ} (k : E) {p : Ex1 X E} (hp : D1 a p) : D1 a (k • p) := D1.sc _ hp
theorem D1.mul {a b : ℕ} {p q : Ex1 X E} (hp : D1 a p) (hq : D1 b q) : D1 (a + b) (p * q) :=
  ⟨Dg.mul hp.out hq.out,
    All.mul (hp.inn.of (Nat.le_add_right _ _)) (hq.inn.of (Nat.le_add_left _ _))⟩
theorem D1.pSum {a n : ℕ} {f : ℕ → Ex1 X E} (h : ∀ k < n, D1 a (f k)) : D1 a (Ex.pSum n f) :=
  ⟨Dg.pSum fun k hk => (h k hk).out, All.pSum fun k hk => (h k hk).inn⟩
theorem D1.ite {a b : ℕ} {c : Prop} [Decidable c] {p q : Ex1 X E}
    (hp : c → D1 a p) (hq : ¬ c → D1 b q) :
    D1 (max a b) (if c then p else q) := by
  split_ifs with h
  · exact (hp h).of (le_max_left _ _)
  · exact (hq h).of (le_max_right _ _)

/-- Under `D1 n p`, the compiled family has no term with more than n atoms, nor has a sum among its
atoms. -/
theorem fam_degLe {n v : ℕ} {p : Ex1 X E} (h : D1 n p) : (Ex1.fam v p).DegLe n := by
  refine ⟨(Req.deg_le_iff X E _ n).2 (terms_len h.out), fun j w P e => ?_⟩
  by_cases hj : j < Ex.na p
  · exact Ex.atomAt_all _ h.inn j hj w P e
  · have e' : Ex.atomAt (.base (.cell fun _ => cK 0)) p j = Atom.sum w P := e
    rw [atomAt_ge _ p (not_lt.1 hj)] at e'
    cases e'

/-- a family from lists (Cm/SegAlg.lean: fam) -/
theorem famL_degLe {n v : ℕ} {atoms : List (Atom X E)} {terms : List (Term X E)}
    (ht : ∀ t ∈ terms, t.atoms.length ≤ n)
    (ha : ∀ a ∈ atoms, ∀ w P, a = Atom.sum w P → P.toFam.deg ≤ n) :
    (fam v atoms terms).DegLe n := by
  refine ⟨(Req.deg_le_iff X E _ n).2 ht, fun j w P e => ?_⟩
  have e' : atoms.getD j (.base (.cell fun _ => cK 0)) = Atom.sum w P := e
  by_cases hj : j < atoms.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at e'
    exact ha _ (List.getElem_mem hj) w P e'
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hj)] at e'
    cases e'

theorem affFam_degLe (v : ℕ) (f : ℕ → CForm E) : (affFam (X := X) v f).DegLe 1 :=
  famL_degLe (fun t ht => by
    rw [List.mem_singleton] at ht
    subst ht
    exact le_refl _) fun a ha w P e => by
    rw [List.mem_singleton] at ha
    subst ha
    cases e

theorem DegLe.of {f : Fam X E} {a n : ℕ} (h : f.DegLe a) (hle : a ≤ n) : f.DegLe n :=
  ⟨le_trans h.1 hle, fun j w P e => le_trans (h.2 j w P e) hle⟩

end Levels

end Cm.Seg
