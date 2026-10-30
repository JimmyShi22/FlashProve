-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegHeadExp.lean: an algebra of polynomial expressions in atoms, and one compiler into families
(Cb/Req/ReqSpec.lean: `Fam`, `Poly0`). Nothing here knows a segment, a key or an identity.

In standard terms: a small language of expressions for the values of polynomial conditions at the
vertices of a cube, and its translation into the normal form `Fam`.

Why: a family of Cb/Req/ReqSpec.lean is a list of terms over numbered atoms. The model's keys and
identities are written as formulas: sums and products of values that are affine in cells, of
entries of weight tensors, of sums of such products, with public coefficients. Here a formula is
mirrored line by line, and the numbering is made once, by a program with three theorems.

Main names:
  `Mono X E α`: a monomial: a table of public coefficients (instance, vertex) and the list of the
    atoms, of type α, whose product it multiplies.
  `Ex X E α`: an expression: a list of monomials. Operations: `Ex.pub`, `Ex.con`, `Ex.one`, +, -,
    *, `Ex.sc` c p (a public coefficient table c times p), •, `Ex.pSum`, `Ex.zero`. `Ex.ev`: the
    value, given the values of the atoms.
  `Ex.na`, `Ex.atomAt`, `Ex.terms`: the compiler: the atoms of all monomials in a row; monomial
    number k names its own atoms. Its three theorems: `Ex.ev_compiled`, `Ex.terms_lt`,
    `Ex.atomAt_all`.
  `Ex0`, `Ex1`: expressions for the two levels of Cb/Req/ReqSpec.lean: in atoms of the first two
    kinds (`Atom0`), and of all three (`Atom`). `Ex0.poly v` and `Ex1.fam v` compile them into a
    `Poly0` and a `Fam` (`poly_val`, `poly_wf`, `poly_places`; `fam_val`, `fam_wf`, `fam_places`);
    `sumA v w p`: see its docstring.
  `Ex.All Q`: see its docstring. `WF0`, `WF1`, `Pl0 P`, `Pl1 P`: "all atoms are well formed", "all
    places read have the property P".

How to use it: open Cm.Seg Cm.Seg.Ex (the instances +, -, *, • are scoped). Mirror the formula;
"rw [fam_val]; simp [your definitions]" turns `(Ex1.fam v p).val` into the formula over forms'
values, index atoms at vertices and sums; `fam_wf` and `fam_places` take `WF1` and `Pl1`.
Dead vertices (vertices of the cube that stand for no element of the formula's index set:
Cb/Req/ReqSpec.lean, the head): multiply by a public indicator (`Ex.sc`), add a public padding
value (`Ex.pub`), and let a form be `cK 0` at a dead vertex, so that it names no place there.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegAlg

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Seg
open Cb Finset

/-! ## 1. Expressions over any type of atoms -/

/-- a monomial -/
structure Mono (X E α : Type) where
  coef : X → ℕ → E
  atoms : List α

/-- An expression: a sum of monomials. -/
def Ex (X E α : Type) : Type := List (Mono X E α)

namespace Ex
variable {X E α : Type} [Field E]

def zero : Ex X E α := ([] : List (Mono X E α))
/-- a public coefficient table -/
def pub (c : X → ℕ → E) : Ex X E α := ([⟨c, []⟩] : List (Mono X E α))
/-- a constant -/
def con (k : E) : Ex X E α := pub fun _ _ => k
/-- one atom -/
def one (a : α) : Ex X E α := ([⟨fun _ _ => 1, [a]⟩] : List (Mono X E α))
def add (p q : Ex X E α) : Ex X E α := List.append p q
/-- a public coefficient table times an expression -/
def sc (c : X → ℕ → E) (p : Ex X E α) : Ex X E α :=
  List.map (fun m => ⟨fun x b => c x b * m.coef x b, m.atoms⟩) p
def mul (p q : Ex X E α) : Ex X E α :=
  List.flatMap
    (fun m =>
      List.map (fun n => (⟨fun x b => m.coef x b * n.coef x b, m.atoms ++ n.atoms⟩ : Mono X E α)) q)
    p
def sub (p q : Ex X E α) : Ex X E α := add p (sc (fun _ _ => -1) q)
/-- f 0 + .. + f (n - 1) -/
def pSum : ℕ → (ℕ → Ex X E α) → Ex X E α
  | 0, _ => zero
  | n + 1, f => add (pSum n f) (f n)

scoped instance : Add (Ex X E α) := ⟨add⟩
scoped instance : Sub (Ex X E α) := ⟨sub⟩
scoped instance : Mul (Ex X E α) := ⟨mul⟩
scoped instance : SMul E (Ex X E α) := ⟨fun k p => sc (fun _ _ => k) p⟩

/-- the value of a monomial, given the values of the atoms -/
def mev (Y : α → E) (x : X) (b : ℕ) (m : Mono X E α) : E := m.coef x b * (m.atoms.map Y).prod

/-- The value of an expression, given the values of the atoms. -/
def ev (p : Ex X E α) (Y : α → E) (x : X) (b : ℕ) : E := (List.map (mev Y x b) p).sum

variable (Y : α → E) (x : X) (b : ℕ)

@[simp] theorem ev_zero : (zero : Ex X E α).ev Y x b = 0 := rfl
@[simp] theorem ev_pub (c : X → ℕ → E) : (pub c : Ex X E α).ev Y x b = c x b := by
  simp [pub, ev, mev]
@[simp] theorem ev_con (k : E) : (con k : Ex X E α).ev Y x b = k := by simp [con]
@[simp] theorem ev_one (a : α) : (one a : Ex X E α).ev Y x b = Y a := by simp [one, ev, mev]
@[simp] theorem ev_add (p q : Ex X E α) : (p + q).ev Y x b = p.ev Y x b + q.ev Y x b := by
  show (List.map (mev Y x b) (List.append p q)).sum = _
  rw [List.append_eq, List.map_append, List.sum_append]
  rfl
@[simp] theorem ev_sc (c : X → ℕ → E) (p : Ex X E α) :
    (Ex.sc c p).ev Y x b = c x b * p.ev Y x b := by
  show (List.map (mev Y x b) (List.map _ p)).sum = c x b * (List.map (mev Y x b) p).sum
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun m _ => mul_assoc _ _ _
@[simp] theorem ev_smul (k : E) (p : Ex X E α) : (k • p).ev Y x b = k * p.ev Y x b :=
  ev_sc Y x b _ p
@[simp] theorem ev_sub (p q : Ex X E α) : (p - q).ev Y x b = p.ev Y x b - q.ev Y x b := by
  show (p + Ex.sc (fun _ _ => (-1 : E)) q).ev Y x b = _
  rw [ev_add, ev_sc]
  ring
@[simp] theorem ev_mul (p q : Ex X E α) : (p * q).ev Y x b = p.ev Y x b * q.ev Y x b := by
  show (List.map (mev Y x b) (List.flatMap _ p)).sum =
    (List.map (mev Y x b) p).sum * (List.map (mev Y x b) q).sum
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons, add_mul]
    congr 1
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun n _ => ?_
    show m.coef x b * n.coef x b * ((m.atoms ++ n.atoms).map Y).prod =
      m.coef x b * (m.atoms.map Y).prod * (n.coef x b * (n.atoms.map Y).prod)
    rw [List.map_append, List.prod_append]
    ring
@[simp] theorem ev_pSum (n : ℕ) (f : ℕ → Ex X E α) :
    (pSum n f).ev Y x b = ∑ k ∈ range n, (f k).ev Y x b := by
  induction n with
  | zero => simp [pSum]
  | succ n ih =>
    show (pSum n f + f n).ev Y x b = _
    rw [ev_add, ih, sum_range_succ]
@[simp] theorem ev_ite (c : Prop) [Decidable c] (p q : Ex X E α) :
    (if c then p else q).ev Y x b = if c then p.ev Y x b else q.ev Y x b := by
  split_ifs <;> rfl

/-! ### All atoms of an expression -/

/-- the monomials -/
def lst (p : Ex X E α) : List (Mono X E α) := p

/-- all atoms of all monomials have the property Q -/
def All (Q : α → Prop) (p : Ex X E α) : Prop := ∀ m ∈ p.lst, ∀ a ∈ m.atoms, Q a

variable {Q : α → Prop}
theorem All.zero : All Q (zero : Ex X E α) := fun _ h => absurd h List.not_mem_nil
theorem All.pub (c : X → ℕ → E) : All Q (pub c : Ex X E α) := fun m hm a ha => by
  have hm' : m ∈ [(⟨c, []⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  exact absurd ha List.not_mem_nil
theorem All.con (k : E) : All Q (con k : Ex X E α) := All.pub _
theorem All.one {a : α} (h : Q a) : All Q (one a : Ex X E α) := fun m hm a' ha => by
  have hm' : m ∈ [(⟨fun _ _ => 1, [a]⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  rw [List.mem_singleton] at ha
  exact ha ▸ h
theorem All.add {p q : Ex X E α} (hp : All Q p) (hq : All Q q) : All Q (p + q) := fun m hm => by
  rcases List.mem_append.1 (show m ∈ p.lst ++ q.lst from hm) with h | h
  · exact hp m h
  · exact hq m h
theorem All.sc (c : X → ℕ → E) {p : Ex X E α} (hp : All Q p) : All Q (Ex.sc c p) := fun m hm => by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1
    (show m ∈ List.map (fun m => (⟨fun x b => c x b * m.coef x b, m.atoms⟩ : Mono X E α)) p.lst
      from hm)
  exact hp n hn
theorem All.smul (k : E) {p : Ex X E α} (hp : All Q p) : All Q (k • p) := All.sc _ hp
theorem All.sub {p q : Ex X E α} (hp : All Q p) (hq : All Q q) : All Q (p - q) :=
  All.add hp (All.sc _ hq)
theorem All.mul {p q : Ex X E α} (hp : All Q p) (hq : All Q q) :
    All Q (p * q) := fun m hm a ha => by
  obtain ⟨m1, h1, hm⟩ := List.mem_flatMap.1
    (show m ∈ List.flatMap
        (fun m =>
          List.map
            (fun n => (⟨fun x b => m.coef x b * n.coef x b, m.atoms ++ n.atoms⟩ : Mono X E α))
            q.lst) p.lst from hm)
  obtain ⟨m2, h2, rfl⟩ := List.mem_map.1 hm
  rcases List.mem_append.1 ha with h | h
  · exact hp m1 h1 a h
  · exact hq m2 h2 a h
theorem All.pSum {n : ℕ} {f : ℕ → Ex X E α} (h : ∀ k < n, All Q (f k)) : All Q (pSum n f) := by
  induction n with
  | zero => exact All.zero
  | succ n ih =>
    exact All.add (ih fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))
theorem All.ite {c : Prop} [Decidable c] {p q : Ex X E α} (hp : c → All Q p) (hq : ¬ c → All Q q) :
    All Q (if c then p else q) := by
  split_ifs with h
  · exact hp h
  · exact hq h

/-! ### The compiler -/

/-- the atoms of all monomials, in a row -/
def flat (p : Ex X E α) : List α := List.flatMap (fun m => m.atoms) p
/-- the number of atoms -/
def na (p : Ex X E α) : ℕ := p.flat.length
/-- atom number j; beyond the last one a default -/
def atomAt (d : α) (p : Ex X E α) (j : ℕ) : α := p.flat.getD j d
/-- the terms, when the first atom has the number o -/
def termsFrom : ℕ → List (Mono X E α) → List (Term X E)
  | _, [] => []
  | o, m :: p =>
    ⟨m.coef, (List.range m.atoms.length).map (o + ·)⟩ :: termsFrom (o + m.atoms.length) p
def terms (p : Ex X E α) : List (Term X E) := termsFrom 0 p

theorem map_getD_range (d : α) (pre l post : List α) :
    ((List.range l.length).map (pre.length + ·)).map (fun j => Y ((pre ++ l ++ post).getD j d)) =
      l.map Y := by
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    have hn : n < l.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hn, List.getElem?_eq_getElem hn]
    rfl

theorem ev_from (d : α) (pre : List α) (p : List (Mono X E α)) :
    ((termsFrom pre.length p).map fun t =>
        t.val x b fun j => Y ((pre ++ List.flatMap (fun m => m.atoms) p).getD j d)).sum =
      (List.map (mev Y x b) p).sum := by
  induction p generalizing pre with
  | nil => rfl
  | cons m p ih =>
    rw [termsFrom, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    congr 1
    · show m.coef x b * _ = m.coef x b * _
      congr 2
      rw [List.flatMap_cons, ← List.append_assoc]
      exact map_getD_range Y d pre m.atoms _
    · have := ih (pre ++ m.atoms)
      rw [List.length_append, List.append_assoc] at this
      rw [List.flatMap_cons]
      exact this

/-- The sum of the compiled terms' values is the value of the expression. -/
theorem ev_compiled (d : α) (p : Ex X E α) :
    (p.terms.map fun t => t.val x b fun j => Y (p.atomAt d j)).sum = p.ev Y x b := by
  have := ev_from Y x b d [] p
  simpa [terms, atomAt, flat, ev] using this

theorem from_lt (o : ℕ) (p : List (Mono X E α)) :
    ∀ t ∈ termsFrom o p, ∀ j ∈ t.atoms, j < o + (List.flatMap (fun m => m.atoms) p).length := by
  induction p generalizing o with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons m p ih =>
    intro t ht j hj
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 ht with rfl | ht
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
      have := List.mem_range.1 hn
      omega
    · have := ih (o + m.atoms.length) t ht j hj
      omega

/-- every term names atoms below na -/
theorem terms_lt (p : Ex X E α) : ∀ t ∈ p.terms, ∀ j ∈ t.atoms, j < p.na := fun t ht j hj => by
  have := from_lt 0 p t ht j hj
  simpa [na, flat] using this

/-- what holds of all atoms of all monomials holds of every numbered atom below na -/
theorem atomAt_all (d : α) {p : Ex X E α} (h : All Q p) :
    ∀ j < p.na, Q (p.atomAt d j) := fun j hj => by
  have hj' : j < p.flat.length := hj
  have e : p.atomAt d j = p.flat[j] := by
    unfold atomAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl
  rw [e]
  obtain ⟨m, hm, ha⟩ := List.mem_flatMap.1 (List.getElem_mem hj')
  exact h m hm _ ha

end Ex

/-! ## 2. The two levels of a family -/

section Levels
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- `Ex0`: expressions in atoms of the first two kinds; `Ex1`, below: in atoms of all three kinds -/
abbrev Ex0 (X E : Type) : Type := Ex X E (Atom0 E)
abbrev Ex1 (X E : Type) : Type := Ex X E (Atom X E)

/-- a value that is affine in cells: at the vertex b the form f b -/
def aff0 (f : ℕ → CForm E) : Ex0 X E := Ex.one (.cell f)
def idx0 (a : IdxAtom E) : Ex0 X E := Ex.one (.idx a)
def aff (f : ℕ → CForm E) : Ex1 X E := Ex.one (.base (.cell f))
def idx (a : IdxAtom E) : Ex1 X E := Ex.one (.base (.idx a))

/-- The compiled sum of terms, on v variables. -/
def Ex0.poly (v : ℕ) (p : Ex0 X E) : Poly0 X E :=
  ⟨v, Ex.na p, Ex.atomAt (.cell fun _ => cK 0) p, Ex.terms p⟩

/-- the sum over w further variables of an expression on v + w variables -/
def sumA (v w : ℕ) (p : Ex0 X E) : Ex1 X E := Ex.one (.sum w (Ex0.poly (v + w) p))

/-- The compiled family, on v variables. -/
def Ex1.fam (v : ℕ) (p : Ex1 X E) : Fam X E :=
  ⟨v, Ex.na p, Ex.atomAt (.base (.cell fun _ => cK 0)) p, Ex.terms p⟩

variable (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

/-- the value of an expression of the lower level at a vertex of v variables -/
def Ex0.val (p : Ex0 X E) (v b : ℕ) : E := Ex.ev p (fun a => a.val Φ v W A b) x b
/-- the value of an expression at a vertex of v variables -/
def Ex1.val (p : Ex1 X E) (v b : ℕ) : E := Ex.ev p (fun a => a.val Φ v x W A b) x b

theorem poly_val (v : ℕ) (p : Ex0 X E) (b : ℕ) :
    (Ex0.poly v p).val Φ x W A b = Ex0.val Φ x W A p v b :=
  Ex.ev_compiled (fun a : Atom0 E => a.val Φ v W A b) x b _ p

/-- The value of the compiled family is the value of the expression. -/
theorem fam_val (v : ℕ) (p : Ex1 X E) (b : ℕ) :
    (Ex1.fam v p).val Φ x W A b = Ex1.val Φ x W A p v b :=
  Ex.ev_compiled (fun a : Atom X E => a.val Φ v x W A b) x b _ p

/-- the value of a sum atom -/
theorem val_sum (v w : ℕ) (p : Ex0 X E) (b : ℕ) :
    (Atom.sum w (Ex0.poly (v + w) p) : Atom X E).val Φ v x W A b =
      ∑ j ∈ range (2 ^ w), Ex0.val Φ x W A p (v + w) (b * 2 ^ w + j) :=
  sum_congr rfl fun _ _ => poly_val Φ x W A (v + w) p _

theorem poly_wf {v : ℕ} {p : Ex0 X E} (h : Ex.All (fun a => a.WF Φ v) p) : (Ex0.poly v p).WF Φ :=
  ⟨Ex.terms_lt p, Ex.atomAt_all _ h⟩

theorem fam_wf {v : ℕ} {p : Ex1 X E} (h : Ex.All (fun a => a.WF Φ v) p) : (Ex1.fam v p).WF Φ :=
  ⟨Ex.terms_lt p, Ex.atomAt_all _ h⟩

theorem poly_places {v : ℕ} {p : Ex0 X E} {P : Cb.Place → Prop}
    (h : Ex.All (fun a => ∀ q ∈ a.places v, P q) p) :
    ∀ q ∈ (Ex0.poly v p).places, P q := by
  rintro q ⟨j, hj, hq⟩
  exact Ex.atomAt_all _ h j hj q hq

theorem fam_places {v : ℕ} {p : Ex1 X E} {P : Cb.Place → Prop}
    (h : Ex.All (fun a => ∀ q ∈ a.places v, P q) p) :
    ∀ q ∈ (Ex1.fam v p).places, P q := by
  rintro q ⟨j, hj, hq⟩
  exact Ex.atomAt_all _ h j hj q hq

/-! the atoms' own rules -/

theorem wf_cell0 (v : ℕ) (f : ℕ → CForm E) : (Atom0.cell f).WF Φ v := trivial
theorem wf_cell (v : ℕ) (f : ℕ → CForm E) : (Atom.base (.cell f) : Atom X E).WF Φ v := trivial
theorem wf_sum {v w : ℕ} {p : Ex0 X E} (h : Ex.All (fun a => a.WF Φ (v + w)) p) :
    (Atom.sum w (Ex0.poly (v + w) p) : Atom X E).WF Φ v :=
  ⟨rfl, poly_wf Φ h⟩

theorem places_cell0 {v : ℕ} {f : ℕ → CForm E}
    {P : Cb.Place → Prop} (h : ∀ b < 2 ^ v, AllPl P (f b)) :
    ∀ q ∈ (Atom0.cell f).places v, P q := by
  rintro q ⟨b, hb, t, ht, rfl⟩
  exact h b hb _ (List.mem_map_of_mem ht)
theorem places_idx0 (v : ℕ) (a : IdxAtom E) {P : Cb.Place → Prop} :
    ∀ q ∈ (Atom0.idx a).places v, P q :=
  fun _ h => absurd h (Set.notMem_empty _)

/-! ### Values, operation by operation (marked simp) -/

section ValRules
open Ex
variable (v b : ℕ)

@[simp] theorem val0_aff (f : ℕ → CForm E) : Ex0.val Φ x W A (aff0 f) v b = (f b).val A := by
  simp [Ex0.val, aff0, Atom0.val]
@[simp] theorem val0_idx (a : IdxAtom E) : Ex0.val Φ x W A (idx0 a) v b = a.at Φ W (vtx v b) := by
  simp [Ex0.val, idx0, Atom0.val]
@[simp] theorem val0_zero : Ex0.val Φ x W A Ex.zero v b = 0 := rfl
@[simp] theorem val0_pub (c : X → ℕ → E) : Ex0.val Φ x W A (Ex.pub c) v b = c x b := by
  simp [Ex0.val]
@[simp] theorem val0_con (k : E) : Ex0.val Φ x W A (Ex.con k) v b = k := by simp [Ex0.val]
@[simp] theorem val0_add (p q : Ex0 X E) :
    Ex0.val Φ x W A (p + q) v b = Ex0.val Φ x W A p v b + Ex0.val Φ x W A q v b := by simp [Ex0.val]
@[simp] theorem val0_sub (p q : Ex0 X E) :
    Ex0.val Φ x W A (p - q) v b = Ex0.val Φ x W A p v b - Ex0.val Φ x W A q v b := by simp [Ex0.val]
@[simp] theorem val0_mul (p q : Ex0 X E) :
    Ex0.val Φ x W A (p * q) v b = Ex0.val Φ x W A p v b * Ex0.val Φ x W A q v b := by simp [Ex0.val]
@[simp] theorem val0_sc (c : X → ℕ → E) (p : Ex0 X E) :
    Ex0.val Φ x W A (Ex.sc c p) v b = c x b * Ex0.val Φ x W A p v b := by simp [Ex0.val]
@[simp] theorem val0_smul (k : E) (p : Ex0 X E) :
    Ex0.val Φ x W A (k • p) v b = k * Ex0.val Φ x W A p v b := by simp [Ex0.val]
@[simp] theorem val0_pSum (n : ℕ) (f : ℕ → Ex0 X E) :
    Ex0.val Φ x W A (Ex.pSum n f) v b = ∑ k ∈ range n, Ex0.val Φ x W A (f k) v b := by
  simp [Ex0.val]
@[simp] theorem val0_ite (c : Prop) [Decidable c] (p q : Ex0 X E) :
    Ex0.val Φ x W A (if c then p else q) v b =
      if c then Ex0.val Φ x W A p v b else Ex0.val Φ x W A q v b := by split_ifs <;> rfl

@[simp] theorem val1_aff (f : ℕ → CForm E) : Ex1.val Φ x W A (aff f) v b = (f b).val A := by
  simp [Ex1.val, aff, Atom.val, Atom0.val]
@[simp] theorem val1_idx (a : IdxAtom E) : Ex1.val Φ x W A (idx a) v b = a.at Φ W (vtx v b) := by
  simp [Ex1.val, idx, Atom.val, Atom0.val]
@[simp] theorem val1_sumA (w : ℕ) (p : Ex0 X E) :
    Ex1.val Φ x W A (sumA v w p) v b =
      ∑ j ∈ range (2 ^ w), Ex0.val Φ x W A p (v + w) (b * 2 ^ w + j) := by
  rw [← val_sum]
  simp [Ex1.val, sumA]
@[simp] theorem val1_zero : Ex1.val Φ x W A Ex.zero v b = 0 := rfl
@[simp] theorem val1_pub (c : X → ℕ → E) : Ex1.val Φ x W A (Ex.pub c) v b = c x b := by
  simp [Ex1.val]
@[simp] theorem val1_con (k : E) : Ex1.val Φ x W A (Ex.con k) v b = k := by simp [Ex1.val]
@[simp] theorem val1_add (p q : Ex1 X E) :
    Ex1.val Φ x W A (p + q) v b = Ex1.val Φ x W A p v b + Ex1.val Φ x W A q v b := by simp [Ex1.val]
@[simp] theorem val1_sub (p q : Ex1 X E) :
    Ex1.val Φ x W A (p - q) v b = Ex1.val Φ x W A p v b - Ex1.val Φ x W A q v b := by simp [Ex1.val]
@[simp] theorem val1_mul (p q : Ex1 X E) :
    Ex1.val Φ x W A (p * q) v b = Ex1.val Φ x W A p v b * Ex1.val Φ x W A q v b := by simp [Ex1.val]
@[simp] theorem val1_sc (c : X → ℕ → E) (p : Ex1 X E) :
    Ex1.val Φ x W A (Ex.sc c p) v b = c x b * Ex1.val Φ x W A p v b := by simp [Ex1.val]
@[simp] theorem val1_smul (k : E) (p : Ex1 X E) :
    Ex1.val Φ x W A (k • p) v b = k * Ex1.val Φ x W A p v b := by simp [Ex1.val]
@[simp] theorem val1_pSum (n : ℕ) (f : ℕ → Ex1 X E) :
    Ex1.val Φ x W A (Ex.pSum n f) v b = ∑ k ∈ range n, Ex1.val Φ x W A (f k) v b := by
  simp [Ex1.val]
@[simp] theorem val1_ite (c : Prop) [Decidable c] (p q : Ex1 X E) :
    Ex1.val Φ x W A (if c then p else q) v b =
      if c then Ex1.val Φ x W A p v b else Ex1.val Φ x W A q v b := by split_ifs <;> rfl

end ValRules

/-! ### Well-formedness and places, as properties of expressions

The rules for +, -, *, `Ex.sc`, •, pSum, ite, pub, con, zero are `Ex.All.add`, .sub, .. -/

/-- every atom of the expression is well formed on v variables -/
abbrev WF0 (v : ℕ) (p : Ex0 X E) : Prop := Ex.All (fun a => a.WF Φ v) p
abbrev WF1 (v : ℕ) (p : Ex1 X E) : Prop := Ex.All (fun a => a.WF Φ v) p
/-- every place that the expression reads has the property P -/
abbrev Pl0 (P : Cb.Place → Prop) (v : ℕ) (p : Ex0 X E) : Prop :=
  Ex.All (fun a => ∀ q ∈ a.places v, P q) p
abbrev Pl1 (P : Cb.Place → Prop) (v : ℕ) (p : Ex1 X E) : Prop :=
  Ex.All (fun a => ∀ q ∈ a.places v, P q) p

theorem WF0.aff (v : ℕ) (f : ℕ → CForm E) : WF0 (X := X) Φ v (aff0 f) := Ex.All.one trivial
theorem WF0.idx {v : ℕ} {a : IdxAtom E} (h : a.OK Φ v) : WF0 (X := X) Φ v (idx0 a) := Ex.All.one h
theorem WF1.aff (v : ℕ) (f : ℕ → CForm E) : WF1 (X := X) Φ v (aff f) := Ex.All.one trivial
theorem WF1.idx {v : ℕ} {a : IdxAtom E} (h : a.OK Φ v) : WF1 (X := X) Φ v (Seg.idx a) :=
  Ex.All.one h
theorem WF1.sumA {v w : ℕ} {p : Ex0 X E} (h : WF0 Φ (v + w) p) : WF1 Φ v (sumA v w p) :=
  Ex.All.one (wf_sum Φ h)

variable {P : Cb.Place → Prop}
theorem Pl0.aff {v : ℕ} {f : ℕ → CForm E} (h : ∀ b < 2 ^ v, AllPl P (f b)) :
    Pl0 (X := X) P v (aff0 f) :=
  Ex.All.one (places_cell0 h)
theorem Pl0.idx (v : ℕ) (a : IdxAtom E) : Pl0 (X := X) P v (idx0 a) := Ex.All.one (places_idx0 v a)
theorem Pl1.aff {v : ℕ} {f : ℕ → CForm E} (h : ∀ b < 2 ^ v, AllPl P (f b)) :
    Pl1 (X := X) P v (Seg.aff f) :=
  Ex.All.one (places_cell0 h)
theorem Pl1.idx (v : ℕ) (a : IdxAtom E) : Pl1 (X := X) P v (Seg.idx a) :=
  Ex.All.one (places_idx0 v a)
theorem Pl1.sumA {v w : ℕ} {p : Ex0 X E} (h : Pl0 P (v + w) p) : Pl1 P v (sumA v w p) :=
  Ex.All.one (poly_places h)

end Levels

end Cm.Seg
