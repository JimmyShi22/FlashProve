-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqGlue.lean: several families of conditions as one.

On constraint systems over Boolean cubes: several of them are joined into one on a larger cube, by
selector variables. A family (`Fam`, Cb/Req/ReqSpec.lean) gives one value at each vertex b < 2^v of
a cube.
Definitions and statements; the proofs are in Cb/Req/ReqGlueProofs*.lean. No protocol.

Why: a segment of Cb/Req/ReqSpec.lean has a list of families of identities (one zerocheck each) and
a list of families of keys (one lookup each). A print of this protocol's technical report
(lean/CREDITS.md) has ONE polynomial map for the identities of a segment and ONE key map for each
table.
Under the hypotheses below:
Here: a combinator that glues a list of families into one, and with it the GLUED FORM of a segment,
which has the paper's counts and the same conditions.


The glued family of L = [f_0, .., f_(n-1)], f_i on v_i variables. Variables: s selector variables in
front (s the least number with n ≤ 2^s), then V = max v_i variables. The vertex i · 2^V + b' carries
family i at b' if i < n and b' < 2^(v_i): such a vertex is live. All other vertices are dead; there
the glued family has the value "pad": 0 for identities, an element of the table for keys
(`Spec.glue_val`, under its hypotheses).

Main names. How the glued family is made, in four steps, each with its laws (those of `Fam.mask`,
`Fam.pub`, `Fam.add`: Cb/Req/ReqGlueProofs.lean):
  `Fam.to N f`: the family on more variables (N ≥ v): it reads the low v bits of a vertex. An index
    atom reads the point's last v coordinates (it is constant in the others, and keeps its law
    `IdxAtom.OK`).
  `Fam.mask c f`: every coefficient table is multiplied by a public table c.
  `Fam.pub v c`: the family without atoms whose value is the public table c.
  `Fam.add f g`: two families on the same variables side by side; the value is the sum (`add_val`,
    Cb/Req/ReqGlueProofs.lean, under its hypotheses).
  `Fam.glue pad L` = pub (pad at dead vertices) + ∑_i mask (indicator of "selector i, and live") (to
    N f_i), where + and ∑ are `Fam.add` and N = s + V.
The glued segment:
  `SegSpec.glued`: one family of identities; for each table that occurs, one family of keys: the
    families with this table, glued, with the table's first element at dead vertices. (Which tables
    are equal is decided classically: Lean models no running time.)
Statements:
  `Spec.glue_val`, `Spec.glue_zero_iff`, `Spec.glue_key_iff`, `Spec.glued_holds_iff`,
    `Spec.glued_counts`: see their docstrings.

Limits: this file says nothing on degrees or on the cost of the public tables (Lean models no
running time). The glued family has s + V variables, so its cube may be larger than the sum of the
families' cubes.
The notion follows a convention of a print of this protocol's technical report
(lean/CREDITS.md).

Terms: lean/GLOSSARY.md: atom, conditions (of a segment), family, key, live vertex, segment, table.
-/
import Cb.Req.ReqSpec
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

section Defs
variable {X E : Type}

/-- The point, read from coordinate k on. -/
def shiftPt (k : ℕ) (pt : ℕ → E) : ℕ → E := fun t => pt (k + t)

/-- An index atom that skips the first k coordinates of the point. -/
def IdxAtom.up (k : ℕ) (a : IdxAtom E) : IdxAtom E :=
  ⟨fun pt => a.g (shiftPt k pt), fun pt => a.ψ (shiftPt k pt)⟩

/-- An atom on v variables, on N ≥ v variables: it reads the low v bits of a vertex. -/
def Atom0.to (N v : ℕ) : Atom0 E → Atom0 E
  | .cell f => .cell fun b => f (b % 2 ^ v)
  | .idx a => .idx (a.up (N - v))

/-- A term whose coefficient table reads the low v bits of a vertex. -/
def Term.low (v : ℕ) (t : Term X E) : Term X E := ⟨fun x b => t.coef x (b % 2 ^ v), t.atoms⟩

def Poly0.to (N : ℕ) (P : Poly0 X E) : Poly0 X E :=
  ⟨N, P.na, fun j => (P.atom j).to N P.v, P.terms.map (Term.low P.v)⟩

def Atom.to (N v : ℕ) : Atom X E → Atom X E
  | .base a => .base (a.to N v)
  | .sum w P => .sum w (P.to (N + w))

/-- A family on more variables: it reads the low bits of a vertex. -/
def Fam.to (N : ℕ) (f : Fam X E) : Fam X E :=
  ⟨N, f.na, fun j => (f.atom j).to N f.v, f.terms.map (Term.low f.v)⟩

/-- Every coefficient table is multiplied by the public table c. -/
def Fam.mask [Mul E] (c : X → ℕ → E) (f : Fam X E) : Fam X E :=
  ⟨f.v, f.na, f.atom, f.terms.map fun t => ⟨fun x b => c x b * t.coef x b, t.atoms⟩⟩

/-- The family without atoms whose value is the public table c. -/
def Fam.pub [Zero E] (v : ℕ) (c : X → ℕ → E) : Fam X E :=
  ⟨v, 0, fun _ => .base (.cell fun _ => ⟨0, []⟩), [⟨c, []⟩]⟩

/-- Two families side by side: the atoms of the second are renumbered behind those of the first. -/
def Fam.add (f g : Fam X E) : Fam X E :=
  ⟨f.v, f.na + g.na,
    fun n => if n < f.na then f.atom n else g.atom (n - f.na),
    f.terms ++ g.terms.map fun t => ⟨t.coef, t.atoms.map (· + f.na)⟩⟩

/-- The largest number of variables. -/
def maxV (L : List (Fam X E)) : ℕ := (L.map (·.v)).foldr max 0

/-- The number of variables of the glued family: selector variables, then maxV. -/
def glueN (L : List (Fam X E)) : ℕ := Nat.clog 2 L.length + maxV L

/-- Is the vertex live: its selector value names a family, and the rest is a vertex of that family.
-/
def liveAt (V : ℕ) (L : List (Fam X E)) (b : ℕ) : Bool :=
  match L[b / 2 ^ V]? with
  | some f => decide (b % 2 ^ V < 2 ^ f.v)
  | none => false

/-- The families from number i on, each at its selector value. -/
def glueFrom [Zero E] [One E] [Mul E] (N V : ℕ) : ℕ → List (Fam X E) → Fam X E
  | _, [] => Fam.pub N fun _ _ => 0
  | i, f :: L =>
    Fam.add (Fam.mask (fun _ b => if b / 2 ^ V = i ∧ b % 2 ^ V < 2 ^ f.v then 1 else 0) (f.to N))
      (glueFrom N V (i + 1) L)

/-- Several families as one; pad is the value at dead vertices. -/
def Fam.glue [Zero E] [One E] [Mul E] (pad : E) (L : List (Fam X E)) : Fam X E :=
  Fam.add (Fam.pub (glueN L) fun _ b => if liveAt (maxV L) L b then 0 else pad)
    (glueFrom (glueN L) (maxV L) 0 L)

/-- What the value of the glued family is to be, given the values of the families. -/
def glueVal (V : ℕ) (L : List (Fam X E)) (val : Fam X E → ℕ → E) (pad : E) (b : ℕ) : E :=
  match L[b / 2 ^ V]? with
  | some f => if b % 2 ^ V < 2 ^ f.v then val f (b % 2 ^ V) else pad
  | none => pad

end Defs

open Classical in
/-- The glued form of a segment: one family of identities; one family of keys for each table. -/
def SegSpec.glued
    {X F E : Type} [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) : SegSpec X F E where
  rowsLog := S.rowsLog
  cols := S.cols
  idn := [Fam.glue 0 S.idn]
  keys := (S.keys.map (·.2)).dedup.map fun T =>
    (Fam.glue (algebraMap F E (T.t 0)) ((S.keys.filter fun k => decide (k.2 = T)).map (·.1)), T)

namespace Spec

def vtx_shift : Prop :=
  ∀ (E : Type) [Zero E] [One E] (N v b : ℕ),
    v ≤ N → shiftPt (N - v) (vtx (E := E) N b) = vtx v (b % 2 ^ v)

def ext_low : Prop :=
  ∀ (E : Type) [Field E] (N v : ℕ) (h : ℕ → E) (pt : ℕ → E),
    v ≤ N → ext N (fun b => h (b % 2 ^ v)) pt = ext v h (shiftPt (N - v) pt)

def to_val : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (f : Fam X E) (Φ : IdxFmt F) (N : ℕ) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    f.WF Φ → f.v ≤ N → ∀ b, (f.to N).val Φ x W A b = f.val Φ x W A (b % 2 ^ f.v)

def to_wf : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (f : Fam X E) (Φ : IdxFmt F) (N : ℕ),
    f.WF Φ → f.v ≤ N → (f.to N).WF Φ

def to_places : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (f : Fam X E) (Φ : IdxFmt F) (N : ℕ),
    f.WF Φ → f.v ≤ N → (f.to N).places = f.places

/-- States: if every family of L is well formed, `glueVal` is the value of the glued family, at
every vertex number. -/
def glue_val : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (pad : E) (Φ : IdxFmt F)
      (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, f.WF Φ) →
    ∀ b, (Fam.glue pad L).val Φ x W A b = glueVal (maxV L) L (fun f b' => f.val Φ x W A b') pad b

def glue_wf : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (pad : E) (Φ : IdxFmt F),
    (∀ f ∈ L, f.WF Φ) → (Fam.glue pad L).WF Φ

def glue_places : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (pad : E) (Φ : IdxFmt F),
    (∀ f ∈ L, f.WF Φ) → ∀ p, p ∈ (Fam.glue pad L).places ↔ ∃ f ∈ L, p ∈ f.places

/-- States: if every family of L is well formed, the glued family (pad: 0) vanishes on its cube iff
all families vanish on theirs. -/
def glue_zero_iff : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, f.WF Φ) →
    ((∀ b < 2 ^ (Fam.glue (0 : E) L).v, (Fam.glue 0 L).val Φ x W A b = 0) ↔
      ∀ f ∈ L, ∀ b < 2 ^ f.v, f.val Φ x W A b = 0)

/-- States: if every family of L is well formed, all keys of the glued family (pad: the table's
first element) lie in the table iff all keys of all families do. -/
def glue_key_iff : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (T : Tab F) (Φ : IdxFmt F)
      (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, f.WF Φ) →
    ((∀ b < 2 ^ (Fam.glue (algebraMap F E (T.t 0)) L).v,
        ∃ u ∈ T.set, (Fam.glue (algebraMap F E (T.t 0)) L).val Φ x W A b = algebraMap F E u) ↔
      ∀ f ∈ L, ∀ b < 2 ^ f.v, ∃ u ∈ T.set, f.val Φ x W A b = algebraMap F E u)

/-- States: if `S.WF Φ`, the glued segment has the same conditions. -/
def glued_holds_iff : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (Φ : IdxFmt F) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    S.WF Φ → (S.glued.Holds Φ x W A ↔ S.Holds Φ x W A)

def glued_wf : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (Φ : IdxFmt F),
    S.WF Φ → S.glued.WF Φ

def glued_places : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (Φ : IdxFmt F),
    S.WF Φ → S.glued.places = S.places

/-- **The paper's counts**: one family of identities; no table twice; the tables are those of the
segment. -/
def glued_counts : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E),
    S.glued.idn.length = 1 ∧
    (S.glued.keys.map (·.2)).Nodup ∧
    ∀ T, T ∈ S.glued.keys.map (·.2) ↔ T ∈ S.keys.map (·.2)

end Spec
end Cb
