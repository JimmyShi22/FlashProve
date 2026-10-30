-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatShape.lean: book-keeping on interleaved codes inside a proximity test: reductions without
messages that add rows which nobody sends (zero rows, copies of a row) or rename coordinates.

Definitions and statements; the proofs are in Cb/Ld/LdBatShapeProofs.lean.

Why: after the batching (Cb/Ld/LdBatSig.lean) a test is left with the main relation of
Cb/Ld/LdRel.lean for the words as they were sent. A fold needs rows named by the corners of a cube.
The rows that are missing are virtual: nobody sends them; the verifier computes their symbols: zero,
or a copy of a row that was sent.
The list and the exceptional sets of the fold are then those of the full interleaving. That the two
arrangements say the same has to be shown for the existential relaxation: a codeword of the full
interleaving that is close to an arranged word might have something else in a virtual row. It has
not, if the joint radius is below the distance (`Spec.ldShape_arr_fix`, under the hypotheses of its
statement).

In standard terms: a code (`LdCode`, Cb/Ld/LdRel.lean) is read under a transformation: the encoder
takes a message and randomness to a native word; the transformation `C.T` takes a native word to a
long word, with a symbol at each long position; distance counts long positions. `C.il R` is the
interleaved code: one codeword of C for each row name in R, a symbol holding one entry of each row
(`LdCode.il`, Cb/Ld/LdRel.lean). In the main relation `C.rels s e` (`LdCode.rels`, same file) the
statement is (target, state) with a native word, and the witness a pair (message, randomness).
Exactly, the word is the pair's encoding and the form s, at the state, takes the value target on the
message. Relaxed (the existential relaxation), the encoding is within e long positions of the word,
and the form takes that value.

Main names:
  1. `Reshape C C'`, for two codes read at the same long positions (`LdCode`): data (wd, up, dn,
    fm). `ρ.Laws`: its six laws.
  `ρ.Fix e`: the only clause that reads a radius. It is not needed for a chain (the extractor dn
    cuts the witness back: it is no farther from the word and the form has the same value); it is
    what makes the two relations one relation up to a bijection of witnesses.
  Operations: `Reshape.refl`, `Reshape.comp`, `Reshape.fam`, `ρ.pairL D`, `ρ.pairR D` (beside a code
    D that is not touched: the joint radius is kept because off is pointwise).
  2. Virtual rows: `Arr R R'`, `a.OK`, `a.reshape C` (from `C.il R` to `C.il R'`).
  3. Renamings of coordinates: `Reshape.gather Rm Rz Cb Zb`, `Reshape.curry C R₁ R₂`.
The statements:
  `Spec.ldShape_step`, `Spec.ldShape_piece`: under `ρ.Laws`: a step without rounds, a piece of a
    chain (`IOR.PieceTr`, so `IOR.GoodT`), from `C.rels s e` to `C'.rels (ρ.sl s) e`, the same
    radius, any radius, no error, extractor dn.
  `Spec.ldShape_same`: under `ρ.Laws` and `ρ.Fix e`: one relation up to a bijection of witnesses.
  `Spec.ldShape_list`: under `ρ.Laws`: a bound on the list of the new code bounds the list of the
    old.
  `Spec.ldShape_refl`, `Spec.ldShape_comp`, `Spec.ldShape_fam`, `Spec.ldShape_pairL`,
    `Spec.ldShape_pairR`: the operations keep the laws and, under the laws, `Fix e`.
  `Spec.ldShape_arr`: `a.OK` and the laws of C (Cb/Ld/LdRel.lean): `(a.reshape C).Laws`.
  `Spec.ldShape_arr_fix`, the lemma on virtual rows: moreover C has the distance d under its
    transformation and e < d: `(a.reshape C).Fix e`.
  `Spec.ldShape_two`: main rows and mask rows at once: from `(C.il R).pair (Z.il Rz)` to
    `(C.il R').pair (Z.il Rz')`: under the laws of C and Z, `a.OK` and `az.OK`: the laws; `Fix e` if
    both distances are above e.
  `Spec.ldShape_gather`, `Spec.ldShape_curry`: the two renamings have the laws, and `Fix` at every
    radius.

Why e < d: two rows of a codeword that are in copies of one row both agree with that row outside the
at most e positions at which the joint words differ; so they agree with each other there, and their
difference is a codeword of C of weight at most e: zero. The same gives zero in a zero row.

Limits: this file does not say how the code of an oracle message as it was declared is tied to the
form "main rows under Cb beside mask rows under Zb, at the group's positions". Nothing on native
positions, so nothing on zero knowledge of encodings: no word is sent here. Nothing on running
times.
The lemma follows this protocol's technical report; so do the main relation and its relaxation, for
which that report follows the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel
import Cb.Ld.LdTowerKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-! ## 1. A code in another shape -/

/-- From C to C', at the same long positions: the data. -/
structure Reshape {E P : Type} (C C' : LdCode E P) where
  /-- native words: what the verifier computes -/
  wd : C.Word → C'.Word
  /-- pairs (message, randomness), forth and back -/
  up : (C.J → E) × (C.Q → E) → (C'.J → E) × (C'.Q → E)
  dn : (C'.J → E) × (C'.Q → E) → (C.J → E) × (C.Q → E)
  /-- the coefficients of a form on messages -/
  fm : (C.J → E) → C'.J → E

namespace Reshape
variable {E P : Type} {C C' C'' : LdCode E P}

/-- The laws. loc: a long symbol of the new word is computed from the long symbol of the old word at
the same position; enc: the new word of an encoding is the encoding of up; off: pointwise: where the
new word agrees with the encoding of w', the old word agrees with the encoding of dn w'; inj: dn
undoes up; winj: different words have different new words; val: the carried form at any w' is the
form at dn w'. -/
structure Laws [Field E] (ρ : Reshape C C') : Prop where
  loc : ∀ f g x, C.T f x = C.T g x → C'.T (ρ.wd f) x = C'.T (ρ.wd g) x
  enc : ∀ w, ρ.wd (C.enc w.1 w.2) = C'.enc (ρ.up w).1 (ρ.up w).2
  off : ∀ f w' x,
    C'.T (ρ.wd f) x = C'.T (C'.enc w'.1 w'.2) x → C.T f x = C.T (C.enc (ρ.dn w').1 (ρ.dn w').2) x
  inj : ∀ w, ρ.dn (ρ.up w) = w
  winj : ∀ f g, ρ.wd f = ρ.wd g → f = g
  val : ∀ a w', ∑ j, ρ.fm a j * w'.1 j = ∑ j, a j * (ρ.dn w').1 j

/-- A codeword within e of a new word is of the new shape. -/
def Fix [Field E] [Finite P] (ρ : Reshape C C') (e : ℕ) : Prop :=
  ∀ f w', C'.Near e (ρ.wd f) (C'.enc w'.1 w'.2) → ρ.up (ρ.dn w') = w'

/-- the map on the implicit parts of statements: a query at x costs one query at x -/
def map (ρ : Reshape C C') : ExtMap C.ext C'.ext := ⟨ρ.wd, fun x => {x}⟩

/-- the carried form; the state stays -/
def sl {St : Type} (ρ : Reshape C C') (s : Slf E St C.J) : Slf E St C'.J := fun st => ρ.fm (s st)

/-- nothing changes -/
def refl (C : LdCode E P) : Reshape C C := ⟨fun f => f, fun w => w, fun w => w, fun a => a⟩

/-- the part of a pair (message, randomness) of a family that belongs to the member a -/
def atP {A : Type} [Fintype A] [DecidableEq A] {D : A → LdCode E P}
    (w : ((LdCode.fam D).J → E) × ((LdCode.fam D).Q → E)) (a : A) : ((D a).J → E) × ((D a).Q → E) :=
  (fun j => w.1 ⟨a, j⟩, fun q => w.2 ⟨a, q⟩)

/-- A family, member by member. -/
def fam {A : Type} [Fintype A] [DecidableEq A]
    {D D' : A → LdCode E P} (ρ : ∀ a, Reshape (D a) (D' a)) :
    Reshape (LdCode.fam D) (LdCode.fam D') where
  wd := fun f p => (ρ p.1).wd (fun p' => f ⟨p.1, p'⟩) p.2
  up := fun w => (fun j => ((ρ j.1).up (atP w j.1)).1 j.2, fun q => ((ρ q.1).up (atP w q.1)).2 q.2)
  dn := fun w => (fun j => ((ρ j.1).dn (atP w j.1)).1 j.2, fun q => ((ρ q.1).dn (atP w q.1)).2 q.2)
  fm := fun a j => (ρ j.1).fm (fun j' => a ⟨j.1, j'⟩) j.2

/-- one after the other -/
def comp (ρ' : Reshape C' C'') (ρ : Reshape C C') : Reshape C C'' :=
  ⟨fun f => ρ'.wd (ρ.wd f), fun w => ρ'.up (ρ.up w),
    fun w => ρ.dn (ρ'.dn w), fun a => ρ'.fm (ρ.fm a)⟩

/-- the two sides of a pair (message, randomness) of two codes side by side, and back -/
def fstP {C₁ C₂ : LdCode E P} (w : ((C₁.pair C₂).J → E) × ((C₁.pair C₂).Q → E)) :
    (C₁.J → E) × (C₁.Q → E) :=
  (fun j => w.1 (.inl j), fun q => w.2 (.inl q))
def sndP {C₁ C₂ : LdCode E P} (w : ((C₁.pair C₂).J → E) × ((C₁.pair C₂).Q → E)) :
    (C₂.J → E) × (C₂.Q → E) :=
  (fun j => w.1 (.inr j), fun q => w.2 (.inr q))
def mkP {C₁ C₂ : LdCode E P} (w₁ : (C₁.J → E) × (C₁.Q → E)) (w₂ : (C₂.J → E) × (C₂.Q → E)) :
    ((C₁.pair C₂).J → E) × ((C₁.pair C₂).Q → E) :=
  (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 w₂.2)

/-- Beside a code that is not touched, on the right and on the left. -/
def pairL (ρ : Reshape C C') (D : LdCode E P) : Reshape (C.pair D) (C'.pair D) where
  wd := fun f => LdCode.mkW (ρ.wd (LdCode.fstW f)) (LdCode.sndW f)
  up := fun w => mkP (ρ.up (fstP w)) (sndP w)
  dn := fun w => mkP (ρ.dn (fstP w)) (sndP w)
  fm := fun a => Sum.elim (ρ.fm fun j => a (.inl j)) fun j => a (.inr j)

def pairR (ρ : Reshape C C') (D : LdCode E P) : Reshape (D.pair C) (D.pair C') where
  wd := fun f => LdCode.mkW (LdCode.fstW f) (ρ.wd (LdCode.sndW f))
  up := fun w => mkP (fstP w) (ρ.up (sndP w))
  dn := fun w => mkP (fstP w) (ρ.dn (sndP w))
  fm := fun a => Sum.elim (fun j => a (.inl j)) (ρ.fm fun j => a (.inr j))

end Reshape

/-! ## 2. Virtual rows -/

/-- An arrangement of rows: the data. -/
structure Arr (R R' : Type) where
  /-- what is in a new row: none = zero; some r = a copy of the row r -/
  src : R' → Option R
  /-- the copy on which a form's coefficients on the row r are placed -/
  rep : R → R'

namespace Arr
variable {R R' X E : Type} (a : Arr R R')

/-- rep r is a copy of r -/
def OK : Prop := ∀ r, a.src (a.rep r) = some r

/-- a vector with coordinates (row, place), arranged -/
def spread [Zero E] (v : R × X → E) : R' × X → E := fun n => match a.src n.1 with
  | some r => v (r, n.2)
  | none => 0

/-- cut back: the rows rep r -/
def pick (v : R' × X → E) : R × X → E := fun n => v (a.rep n.1, n.2)

/-- the coefficients of a form: if `a.OK`, on rep r those on r, zeros elsewhere -/
def place [Zero E] [DecidableEq R'] (c : R × X → E) : R' × X → E := fun n => match a.src n.1 with
  | some r => if a.rep r = n.1 then c (r, n.2) else 0
  | none => 0

/-- The interleaving with rows R, brought to rows R'. -/
def reshape [Zero E] {P : Type} [Fintype R] [DecidableEq R] [Fintype R']
    [DecidableEq R'] (C : LdCode E P) : Reshape (C.il R) (C.il R') where
  wd := fun f p => a.spread (f p)
  up := fun w => (a.spread w.1, a.spread w.2)
  dn := fun w => (a.pick w.1, a.pick w.2)
  fm := a.place

end Arr

/-! ## 3. Renamings of coordinates -/

section
variable {A : Type} (Rm Rz : A → Type)

/-- (member, row) with a place, main or mask  ≃  member with (row, place), main or mask -/
def gatE (X Y : Type) : ((Σ a, Rm a) × X) ⊕ ((Σ a, Rz a) × Y) ≃ Σ a, (Rm a × X) ⊕ (Rz a × Y) where
  toFun := fun n => match n with
    | .inl n => ⟨n.1.1, .inl (n.1.2, n.2)⟩
    | .inr n => ⟨n.1.1, .inr (n.1.2, n.2)⟩
  invFun := fun n => match n.2 with
    | .inl s => .inl (⟨n.1, s.1⟩, s.2)
    | .inr s => .inr (⟨n.1, s.1⟩, s.2)
  left_inv := fun n => by rcases n with ⟨⟨a, i⟩, x⟩ | ⟨⟨a, i⟩, x⟩ <;> rfl
  right_inv := fun n => by rcases n with ⟨a, ⟨i, x⟩ | ⟨i, x⟩⟩ <;> rfl

variable {E P : Type} [Fintype A] [DecidableEq A] [∀ a, Fintype (Rm a)] [∀ a, DecidableEq (Rm a)]
  [∀ a, Fintype (Rz a)] [∀ a, DecidableEq (Rz a)]

/-- Members side by side, each with main rows under Cb and mask rows under Zb → all main rows under
Cb beside all mask rows under Zb (rows named by (member, row)). -/
def Reshape.gather (Cb Zb : LdCode E P) :
    Reshape (LdCode.fam fun a => (Cb.il (Rm a)).pair (Zb.il (Rz a)))
      ((Cb.il (Σ a, Rm a)).pair (Zb.il (Σ a, Rz a))) where
  wd := fun f p => match p with
    | .inl p => fun s => f ⟨s.1.1, .inl p⟩ (s.1.2, s.2)
    | .inr p => fun s => f ⟨s.1.1, .inr p⟩ (s.1.2, s.2)
  up := fun w => (fun j => w.1 (gatE Rm Rz Cb.J Zb.J j), fun q => w.2 (gatE Rm Rz Cb.Q Zb.Q q))
  dn := fun w =>
    (fun j => w.1 ((gatE Rm Rz Cb.J Zb.J).symm j), fun q => w.2 ((gatE Rm Rz Cb.Q Zb.Q).symm q))
  fm := fun a j => a (gatE Rm Rz Cb.J Zb.J j)

end

/-- Rows named by pairs → rows of rows (an interleaving of an interleaving). -/
def Reshape.curry {E P : Type} (C : LdCode E P) (R₁ R₂ : Type) [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] :
    Reshape (C.il (R₁ × R₂)) ((C.il R₂).il R₁) where
  wd := fun f p s => f p ((s.1, s.2.1), s.2.2)
  up := fun w => (fun j => w.1 ((j.1, j.2.1), j.2.2), fun q => w.2 ((q.1, q.2.1), q.2.2))
  dn := fun w => (fun j => w.1 (j.1.1, (j.1.2, j.2)), fun q => w.2 (q.1.1, (q.1.2, q.2)))
  fm := fun a j => a ((j.1, j.2.1), j.2.2)

/-! ## The statements -/

namespace Spec
open IOR

section
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

/-- States, under `ρ.Laws`: a step without rounds, from the main relation of C to that of C', at the
same radius; dn extracts. -/
def ldShape_step : Prop :=
  ∀ (C C' : LdCode E P) (ρ : Reshape C C') (e : ℕ) (St : Type) (s : Slf E St C.J), ρ.Laws →
    Step (fun x : E × St => some x) ρ.map (fun a => (a.1, ρ.up a.2)) (fun _ w => ρ.dn w)
      (C.rels s e fun _ => ()) (C'.rels (ρ.sl s) e fun _ => ())

/-- States, under `ρ.Laws`: the step of `Spec.ldShape_step` is a piece of a chain. -/
def ldShape_piece : Prop :=
  ∀ (C C' : LdCode E P) (ρ : Reshape C C') (e : ℕ) (St : Type)
      (s : Slf E St C.J) (q : Finset P → Prop),
    ρ.Laws →
    PieceTr (IOR.pure (fun x : E × St => some x) ρ.map)
      (Honest.pure (fun x : E × St => some x) ρ.map fun a => (a.1, ρ.up a.2))
      (C.rels s e fun _ => ()) (C'.rels (ρ.sl s) e fun _ => ()) (fun _ _ w => ρ.dn w)
      (Nums.pure Unit (fun x : E × St => some x) ρ.map) q q

/-- One relation up to a bijection of witnesses. States, under `ρ.Laws` and `ρ.Fix e`, of the
relaxed relations: w is a witness of (x, f) if and only if up w is one of (x, wd f); every witness
of (x, wd f) is up of one; and the same for the exact relations. -/
def ldShape_same : Prop :=
  ∀ (C C' : LdCode E P) (ρ : Reshape C C') (e : ℕ) (St : Type) (s : Slf E St C.J), ρ.Laws →
    ρ.Fix e →
    ∀ (x : E × St) (f : C.Word),
      (∀ w,
        (C.rels s e fun _ => ()).relR (x, f) w ↔
        (C'.rels (ρ.sl s) e fun _ => ()).relR (x, ρ.wd f) (ρ.up w)) ∧
      (∀ w', (C'.rels (ρ.sl s) e fun _ => ()).relR (x, ρ.wd f) w' → ρ.up (ρ.dn w') = w') ∧
      (∀ w,
        (C.rels s e fun _ => ()).rel x f w ↔
        (C'.rels (ρ.sl s) e fun _ => ()).rel x (ρ.wd f) (ρ.up w)) ∧
      (∀ w', (C'.rels (ρ.sl s) e fun _ => ()).rel x (ρ.wd f) w' → ρ.up (ρ.dn w') = w')

/-- States, under `ρ.Laws`: a bound on the list of the new code bounds the list of the old. -/
def ldShape_list : Prop :=
  ∀ (C C' : LdCode E P) (ρ : Reshape C C') (e L : ℕ), ρ.Laws → C'.ListAt e L → C.ListAt e L

def ldShape_comp : Prop :=
  ∀ (C C' C'' : LdCode E P) (ρ : Reshape C C') (ρ' : Reshape C' C''),
    ρ.Laws → ρ'.Laws → (ρ'.comp ρ).Laws ∧ ∀ e, ρ.Fix e → ρ'.Fix e → (ρ'.comp ρ).Fix e

def ldShape_refl : Prop := ∀ C : LdCode E P, (Reshape.refl C).Laws ∧ ∀ e, (Reshape.refl C).Fix e

def ldShape_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (D D' : A → LdCode E P) (ρ : ∀ a, Reshape (D a) (D' a)),
    (∀ a, (ρ a).Laws) → (Reshape.fam ρ).Laws ∧ ∀ e, (∀ a, (ρ a).Fix e) → (Reshape.fam ρ).Fix e

def ldShape_pairL : Prop :=
  ∀ (C C' D : LdCode E P) (ρ : Reshape C C'),
    ρ.Laws → (ρ.pairL D).Laws ∧ ∀ e, ρ.Fix e → (ρ.pairL D).Fix e

def ldShape_pairR : Prop :=
  ∀ (C C' D : LdCode E P) (ρ : Reshape C C'),
    ρ.Laws → (ρ.pairR D).Laws ∧ ∀ e, ρ.Fix e → (ρ.pairR D).Fix e

/-- Virtual rows. States the laws of `a.reshape C`, if `C.Laws` and `a.OK`. -/
def ldShape_arr : Prop :=
  ∀ (C : LdCode E P) (R R' : Type) [Fintype R] [DecidableEq R] [Fintype R']
      [DecidableEq R'] (a : Arr R R'),
    C.Laws → a.OK → (a.reshape C).Laws

/-- The lemma on virtual rows. States, under the hypotheses below: below the distance, a codeword of
the full interleaving that is close to an arranged word is arranged. -/
def ldShape_arr_fix : Prop :=
  ∀ (C : LdCode E P) (R R' : Type) [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
      (a : Arr R R') (d e : ℕ),
    C.Laws → C.Dist d → e < d → a.OK → (a.reshape C).Fix e

/-- Main rows and mask rows at once. -/
def ldShape_two : Prop :=
  ∀ (C Z : LdCode E P) (R R' Rz Rz' : Type) [Fintype R] [DecidableEq R] [Fintype R']
      [DecidableEq R'] [Fintype Rz] [DecidableEq Rz] [Fintype Rz'] [DecidableEq Rz']
      (a : Arr R R') (az : Arr Rz Rz'),
    C.Laws → a.OK → Z.Laws → az.OK →
    (((az.reshape Z).pairR (C.il R')).comp ((a.reshape C).pairL (Z.il Rz))).Laws ∧
    ∀ d dz e : ℕ, C.Dist d → e < d → Z.Dist dz → e < dz →
      (((az.reshape Z).pairR (C.il R')).comp ((a.reshape C).pairL (Z.il Rz))).Fix e

def ldShape_gather : Prop :=
  ∀ (A : Type) (Rm Rz : A → Type) [Fintype A] [DecidableEq A]
      [∀ a, Fintype (Rm a)] [∀ a, DecidableEq (Rm a)] [∀ a, Fintype (Rz a)]
      [∀ a, DecidableEq (Rz a)] (Cb Zb : LdCode E P),
    (Reshape.gather Rm Rz Cb Zb).Laws ∧ ∀ e, (Reshape.gather Rm Rz Cb Zb).Fix e

def ldShape_curry : Prop :=
  ∀ (C : LdCode E P) (R₁ R₂ : Type) [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂],
    (Reshape.curry C R₁ R₂).Laws ∧ ∀ e, (Reshape.curry C R₁ R₂).Fix e

end
end Spec
end Cb
