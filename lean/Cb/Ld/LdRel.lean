-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRel.lean: the main relation of the proximity blocks beyond unique decoding, and its
existential relaxation.

This file defines the relation that the proximity tests work with: an oracle is the encoding of a
message that meets a linear constraint. It also defines the relaxation of which their soundness
speaks: the oracle is within a given number of positions of such an encoding, and the witness names
the codeword, so that radii beyond unique decoding are allowed.
Definitions, and the statements of their first laws (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdRelProofs.lean and Cb/Ld/LdRelProofsCode.lean.

Why: a constraint relation can be relaxed by decoding (the oracles decode to the witness) only where
there is a decoding function. At a radius not below half the distance a word can be close to several
codewords and there is none. The paper that this protocol builds on (lean/CREDITS.md) relaxes
otherwise: the witness names a codeword within the distance, and that codeword meets the exact
relation. There is no decoder in the relation, any distance is allowed, and a statement may have
several witnesses.

The file has four parts.
 1. For any encoding N (`Hiop.Enc`) of oracles with finitely many positions.
      `Con N Φ` (Cb/Gen/Code.lean): the exact relation: y is the encoding of the witness
        (message, randomness), and Φ x message.
      `ConL N e Φ`: the relaxation at the radius e: y differs from the encoding of the witness at no
        more than e positions, and Φ x message. The field "dec" of N is not read.
      `ConLit N e Φ`: the same in the text's own letter: the witness is ((message, randomness),
        corrected oracles); the corrected oracles are within e of y, and (x, corrected oracles,
        (message, randomness)) is in the exact relation.
    The blocks use `ConL`.
    A radius is a count of positions: the distance δ of the text is the radius ⌊δ · number of
    positions⌋.
 2. Linear forms with a state (`Slf E St J`). The form is a parameter of a relation, the state is in
    the explicit part of a statement: x = (target, state).
    The operations of the text: the state is the vector itself (idf); multiple by a scalar in the
    state (smul); sum (add); zero; zeros to the right or left (padR, padL); a combination with
    coefficients made from a seed (bat); rows fixed at a point (fix) and its dual (unfold); two
    forms side by side (pair), a family (fam).
    Lean models no running time, so "succinct" is not said.
 3. A code with encoder, read under a transformation (`LdCode E P`), data only. Native words: a
    symbol for each native position p : NP, with coordinates NS p in E (a family of words of
    different lengths and alphabets is the case NP = pairs (component, place)).
    The transformation T takes a native word to a long word: a symbol with coordinates Aa at each
    long position x : P; it reads the native word at the positions src x only (this is the law `loc`
    of `Laws`). P is a parameter, so that codes read at common positions can be put side by side.
    `C.ext`, the kind of the implicit instance: the string is the native word f, the positions and
      symbols are the long ones, and reading is T. So "the implicit instance is T(f)" holds by type,
      a query is a query to T(f), and distance counts long positions.
    Native positions enter where a block sends a word (its srcO is `C.src`) and in zero knowledge
    (`C.nat`, `C.toLong`, `C.Zk`).
    `C.N`: the encoding of `C.ext`, without a decoder (its field "dec" is the constant none; so
      `Hiop.Enc.Laws` fails for it, on purpose: nothing here may lean on decoding).
    Operations: `C.il R`, pair, fam (the code complex), ofEnc, `LdCode.rep`.
    Notions under the transformation: Laws, Dist, Near, OnCode, ListAt, MCAat, LocalLE, Transparent,
    Zk; row, rowSlf.
 4. The main relation: `C.rels sl e core`, a joint of a chain (`Iop.IOR.Rels`):
    rel = Con C.N sl.Holds, relR = ConL C.N e sl.Holds, no condition on statements.
The guard (`Spec.ld_conL_guard`): for a component of Cb/Gen/Code.lean with `c.code.Props E`, whose
message and randomness fill the dimension, at the code's own radius of unique decoding, `ConL` holds
exactly if the oracles decode to the witness and Φ holds of the statement and the message.

Main names: `ConL`, `Slf`, `LdCode` with its notions, `LdCode.rels`: see parts 1 to 4 and their doc
comments.

Limits: the declared differences to the text are these.
  (a) One finite field E in the place of ring, module and challenge set; alphabets are
      E^(coordinates).
  (b) Code and transformation are one record.
  (c) The implicit instance is held as the native word and read as the long word; the text's
      statements "(x, T(f))" and ours "(x, f)" correspond, one to one if T is injective.
  (d) ListAt counts pairs (message, randomness); by injectivity of the encoder these are the
      codewords.
  (e) MCAat is for lines f₀ + θ f₁ only. The text uses no other generator, and shows that
      (1 - θ, θ) has the same error.
  (f) Zk is the text's "strong" form with error 0: every set of at most t long positions, exact
      equality of laws.
  (g) Where the text has a mask code interleaved twice whose two rows are read by different
      transformations (a mask that is carried along, a fresh one: two oracles, sent at different
      times), here stands the pair of two records with one encoder.
  (h) A form here has one row, as in the main relation; the text's general notion is a matrix with
      several rows: those are a family of forms.
  (i) Dist d with d ≥ 1 also says that T is injective on the code (with `Laws`); the text speaks of
      the minimum distance of the transformed code and has no lemma on it for complexes:
      `Spec.ld_dist_pair`, `Spec.ld_dist_il` are ours.
  (k) The text's complex is the bare product of codes, the transformation apart; "pair" and "fam"
      put codes with their transformations side by side, so Spec.ld_list_*, Spec.ld_mca_* hold for
      any componentwise transformation at one count of long positions. The step from a long radius
      to a component's own radius under a repetition is in Cb/Gen/CodeRep.lean.
This file says nothing on any protocol. No bound on a list or on agreement of a single code is
proved here, or assumed, but for the guard's premise `c.code.Props E`, whose field on agreement of
that one code is assumed: those of pairs and families are passed on from the components. The file
says nothing on erasure correction, on samples outside the domain, on running times. `ConL` at a
radius e that reaches the number of positions says nothing about y.
The notions follow definitions of the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Ior.Chain
import Ior.Frame
import Blocks.ClosingBlock
import Cb.Gen.Code
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-! ## 1. The relaxation at a radius, for any encoding -/

section Near
variable {Ex : ExtSpec} [Finite Ex.Pos]

/-- At how many positions two oracles differ. -/
def offCnt (y y' : Ex.Str) : ℕ := cnt fun p : Ex.Pos => Ex.rd y p ≠ Ex.rd y' p

variable (N : Enc Ex) {X : Type}

/-- The existential relaxation at the radius e: the witness's encoding is within e positions of the
oracles. -/
def ConL (e : ℕ) (Φ : X → N.Msg → Prop) : X × Ex.Str → N.Wit → Prop := fun a w =>
  offCnt a.2 (N.enc w.1 w.2) ≤ e ∧ Φ a.1 w.1

/-- The same, the corrected oracles being a part of the witness. -/
def ConLit (e : ℕ) (Φ : X → N.Msg → Prop) : X × Ex.Str → N.Wit × Ex.Str → Prop := fun a w =>
  offCnt a.2 w.2 ≤ e ∧ Con N Φ a.1 w.2 w.1

end Near

/-! ## 2. Linear forms with a state -/

/-- A linear form with a state: from states to vectors with coordinates J. -/
abbrev Slf (E St J : Type) : Type := St → J → E

namespace Slf
variable {E St St₁ St₂ J J' J₁ J₂ : Type}

/-- The claim: x = (target, state). -/
def Holds [Field E] [Fintype J] (sl : Slf E St J) : E × St → (J → E) → Prop := fun x m =>
  ∑ j, sl x.2 j * m j = x.1

/-- the state is the vector -/
def idf : Slf E (J → E) J := fun v => v
/-- a multiple; the scalar stands in the state -/
def smul [Mul E] (sl : Slf E St J) : Slf E (St × E) J := fun x j => sl x.1 j * x.2
def add [Add E] (sl₁ : Slf E St₁ J) (sl₂ : Slf E St₂ J) : Slf E (St₁ × St₂) J := fun x j =>
  sl₁ x.1 j + sl₂ x.2 j
def zero [Zero E] : Slf E Unit J := fun _ _ => 0
/-- zeros at further coordinates, to the right and to the left -/
def padR [Zero E] (sl : Slf E St J) : Slf E St (J ⊕ J') := fun x => Sum.elim (sl x) fun _ => 0
def padL [Zero E] (sl : Slf E St J) : Slf E St (J' ⊕ J) := fun x => Sum.elim (fun _ => 0) (sl x)
/-- A combination of the forms sl b, with the coefficients that Z makes from a seed. -/
def bat [Field E] {B D : Type} [Fintype B] {S : B → Type}
    (Z : D → B → E) (sl : ∀ b, Slf E (S b) J) : Slf E ((∀ b, S b) × D) J :=
  fun x j => ∑ b, sl b (x.1 b) j * Z x.2 b
/-- Rows fixed at a point: the coordinates are (row on the cube, place); the new form is the fold of
the rows of the old one. -/
def fix [Field E] {ι : Type} [Fintype ι] [DecidableEq ι] (sl : Slf E St ((ι → Bool) × J)) :
    Slf E (St × (ι → E)) J :=
  fun x c => ∑ b, sl x.1 (b, c) * Alg.eqk x.2 b
/-- Its dual: a claim on a folded vector as a claim on the vector. -/
def unfold [Field E] {ι : Type} [Fintype ι] (sl : Slf E St J) :
    Slf E (St × (ι → E)) ((ι → Bool) × J) :=
  fun x n => sl x.1 n.2 * Alg.eqk x.2 n.1
/-- two forms side by side -/
def pair (sl₁ : Slf E St₁ J₁) (sl₂ : Slf E St₂ J₂) : Slf E (St₁ × St₂) (J₁ ⊕ J₂) := fun x =>
  Sum.elim (sl₁ x.1) (sl₂ x.2)
/-- a family of forms side by side -/
def fam {A : Type} {S Jf : A → Type} (sl : ∀ a, Slf E (S a) (Jf a)) :
    Slf E (∀ a, S a) (Σ a, Jf a) :=
  fun x n => sl n.1 (x n.1) n.2

end Slf

/-- The fold of a vector with rows on the cube. -/
def foldV {E ι J : Type} [Field E] [Fintype ι] [DecidableEq ι]
    (γ : ι → E) (v : (ι → Bool) × J → E) : J → E :=
  fun c => ∑ b, Alg.eqk γ b * v (b, c)

/-! ## 3. A code with encoder, read under a transformation -/

/-- A code with encoder, read under a transformation: the data. P: the long positions. -/
structure LdCode (E P : Type) where
  /-- native positions, and the coordinates of the native symbol at a position -/
  NP : Type
  [finNP : Fintype NP]
  [decNP : DecidableEq NP]
  NS : NP → Type
  /-- coordinates of the message and of the encoding randomness -/
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  Q : Type
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  enc : (J → E) → (Q → E) → ∀ p, NS p → E
  /-- coordinates of a long symbol -/
  Aa : Type
  /-- the transformation, and the native positions that it reads for a long position -/
  T : (∀ p, NS p → E) → P → Aa → E
  src : P → Finset NP

attribute [instance] LdCode.finNP LdCode.decNP LdCode.finJ LdCode.decJ LdCode.finQ LdCode.decQ

namespace LdCode
variable {E P : Type}

/-- the native words -/
abbrev Word (C : LdCode E P) : Type := ∀ p, C.NS p → E

/-- The kind of the implicit instance: the string is a native word; positions and symbols are the
long ones. -/
abbrev ext (C : LdCode E P) : ExtSpec := ⟨C.Word, P, C.Aa → E, C.T⟩

/-- the native word, read natively -/
abbrev nat (C : LdCode E P) : ExtSpec := ⟨C.Word, C.NP, Σ p, C.NS p → E, fun f p => ⟨p, f p⟩⟩

/-- from native reading to long reading: the string stays -/
def toLong (C : LdCode E P) : ExtMap C.nat C.ext := ⟨fun f => f, C.src⟩

/-- The encoding, without a decoder, of the long and of the native kind. -/
@[reducible] def N [Fintype E] [Nonempty E] (C : LdCode E P) : Enc C.ext :=
  ⟨C.J → E, C.Q → E, C.enc, fun _ => none⟩
@[reducible] def Nn [Fintype E] [Nonempty E] (C : LdCode E P) : Enc C.nat :=
  ⟨C.J → E, C.Q → E, C.enc, fun _ => none⟩

/-- Interleaving: rows named by R under one code; a symbol holds one entry of each row; the
transformation works row by row. -/
@[reducible] def il (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] : LdCode E P where
  NP := C.NP
  NS := fun p => R × C.NS p
  J := R × C.J
  Q := R × C.Q
  enc := fun m r p s => C.enc (fun j => m (s.1, j)) (fun q => r (s.1, q)) p s.2
  Aa := R × C.Aa
  T := fun f x α => C.T (fun p s => f p (α.1, s)) x α.2
  src := C.src

/-- the row i of a native word of the interleaved code -/
def rowW (C : LdCode E P) {R : Type} [Fintype R] [DecidableEq R] (f : (C.il R).Word) (i : R) :
    C.Word :=
  fun p s => f p (i, s)

/-- Two codes side by side, read at common long positions. -/
@[reducible] def pair (C₁ C₂ : LdCode E P) : LdCode E P where
  NP := C₁.NP ⊕ C₂.NP
  NS := Sum.elim C₁.NS C₂.NS
  J := C₁.J ⊕ C₂.J
  Q := C₁.Q ⊕ C₂.Q
  enc := fun m r p => match p with
    | .inl p => C₁.enc (fun j => m (.inl j)) (fun q => r (.inl q)) p
    | .inr p => C₂.enc (fun j => m (.inr j)) (fun q => r (.inr q)) p
  Aa := C₁.Aa ⊕ C₂.Aa
  T := fun f x α => match α with
    | .inl α => C₁.T (fun p => f (.inl p)) x α
    | .inr α => C₂.T (fun p => f (.inr p)) x α
  src := fun x => (C₁.src x).disjSum (C₂.src x)

/-- the two sides of a native word of a pair, and a native word from its sides -/
def fstW {C₁ C₂ : LdCode E P} (f : (C₁.pair C₂).Word) : C₁.Word := fun p => f (.inl p)
def sndW {C₁ C₂ : LdCode E P} (f : (C₁.pair C₂).Word) : C₂.Word := fun p => f (.inr p)
def mkW {C₁ C₂ : LdCode E P} (f₁ : C₁.Word) (f₂ : C₂.Word) :
    (C₁.pair C₂).Word := fun p => match p with
  | .inl p => f₁ p
  | .inr p => f₂ p

/-- A code complex: a finite family of codes side by side, read at common long positions. -/
@[reducible] def fam {A : Type} [Fintype A] [DecidableEq A] (C : A → LdCode E P) : LdCode E P where
  NP := Σ a, (C a).NP
  NS := fun p => (C p.1).NS p.2
  J := Σ a, (C a).J
  Q := Σ a, (C a).Q
  enc := fun m r p => (C p.1).enc (fun j => m ⟨p.1, j⟩) (fun q => r ⟨p.1, q⟩) p.2
  Aa := Σ a, (C a).Aa
  T := fun f x α => (C α.1).T (fun p => f ⟨α.1, p⟩) x α.2
  src := fun x => Finset.univ.sigma fun a => (C a).src x

/-- One code of Code/Iface.lean, over the extension field E, one row; the long position x is read at
pos x. -/
@[reducible] def ofEnc {F : Type} [Field F] [Field E] [Algebra F E]
    (C₀ : Code.Enc F) (pos : P → Fin C₀.n) : LdCode E P where
  NP := Fin C₀.n
  NS := fun _ => Unit
  J := Fin C₀.msg
  Q := Fin C₀.r
  enc := fun m r p _ => C₀.encE E m r p
  Aa := Unit
  T := fun f x _ => f (pos x) ()
  src := fun x => {pos x}

/-- Repetition: n' is a multiple of the length; the long position x is read at x mod the length. -/
@[reducible] def rep {F : Type} [Field F] [Field E] [Algebra F E] (C₀ : Code.Enc F)
    (n' : ℕ) (h : C₀.n ∣ n') : LdCode E (Fin n') :=
  ofEnc C₀ fun x => ⟨x.val % C₀.n, Nat.mod_lt _ (Nat.pos_of_dvd_of_pos h x.pos)⟩

/-! ### The notions under the transformation -/

section Notions
variable [Field E] (C : LdCode E P)

/-- The laws: encoder and transformation are linear, the encoder is injective, the transformation
reads what it declares. -/
structure Laws : Prop where
  encLin : IsLinearMap E fun w : (C.J → E) × (C.Q → E) => C.enc w.1 w.2
  tLin   : IsLinearMap E C.T
  inj    : ∀ m r, C.enc m r = 0 → m = 0 ∧ r = 0
  loc    : ∀ (f g : C.Word) x, (∀ p ∈ C.src x, f p = g p) → C.T f x = C.T g x

/-- the transformation declares at most b native positions for a long position -/
def LocalLE (b : ℕ) : Prop := ∀ x, (C.src x).card ≤ b

/-- Transparent on the code: "bk" computes, from a long position and the long symbol of a codeword
there, the native symbols that were read for it. -/
def TranspBy (bk : P → (C.Aa → E) → C.Word) : Prop :=
  ∀ m r x, ∀ p ∈ C.src x, bk x (C.T (C.enc m r) x) p = C.enc m r p
def Transparent : Prop := ∃ bk, C.TranspBy bk

/-- On the set S of long positions the long word g agrees with the transform of a codeword. -/
def OnCode (g : P → C.Aa → E) (S : Finset P) : Prop := ∃ m r, ∀ x ∈ S, g x = C.T (C.enc m r) x

/-- The row of the generator behind the coordinate α of the long symbol at x: its entries at the
coordinates of message and randomness. -/
def row (x : P) (α : C.Aa) : C.J ⊕ C.Q → E := fun i => match i with
  | .inl j => C.T (C.enc (Pi.single j 1) 0) x α
  | .inr q => C.T (C.enc 0 (Pi.single q 1)) x α

/-- The rows of the generator as a linear form on (message, randomness); the state is (long
position, coordinate). -/
def rowSlf : Slf E (P × C.Aa) (C.J ⊕ C.Q) := fun s => C.row s.1 s.2

variable [Finite P]

/-- The distance under the transformation: the transform of a non-zero codeword (the encoding of a
pair (message, randomness) other than (0, 0)) is non-zero at d long positions or more. -/
def Dist (d : ℕ) : Prop := ∀ m r, ¬ (m = 0 ∧ r = 0) → d ≤ cnt fun x => C.T (C.enc m r) x ≠ 0

/-- Two native words are within e long positions of each other. -/
def Near (e : ℕ) (f g : C.Word) : Prop := cnt (fun x => C.T f x ≠ C.T g x) ≤ e

variable [Finite E]

/-- The list under the transformation: every native word has at most L pairs (message, randomness)
whose encoding is within e long positions. -/
def ListAt (e L : ℕ) : Prop :=
  ∀ f : C.Word, cnt (fun w : (C.J → E) × (C.Q → E) => C.Near e f (C.enc w.1 w.2)) ≤ L

/-- Mutual correlated agreement on lines under the transformation, as a count of exceptional θ. -/
def MCAat [Fintype P] (e bad : ℕ) : Prop :=
  ∀ f₀ f₁ : C.Word, cnt (fun θ : E => ∃ S : Finset P, Fintype.card P ≤ S.card + e ∧
    C.OnCode (C.T f₀ + θ • C.T f₁) S ∧ ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S)) ≤ bad

end Notions

/-- the sets of native positions that are read for at most t long positions -/
def budT (C : LdCode E P) (t : ℕ) : Finset C.nat.Pos → Prop := fun S =>
  ∃ X : Finset P, X.card ≤ t ∧ S ⊆ X.biUnion C.src

/-- Zero knowledge of the encoding under the transformation, t queries, error 0, every set of
positions: the law of the native symbols read for any t long positions does not depend on the
message. -/
def Zk [Fintype E] [Nonempty E] (C : LdCode E P) (t : ℕ) : Prop := C.Nn.Hides (C.budT t)

/-! ## 4. The main relation -/

/-- The main relation and its relaxation at the radius e, as a joint of a chain. A statement:
(target, state); the native word, read under the transformation. A witness: (message, randomness).
-/
def rels [Field E] [Fintype E] [Finite P] {Kc St : Type} (C : LdCode E P) (sl : Slf E St C.J)
    (e : ℕ) (core : C.N.Wit → Kc) :
    IOR.Rels Kc (E × St) C.ext C.N.Wit where
  rel  := Con C.N sl.Holds
  relR := ConL C.N e sl.Holds
  on   := fun _ => True
  core := core

end LdCode

/-! ## The statements -/

namespace Spec

/-- The two forms of the relaxation have the same witnesses: the corrected oracles are the encoding.
-/
def ld_conLit_iff : Prop :=
  ∀ (Ex : ExtSpec) [Finite Ex.Pos] (N : Enc Ex) (X : Type) (e : ℕ) (Φ : X → N.Msg → Prop)
      (a : X × Ex.Str) (w : N.Wit) (y' : Ex.Str),
    ConLit N e Φ a (w, y') ↔ ConL N e Φ a w ∧ y' = N.enc w.1 w.2

/-- The relation lies in its relaxation, at every radius. -/
def ld_con_sub_conL : Prop :=
  ∀ (Ex : ExtSpec) [Finite Ex.Pos] (N : Enc Ex) (X : Type) (e : ℕ) (Φ : X → N.Msg → Prop) x y w,
    Con N Φ x y w → ConL N e Φ (x, y) w

/-- A larger radius, a larger predicate: a larger relaxation. -/
def ld_conL_mono : Prop :=
  ∀ (Ex : ExtSpec) [Finite Ex.Pos] (N : Enc Ex) (X : Type) (e e' : ℕ) (Φ Φ' : X → N.Msg → Prop),
    e ≤ e' → (∀ x m, Φ x m → Φ' x m) → ∀ a w, ConL N e Φ a w → ConL N e' Φ' a w

/-- At the radius 0, for oracles that are given by their symbols, the relaxation is the relation. -/
def ld_conL_zero : Prop :=
  ∀ (Ex : ExtSpec) [Finite Ex.Pos] (N : Enc Ex) (X : Type) (Φ : X → N.Msg → Prop),
    (∀ y y' : Ex.Str, (∀ p, Ex.rd y p = Ex.rd y' p) → y = y') →
    ∀ x y w, ConL N 0 Φ (x, y) w ↔ Con N Φ x y w

/-- The guard: under the hypotheses below, at the code's own radius of unique decoding `ConL` holds
exactly if the oracles decode to the witness and Φ holds of the statement and the message, for a
component whose message and randomness fill the dimension. -/
def ld_conL_guard : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (c : Comp F),
    c.code.Props E → c.code.msg + c.code.r = c.code.k →
    ∀ (X : Type) (Φ : X → c.Msg E → Prop) (a : X × (c.ext E).Str) (w : (c.enc E).Wit),
      ConL (c.enc E) c.code.e Φ a w ↔ ((c.enc E).dec a.2 = some w ∧ Φ a.1 w.1)

/-- The relaxation is not a relaxation by decoding: there are a code with the laws, a radius below
its distance, and a statement with two witnesses that hold different messages. -/
def ld_conL_two : Prop :=
  ∃ (E P : Type) (_ : Field E) (_ : Fintype E) (_ : Fintype P) (C : LdCode E P) (d e : ℕ)
      (x : E × Unit) (f : C.Word) (w w' : C.N.Wit),
    C.Laws ∧ C.Dist d ∧ e < d ∧ w.1 ≠ w'.1 ∧
    ConL C.N e (Slf.zero (E := E) (J := C.J)).Holds (x, f) w ∧
    ConL C.N e (Slf.zero (E := E) (J := C.J)).Holds (x, f) w'

section
variable (E : Type) [Field E]

/-- Unfolding and folding: the value of the unfolded form at a vector is the value of the form at
the fold of the vector. -/
def ld_slf_unfold : Prop :=
  ∀ (St J ι : Type) [Fintype J] [Fintype ι] [DecidableEq ι] (sl : Slf E St J) (st : St)
      (γ : ι → E) (v : (ι → Bool) × J → E),
    ∑ n, sl.unfold (st, γ) n * v n = ∑ c, sl st c * foldV γ v c

/-- A claim of the unfolded form is the claim of the form on the fold. -/
def ld_holds_unfold : Prop :=
  ∀ (St J ι : Type) [Fintype J] [Fintype ι] [DecidableEq ι] (sl : Slf E St J) (τ : E) (st : St)
      (γ : ι → E) (v : (ι → Bool) × J → E),
    sl.unfold.Holds (τ, (st, γ)) v ↔ sl.Holds (τ, st) (foldV γ v)

/-- On a corner of the cube, fixing picks the row. -/
def ld_slf_fix_corner : Prop :=
  ∀ (St J ι : Type) [Fintype ι] [DecidableEq ι] (sl : Slf E St ((ι → Bool) × J))
      (st : St) (b : ι → Bool) (c : J),
    sl.fix (st, Alg.corner b) c = sl st (b, c)

/-- Two forms side by side: the sum of the two values. -/
def ld_slf_pair : Prop :=
  ∀ (St₁ St₂ J₁ J₂ : Type) [Fintype J₁] [Fintype J₂] (sl₁ : Slf E St₁ J₁) (sl₂ : Slf E St₂ J₂)
      (x : St₁ × St₂) (m : J₁ ⊕ J₂ → E),
    ∑ j, sl₁.pair sl₂ x j * m j = ∑ j, sl₁ x.1 j * m (.inl j) + ∑ j, sl₂ x.2 j * m (.inr j)

/-- States, of a combination: its value is the combination of the values. -/
def ld_slf_bat : Prop :=
  ∀ (J B D : Type) [Fintype J] [Fintype B] (S : B → Type) (Z : D → B → E) (sl : ∀ b, Slf E (S b) J)
      (x : (∀ b, S b) × D) (m : J → E),
    ∑ j, Slf.bat Z sl x j * m j = ∑ b, Z x.2 b * ∑ j, sl b (x.1 b) j * m j

variable (P : Type)

/-- States, under `C.Laws`: the transform of an encoding is given by the rows of the generator. -/
def ld_row_spec : Prop :=
  ∀ C : LdCode E P, C.Laws →
    ∀ m r x α, C.T (C.enc m r) x α = ∑ j, C.row x α (.inl j) * m j + ∑ q, C.row x α (.inr q) * r q

/-- These state: the laws are kept by interleaving, pairs and families. -/
def ld_laws_il : Prop :=
  ∀ (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R], C.Laws → (C.il R).Laws
def ld_laws_pair : Prop := ∀ C₁ C₂ : LdCode E P, C₁.Laws → C₂.Laws → (C₁.pair C₂).Laws
def ld_laws_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → LdCode E P),
    (∀ a, (C a).Laws) → (LdCode.fam C).Laws

/-- These state: transparency is kept by interleaving and pairs; one code read at given positions is
transparent. -/
def ld_transp_il : Prop :=
  ∀ (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R], C.Transparent → (C.il R).Transparent
def ld_transp_pair : Prop :=
  ∀ C₁ C₂ : LdCode E P, C₁.Transparent → C₂.Transparent → (C₁.pair C₂).Transparent
def ld_transp_ofEnc : Prop :=
  ∀ (F : Type) [Field F] [Algebra F E] (C₀ : Code.Enc F) (pos : P → Fin C₀.n),
    (LdCode.ofEnc (E := E) C₀ pos).Transparent

variable [Fintype P]

/-- States, of Near for a pair: both sides are near. -/
def ld_near_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (e : ℕ) (f g : (C₁.pair C₂).Word), (C₁.pair C₂).Near e f g →
    C₁.Near e (LdCode.fstW f) (LdCode.fstW g) ∧ C₂.Near e (LdCode.sndW f) (LdCode.sndW g)

/-- These state: `Dist d` passes from two codes to their pair, and from a code to its interleaving.
-/
def ld_dist_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (d : ℕ), C₁.Dist d → C₂.Dist d → (C₁.pair C₂).Dist d
def ld_dist_il : Prop :=
  ∀ (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] (d : ℕ), C.Dist d → (C.il R).Dist d

variable [Finite E]

/-- The list of a complex is at most the product of the lists, at one radius in long positions. -/
def ld_list_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (e L₁ L₂ : ℕ),
    C₁.ListAt e L₁ → C₂.ListAt e L₂ → (C₁.pair C₂).ListAt e (L₁ * L₂)
def ld_list_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → LdCode E P) (e : ℕ) (L : A → ℕ),
    (∀ a, (C a).ListAt e (L a)) → (LdCode.fam C).ListAt e (∏ a, L a)

/-- These state: the exceptional θ of a complex are at most the sum. -/
def ld_mca_pair : Prop :=
  ∀ (C₁ C₂ : LdCode E P) (e b₁ b₂ : ℕ),
    C₁.MCAat e b₁ → C₂.MCAat e b₂ → (C₁.pair C₂).MCAat e (b₁ + b₂)
def ld_mca_fam : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → LdCode E P) (e : ℕ) (b : A → ℕ),
    (∀ a, (C a).MCAat e (b a)) → (LdCode.fam C).MCAat e (∑ a, b a)

end
end Spec
end Cb
