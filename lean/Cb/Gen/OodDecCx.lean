-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecCx.lean: list decoding with an out-of-domain sample, for several interleaved words at
once. The decoder with samples for a code complex (`Cb.Cx` of Cb/Gen/Code.lean): the words that a
prover sends together, each component under its own code and radius, and one joint sample of all
their messages.

Definitions and statements; proofs in Cb/Gen/OodDecCxProofs.lean. A code complex is a finite family
of named components, each a table of interleaved rows under one code. Sample maps, candidates and
the three kinds of value are those of Cb/Gen/OodDec.lean: a candidate for an answer, at a seed, is a
member of the list that has this answer.

Main names, the definitions:
  `Comp.fullOf c m r`: among the statements in `Cb.Spec`, only Cb/Gen/OodDecRep.lean states
    something with it.
  `Comp.Near c e y m`, `Cx.Near K e y m`: see their docstrings. A symbol is a column: one entry of
    each interleaved row. The radius e is the caller's, not the field "e" of the code.
  `Cx.ans K Z ρ m`: the answers of the message m at the seed ρ: the sample map Z (`Cb.Ood.Sample`)
    applied to all entries of the message, read in E (`Cx.ents`): all components, all rows, all
    places as one vector. The encoding randomness is not under the sample.
  `Cx.decS`: the decoder: the only message within the radii that has the answers / none / several
    (`Cb.Ood.Val`).

What is decoded, and a difference to Cb/Gen/Code.lean: a candidate is a message of which some
encoding is close (and that has the answers): the close codewords are sought in the image of the
encoder (message, randomness, zeros), not in the whole code of dimension k, as the decoder of
`Cx.enc` in Cb/Gen/Code.lean does. What becomes unique is the message; two encodings of one message
under different randomness may both be close, and they are one candidate. So the decoder returns no
encoding randomness.

Main names, the statements. From `ood_comp_list` on each assumes "place" in every component: msg + r
≤ k (the first field of `Code.Enc.Props`); no other field of `Code.Enc.Props` is used, except in the
guard (the distance of the generators, where it is needed, is a hypothesis of its own).
  `ood_comp_list`, `ood_cx_list`: a bound L a on the list of full messages of each component (tables
    of vectors of length k to which the word decodes: the form of Cb/Gen/JohnsonList.lean) bounds
    the list of messages of the complex by the product of the L a.
  `ood_cx_cnt`: the counting lemma (`ood_cnt_clash`, Cb/Gen/OodDec.lean), under such bounds L a and
    `Sample.OK`: the seeds at which some answers get the value "several" number at most ((∏ L a)
    choose 2) err (`Sample.err`); twice their number is at most (∏ L a)² err.
  `ood_cx_johnson`: the first of these bounds, under `Sample.OK`, with the Johnson bound for the
    lists (from the distance of the generators and "each radius is below the Johnson radius" alone).
  `ood_cx_close`, `ood_cx_enc` (e' = 0): at every seed, the distance of the generator being at least
    d a (`HasDist`): a word within e' a ≤ e a symbols of an encoding of m, with e a + e' a < d a,
    and the answers of m: `Cx.decS` returns m.
  `ood_cx_guard`: the guard: at the codes' own radii, under `Code.Enc.Props` (2 e < d): the value is
    never "several", and if it is "one m" then the decoder of `Cx.enc` (Cb/Gen/Code.lean) returns m
    with some randomness.

Limits: the converse of the guard fails: the decoder of `Cx.enc` also accepts words that are close
to a codeword outside the image of the encoder. Nothing on hiding (the answers are linear
functionals of the message: a protocol that wants zero knowledge puts fresh random entries into the
message, under the sample). No relaxed relation is defined. The counts say nothing if ((∏ L a)
choose 2) err reaches the number of seeds.
The shape (one joint sample for the words sent together; unique is the message) follows advice
(lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDec
import Cb.Gen.JohnsonList
import Cb.Gen.Code
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

section
variable {F : Type} [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

variable {E} in
/-- The full messages that the encoder forms from message and randomness (message, randomness,
zeros), read in E. -/
def Comp.fullOf (c : Comp F) (m : c.Msg E) (r : c.Rnd E) : c.R → Fin c.code.k → E := fun i =>
  c.code.fm (fun j => (m i j).toE) fun t => (r i t).toE

/-- Within the radius, one component: some encoding of m differs from y in at most e symbols. -/
def Comp.Near (c : Comp F) (e : ℕ) (y : (c.ext E).Str) (m : c.Msg E) : Prop :=
  ∃ r : c.Rnd E, cnt (fun p => y p ≠ (c.enc E).enc m r p) ≤ e

/-- Within the radii: in every component. -/
def Cx.Near (K : Cx F) (e : K.A → ℕ) (y : (K.ext E).Str) (m : K.Msg E) : Prop :=
  ∀ a, (K.comp a).Near E (e a) (y a) (m a)

variable {E} in
/-- The answers of a message: the sample map on all its entries. -/
def Cx.ans (K : Cx F) (Z : Ood.Sample E K.Ent) (ρ : Z.D) (m : K.Msg E) : Z.S → E :=
  Z.val ρ (K.ents m)

/-- The decoder of a complex, with one joint sample. -/
def Cx.decS (K : Cx F) (e : K.A → ℕ) (Z : Ood.Sample E K.Ent) (y : (K.ext E).Str)
    (ρ : Z.D) (v : Z.S → E) : Ood.Val (K.Msg E) :=
  Ood.pick (K.Near E e y) (K.ans Z) ρ v

end

namespace Spec
open Cb.Ood

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

def ood_cx_one_iff : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D)
      (v : Z.S → E) (m : K.Msg E),
    K.decS E e Z y ρ v = .one m ↔
    K.Near E e y m ∧ K.ans Z ρ m = v ∧ ∀ m', K.Near E e y m' → K.ans Z ρ m' = v → m' = m

def ood_cx_none_iff : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E),
    K.decS E e Z y ρ v = .none ↔ ∀ m, K.Near E e y m → K.ans Z ρ m ≠ v

def ood_cx_several_iff : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E),
    K.decS E e Z y ρ v = .several ↔
    ∃ m m', m ≠ m' ∧ K.Near E e y m ∧ K.Near E e y m' ∧ K.ans Z ρ m = v ∧ K.ans Z ρ m' = v

/-- At a seed at which no answers get the value "several", whatever is within the radii and has the
answers is what the decoder returns (an equivalence: see the statement). -/
def ood_cx_good : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D),
    (¬ ∃ v, K.decS E e Z y ρ v = .several) →
    ∀ (v : Z.S → E) (m : K.Msg E), K.decS E e Z y ρ v = .one m ↔ K.Near E e y m ∧ K.ans Z ρ m = v

/-- If msg + r ≤ k, the list of messages of a component is at most the list of full messages of its
word. -/
def ood_comp_list : Prop :=
  ∀ (c : Comp F) (e : ℕ) (y : (c.ext E).Str) (L : ℕ), c.code.msg + c.code.r ≤ c.code.k →
    ListLE (DecodesTo (c.code.GE E) e (c.tab y)) L → ListLE (c.Near E e y) L

def ood_cx_list : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (y : (K.ext E).Str) (L : K.A → ℕ),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    (∀ a, ListLE (DecodesTo ((K.comp a).code.GE E) (e a) ((K.comp a).tab (y a))) (L a)) →
    ListLE (K.Near E e y) (∏ a, L a)

/-- The counting lemma for a complex. The words are fixed before the seed is drawn; the answers may
depend on the seed. -/
def ood_cx_cnt : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (L : K.A → ℕ),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    (∀ a, ListLE (DecodesTo ((K.comp a).code.GE E) (e a) ((K.comp a).tab (y a))) (L a)) → Z.OK →
    cnt (fun ρ : Z.D => ∃ v, K.decS E e Z y ρ v = .several) ≤ (∏ a, L a).choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ v, K.decS E e Z y ρ v = .several) ≤ (∏ a, L a) ^ 2 * Z.err

/-- The counting lemma below the Johnson radius: no hypothesis on lists. -/
def ood_cx_johnson : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) →
    (∀ a, InJohnson (K.comp a).code.n (K.comp a).code.d (e a)) → Z.OK →
    cnt (fun ρ : Z.D => ∃ v, K.decS E e Z y ρ v = .several) ≤
      (∏ a, listMax (K.comp a).code.n (K.comp a).code.d (e a)).choose 2 * Z.err

/-- Close to an encoding, at every seed. -/
def ood_cx_close : Prop :=
  ∀ (K : Cx F) (e e' : K.A → ℕ) (Z : Sample E K.Ent) (y : (K.ext E).Str) (m : K.Msg E),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) →
    (∀ a, e' a ≤ e a) → (∀ a, e a + e' a < (K.comp a).code.d) →
    K.Near E e' y m → ∀ ρ : Z.D, K.decS E e Z y ρ (K.ans Z ρ m) = .one m

/-- Under the hypotheses below, decoding undoes encoding, at every seed, for all radii below the
distance, with the answers of m. -/
def ood_cx_enc : Prop :=
  ∀ (K : Cx F) (e : K.A → ℕ) (Z : Sample E K.Ent) (m : K.Msg E) (r : K.Rnd E),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) → (∀ a, e a < (K.comp a).code.d) →
    ∀ ρ : Z.D, K.decS E e Z ((K.enc E).enc m r) ρ (K.ans Z ρ m) = .one m

/-- The guard: at the codes' own radii of unique decoding. -/
def ood_cx_guard : Prop :=
  ∀ (K : Cx F) (Z : Sample E K.Ent) (y : (K.ext E).Str) (ρ : Z.D) (v : Z.S → E), K.Props E →
    K.decS E (fun a => (K.comp a).code.e) Z y ρ v ≠ .several ∧
    ∀ m, K.decS E (fun a => (K.comp a).code.e) Z y ρ v = .one m → ∃ r, (K.enc E).dec y = some (m, r)

end
end Spec
end Cb
