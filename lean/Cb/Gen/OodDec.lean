-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDec.lean: list decoding with out-of-domain samples: decoding beyond half the distance,
with samples of the message.

Definitions and statements (Cb.Spec.ood_*); the proofs are in Cb/Gen/OodDecProofs.lean.

Why: at a radius e with 2 e < d (d a lower bound on the distance: `Blocks.HasDist`) a table of words
has at most one table of messages within e columns, and "the decoded message" (`Blocks.dec`) is a
function of the table. At a larger radius (up to the Johnson radius: Cb/Gen/JohnsonList.lean) there
may be several: a list (list decoding). The standard remedy: right after the words are sent, the
verifier draws a seed, and the prover answers with a few linear functionals of the message that the
seed names (an "out-of-domain sample"). Two different messages of the list give the same answers for
few seeds only (at most err, under `Sample.OK`), so outside a small set of seeds, which depends on
the words alone, at most one message of the list fits the answers, whatever the prover answers. "The
decoded message" is again a function: of the table, the seed and the answers.

Main names, the definitions (in `Cb.Ood`):
 1. Without an error-correcting code (`Cand`, `Coll`, `Val`, `pick`, `Clash`, `ListLE`): a list Lst
    of members u : U, an evaluation ev : seed → U → answer. `pick` has three kinds of value (`Val`):
    the only candidate (one u), no candidate (none), two different candidates (several). `Val.opt`
    forgets the difference between none and several. `Clash` (the bad seeds) does not mention the
    prover's answer.
 2. A sample map (`Sample`): for each seed a matrix with rows S (the names of the answers) and
    columns J (the entries of a message), and a number err. `Sample.OK`: a vector other than 0 has
    all answers 0 for at most err seeds. This is a zero-evader with several rows (`Cb.Evader` of
    Cb/Gen/BatEvader.lean has one row); the rows need not be independent, only the count for the
    whole matrix matters.
 3. Tables of words (`whole`, `InList`, `DecodesToS`, `decS`, `ClashS`) over Blocks/Decode.lean: any
    generator matrix G, any radius e, any rows. `Blocks.DecodesTo G e f M`: in at most e columns the
    table f differs, in some row, from the codewords of M. What is sampled is a "view" of the table
    M of full messages: any function view : (R → κ → E) → (J → E). A view that reads the message
    part alone is allowed too: then two members of the list with the same message part and different
    encoding randomness are one candidate, and `decS` returns the message part, not the codeword.
 4. Several tables under one sample (`InListFam`, `decF`): a finite family of tables, each with its
    own generator matrix, radius and rows (words that are sent together, say a main word and a mask
    word).

Main names, the statements (in `Cb.Spec`; the others are told in docstrings):
  `ood_pick_iff`, `ood_pick_none_iff`, `ood_pick_several_iff`: what the three kinds of value mean.
  `ood_cnt_clash`: the counting lemma, abstract: a list of at most L members, any two of which agree
    at no more than k seeds, clashes at no more than (L choose 2) k seeds.
  `ood_ok_one`, `ood_ok_pow`: `Sample.one`, `Sample.pow` have
    `Sample.OK`, if the evader has `Evader.OK`.
  `ood_list_view`, `ood_cnt_clashS`, `ood_cnt_severalS`, `ood_main`: a bound on the list of full
    messages (a hypothesis here; the Johnson bound gives one) bounds the list of views, and so, for
    a sample map with `Sample.OK`, the number of bad seeds.
  `ood_decS_good` (outside `ClashS`): in place of `Blocks.DecodesTo.dec_eq` and
    `Blocks.decodesTo_iff_dec_eq`; `ood_lt_cnt_off` (outside `ClashS`): in place of
    `Blocks.lt_cnt_off`; `ood_decS_near`, `ood_decS_mulVec` (at every seed): in place of
    `Blocks.dec_mulVec`.
  `ood_decS_imp`, `ood_decS_comp`, `ood_decS_combs`: sub-tables and combinations of rows. In place
    of `Blocks.dec_comp`, `Blocks.dec_combs`: see "What fails" under Limits.
  `ood_decS_unique`: the guard, for 2 e < d: see its docstring.

Limits:
What fails beyond half the distance, and is therefore not stated (a small example, at 2 e = d:
Cb/Gen/OodDecTest.lean). `Blocks.dec_comp`, `Blocks.dec_combs`, `Blocks.dec_line`,
`Blocks.dec_row_eq` say that the decoded message of a sub-table, of a combination of rows, of a row
that stands in two tables, is the corresponding part of the decoded message of the table. Here the
derived table has a list of its own, which may hold messages that come from no member of the first
list, and its samples are its own. What remains (`ood_decS_imp`): the part of any member M of the
first list lies in the list of the derived table; so outside the derived table's own `ClashS`, and
if the answers given for the derived table are those of that part, `decS` of the derived table
returns it. If other answers are given, `decS` of the derived table may return another message.
Whoever relies on these four lemmas must carry one constraint for each oracle.
No bound on a list is proved here but from another bound (in the statements ood_list_*).
`Sample.OK` with err ≥ |D| holds for free, and (L choose 2) err ≥
|D| says nothing: the counts are as good as (L choose 2) err / |D| is small. Nothing on hiding: an
answer is a linear functional of what the view shows, and whoever wants zero knowledge has to pay
for it (fresh random coordinates under the sample). No relaxed relation is defined (what a statement
about oracles means when the value is "several" is left to the protocol). This file says nothing on
proximity gaps, on protocols, on running times (`pick` is a choice). The code's own radius
`Code.Enc.e` and the field "unique" of `Code.Enc.Props` are not used.
That samples are wanted, that they may be any zero-evader applied to the message, and that what
becomes unique is the message and not the encoding randomness follows advice; the union bound over
the pairs of a list is the field's (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.BatEvader
import Blocks.Decode
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Ood
open Prob Blocks

/-! ## 1. The choice among the candidates of a list -/

/-- u is a candidate: a member of the list with the answer y at the seed ρ. -/
def Cand {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y) (u : U) : Prop :=
  Lst u ∧ ev ρ u = y

/-- Collision ("several"): the answer y has two different candidates at the seed ρ. -/
def Coll {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y) : Prop :=
  ∃ u u', u ≠ u' ∧ Cand Lst ev ρ y u ∧ Cand Lst ev ρ y u'

/-- The three kinds of value of a decoder with samples. -/
inductive Val (U : Type) where
  /-- the only candidate -/
  | one (u : U)
  /-- there is no candidate -/
  | none
  /-- there are two different candidates -/
  | several

/-- The candidate, if there is exactly one. -/
def Val.opt {U : Type} : Val U → Option U
  | .one u => some u
  | .none => Option.none
  | .several => Option.none

open Classical in
/-- The choice: the only candidate, or "none", or "several". -/
def pick {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y) : Val U :=
  if h : ∃ u,
    Cand Lst ev ρ y u then (if Coll Lst ev ρ y then .several else .one h.choose) else .none

/-- The bad seeds: two different members of the list have the same answer. -/
def Clash {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) : Prop :=
  ∃ u u', Lst u ∧ Lst u' ∧ u ≠ u' ∧ ev ρ u = ev ρ u'

/-- The list has at most L members. -/
def ListLE {U : Type} (Lst : U → Prop) (L : ℕ) : Prop :=
  ∀ S : Finset U, (∀ u ∈ S, Lst u) → S.card ≤ L

/-! ## 2. Sample maps -/

/-- A sample map: the data. -/
structure Sample (E J : Type) where
  /-- the seeds -/
  D : Type
  [fin : Fintype D]
  [ne : Nonempty D]
  /-- the names of the answers -/
  S : Type
  [finS : Fintype S]
  /-- the matrix that a seed gives -/
  mat : D → S → J → E
  /-- the number of seeds at which a vector other than 0 may have all answers 0 -/
  err : ℕ

attribute [instance] Sample.fin Sample.ne Sample.finS

/-- The answers of the vector u at the seed ρ. -/
def Sample.val {E J : Type} [Field E] [Fintype J] (Z : Sample E J) (ρ : Z.D) (u : J → E) :
    Z.S → E :=
  fun s => ∑ j, Z.mat ρ s j * u j

/-- The property of a sample map. -/
def Sample.OK {E J : Type} [Field E] [Fintype J] (Z : Sample E J) : Prop :=
  ∀ v : J → E, v ≠ 0 → cnt (fun ρ : Z.D => Z.val ρ v = 0) ≤ Z.err

/-- No sample: one seed, no answer. -/
@[reducible] def Sample.nil (E J : Type) : Sample E J :=
  { D := Unit, S := Empty, mat := fun _ s => Empty.elim s, err := 1 }

/-- One answer: a zero-evader as it is. -/
@[reducible] def Sample.one {E J : Type} (Z : Evader E J) : Sample E J :=
  { D := Z.D, S := Unit, mat := fun ρ _ => Z.ze ρ, err := Z.err }

/-- s answers at s independent seeds of a zero-evader. -/
@[reducible] def Sample.pow {E J : Type} (Z : Evader E J) (s : ℕ) : Sample E J :=
  { D := Fin s → Z.D, S := Fin s, mat := fun ρ i => Z.ze (ρ i), err := Z.err ^ s }

/-! ## 3. Tables of words -/

/-- All coordinates of all rows, as one vector. -/
def whole {E κ R : Type} (M : R → κ → E) : R × κ → E := fun n => M n.1 n.2

/-- The list: u is the view of a table of full messages to which f decodes at the radius e. -/
def InList {E ι κ R J : Type} [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ)
    (view : (R → κ → E) → J → E) (f : R → ι → E) (u : J → E) : Prop :=
  ∃ M, DecodesTo G e f M ∧ view M = u

/-- The table f, with the answers y at the seed ρ, decodes to u. -/
def DecodesToS {E ι κ R J : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J]
    (G : Matrix ι κ E) (e : ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E)
    (ρ : Z.D) (y : Z.S → E) (u : J → E) : Prop :=
  Cand (InList G e view f) Z.val ρ y u

/-- The decoder with samples: the one view of a table of messages within the radius that has the
answers, if there is exactly one; else "none" or "several". -/
def decS {E ι κ R J : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J]
    (G : Matrix ι κ E) (e : ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E)
    (ρ : Z.D) (y : Z.S → E) : Val (J → E) :=
  pick (InList G e view f) Z.val ρ y

/-- The bad seeds of a table. They depend on the table, not on the answers. -/
def ClashS {E ι κ R J : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
    (e : ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (ρ : Z.D) : Prop :=
  Clash (InList G e view f) Z.val ρ

/-! ## 4. Several tables under one sample -/

/-- The list of a family: u is the view of tables of full messages, one for each member of the
family, to which the members decode, each at its own radius. -/
def InListFam {E A J : Type} {ι κ R : A → Type} [Field E] [∀ a, Fintype (ι a)] [∀ a, Fintype (κ a)]
    (G : ∀ a, Matrix (ι a) (κ a) E) (e : A → ℕ) (view : (∀ a, R a → κ a → E) → J → E)
    (f : ∀ a, R a → ι a → E) (u : J → E) : Prop :=
  ∃ M : ∀ a, R a → κ a → E, (∀ a, DecodesTo (G a) (e a) (f a) (M a)) ∧ view M = u

/-- The decoder of a family, with one joint sample. -/
def decF {E A J : Type} {ι κ R : A → Type} [Field E] [∀ a, Fintype (ι a)]
    [∀ a, Fintype (κ a)] [Fintype J] (G : ∀ a, Matrix (ι a) (κ a) E) (e : A → ℕ)
    (view : (∀ a, R a → κ a → E) → J → E) (Z : Sample E J) (f : ∀ a, R a → ι a → E)
    (ρ : Z.D) (y : Z.S → E) : Val (J → E) :=
  pick (InListFam G e view f) Z.val ρ y

end Cb.Ood

/-! ## The statements -/

namespace Cb.Spec
open Prob Blocks Cb.Ood

def ood_pick_iff : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y) (u : U),
    pick Lst ev ρ y = .one u ↔ Cand Lst ev ρ y u ∧ ∀ u', Cand Lst ev ρ y u' → u' = u

def ood_pick_none_iff : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y),
    pick Lst ev ρ y = .none ↔ ∀ u, ¬ Cand Lst ev ρ y u

def ood_pick_several_iff : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y),
    pick Lst ev ρ y = .several ↔ Coll Lst ev ρ y

/-- Outside the bad seeds (`Clash`), `pick` returns "one u" if and only if u is a candidate. -/
def ood_pick_good : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D),
    ¬ Clash Lst ev ρ → ∀ (y : Y) (u : U), pick Lst ev ρ y = .one u ↔ Cand Lst ev ρ y u

/-- A seed is bad if and only if some answer has two candidates. -/
def ood_clash_iff : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D),
    Clash Lst ev ρ ↔ ∃ y, Coll Lst ev ρ y

/-- The counting lemma, abstract: the union bound over the pairs of the list. -/
def ood_cnt_clash : Prop :=
  ∀ (U D Y : Type) [Fintype D] (Lst : U → Prop) (ev : D → U → Y) (L k : ℕ), ListLE Lst L →
    (∀ u u', Lst u → Lst u' → u ≠ u' → cnt (fun ρ => ev ρ u = ev ρ u') ≤ k) →
    cnt (Clash Lst ev) ≤ L.choose 2 * k

/-- The counting lemma for a sample map with `Sample.OK` and any list of at most L vectors. -/
def ood_cnt_clash_sample : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (Lst : (J → E) → Prop) (L : ℕ),
    ListLE Lst L → Z.OK → cnt (Clash Lst Z.val) ≤ L.choose 2 * Z.err

/-- The coarser form: half of L² err. -/
def ood_cnt_clash_sq : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (Lst : (J → E) → Prop) (L : ℕ),
    ListLE Lst L → Z.OK → 2 * cnt (Clash Lst Z.val) ≤ L ^ 2 * Z.err

/-- The counting lemma in the words of the decoder. -/
def ood_cnt_several : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (Lst : (J → E) → Prop) (L : ℕ),
    ListLE Lst L → Z.OK →
    cnt (fun ρ : Z.D => ∃ y, pick Lst Z.val ρ y = .several) ≤ L.choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ y, pick Lst Z.val ρ y = .several) ≤ L ^ 2 * Z.err

/-- This and the next three statements carry a bound on a list over: to a part of the list; to an
image; to a product; from a count. -/
def ood_list_mono : Prop :=
  ∀ (U : Type) (Lst Lst' : U → Prop) (L : ℕ), (∀ u, Lst' u → Lst u) → ListLE Lst L → ListLE Lst' L
def ood_list_image : Prop :=
  ∀ (T U : Type) (P : T → Prop) (view : T → U) (L : ℕ),
    ListLE P L → ListLE (fun u => ∃ t, P t ∧ view t = u) L
def ood_list_pi : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (T : A → Type) (P : ∀ a, T a → Prop) (L : A → ℕ),
    (∀ a, ListLE (P a) (L a)) → ListLE (fun t : ∀ a, T a => ∀ a, P a (t a)) (∏ a, L a)
def ood_list_of_cnt : Prop :=
  ∀ (U : Type) [Finite U] (Lst : U → Prop) (L : ℕ), cnt Lst ≤ L → ListLE Lst L

def ood_ok_one : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Evader E J), Z.OK → (Sample.one Z).OK
def ood_ok_pow : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Evader E J) (s : ℕ), Z.OK → (Sample.pow Z s).OK

/-- When the decoder returns "one u", written out. -/
def ood_decS_iff : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
      (e : ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (ρ : Z.D)
      (y : Z.S → E) (u : J → E),
    decS G e view Z f ρ y = .one u ↔
    (∃ M, DecodesTo G e f M ∧ view M = u) ∧
    Z.val ρ u = y ∧
    ∀ M', DecodesTo G e f M' → Z.val ρ (view M') = y → view M' = u

/-- Outside the bad seeds of the table, the view of whatever is within the radius and has the
answers is what the decoder returns. -/
def ood_decS_good : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (ρ : Z.D),
    ¬ ClashS G e view Z f ρ →
    ∀ (y : Z.S → E) (u : J → E),
      decS G e view Z f ρ y = .one u ↔ (∃ M, DecodesTo G e f M ∧ view M = u) ∧ Z.val ρ u = y

/-- A wrong message is far: outside the bad seeds, if the decoder, given the answers of M, does not
return the view of M, more than e columns are off M. -/
def ood_lt_cnt_off : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (ρ : Z.D),
    ¬ ClashS G e view Z f ρ →
    ∀ M : R → κ → E, decS G e view Z f ρ (Z.val ρ (view M)) ≠ .one (view M) → e < cnt (Off G f M)

/-- A bound on the list of full messages bounds the list of views. -/
def ood_list_view : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (f : R → ι → E) (L : ℕ),
    ListLE (DecodesTo G e f) L → ListLE (InList G e view f) L

/-- The counting lemma for a table: if the list of full messages has at most L members and `Z.OK`
holds, there are at most (L choose 2) err bad seeds. -/
def ood_cnt_clashS : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (L : ℕ),
    ListLE (DecodesTo G e f) L → Z.OK → cnt (ClashS G e view Z f) ≤ L.choose 2 * Z.err

/-- The counting lemma for a table, in the words of the decoder. -/
def ood_cnt_severalS : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (L : ℕ),
    ListLE (DecodesTo G e f) L → Z.OK →
    cnt (fun ρ : Z.D => ∃ y, decS G e view Z f ρ y = .several) ≤ L.choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ y, decS G e view Z f ρ y = .several) ≤ L ^ 2 * Z.err

/-- All in one count. The table is fixed before the seed is drawn; the answers may depend on the
seed. Under the hypotheses below, at all but (L choose 2) err seeds: whatever answers y are given,
every table of messages within the radius whose view has these answers has the view that the decoder
returns. -/
def ood_main : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (L : ℕ),
    ListLE (DecodesTo G e f) L → Z.OK →
    cnt (fun ρ : Z.D =>
        ∃ (y : Z.S → E) (M : R → κ → E),
          DecodesTo G e f M ∧ Z.val ρ (view M) = y ∧ decS G e view Z f ρ y ≠ .one (view M)) ≤
      L.choose 2 * Z.err

/-- Close to a codeword, at every seed, under `HasDist G d`: for a table within e' ≤ e columns of
the codewords of M, with e + e' < d, and with the answers of M, the decoder returns the view of
M. -/
def ood_decS_near : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (d e e' : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (M : R → κ → E),
    HasDist G d → e' ≤ e → e + e' < d → DecodesTo G e' f M →
    ∀ ρ : Z.D, decS G e view Z f ρ (Z.val ρ (view M)) = .one (view M)

/-- Decoding undoes encoding, at every seed, under `HasDist G d`, for every radius e < d, with the
answers of M. -/
def ood_decS_mulVec : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (d e : ℕ)
      (view : (R → κ → E) → J → E) (Z : Sample E J) (M : R → κ → E),
    HasDist G d → e < d →
    ∀ ρ : Z.D, decS G e view Z (fun a => G.mulVec (M a)) ρ (Z.val ρ (view M)) = .one (view M)

/-- Derived tables. Suppose that in every column in which f is equal to the codewords of M, also f'
is equal to the codewords of M'. If f decodes to M then, outside the bad seeds of f' and with the
answers of M', the decoder returns the view of M' for f'. -/
def ood_decS_imp : Prop :=
  ∀ (E ι κ R R' J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R' → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (M : R → κ → E)
      (f' : R' → ι → E) (M' : R' → κ → E),
    DecodesTo G e f M → (∀ j, (∀ a, f a j = G.mulVec (M a) j) → ∀ b, f' b j = G.mulVec (M' b) j) →
    ∀ ρ : Z.D, ¬ ClashS G e view Z f' ρ → decS G e view Z f' ρ (Z.val ρ (view M')) = .one (view M')

/-- Sub-tables: any selection of rows. -/
def ood_decS_comp : Prop :=
  ∀ (E ι κ R R' J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (e : ℕ)
      (view : (R' → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (M : R → κ → E) (σ : R' → R),
    DecodesTo G e f M →
    ∀ ρ : Z.D, ¬ ClashS G e view Z (fun b => f (σ b)) ρ →
      decS G e view Z (fun b => f (σ b)) ρ (Z.val ρ (view fun b => M (σ b))) =
        .one (view fun b => M (σ b))

/-- Combinations of rows. -/
def ood_decS_combs : Prop :=
  ∀ (E ι κ R R' J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype R]
      (G : Matrix ι κ E) (e : ℕ) (view : (R' → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E)
      (M : R → κ → E) (c : R' → R → E),
    DecodesTo G e f M →
    ∀ ρ : Z.D, ¬ ClashS G e view Z (fun b => ∑ a, c b a • f a) ρ →
      decS G e view Z (fun b => ∑ a, c b a • f a) ρ (Z.val ρ (view fun b => ∑ a, c b a • M a)) =
        .one (view fun b => ∑ a, c b a • M a)

/-- The guard: under `HasDist G d`, for 2 e < d, the decoder returns "one u" if and only if the
table decodes, u is the view of `Blocks.dec`, and u has the answers; it never returns "several". -/
def ood_decS_unique : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
      (d e : ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E) (ρ : Z.D)
      (y : Z.S → E) (u : J → E),
    HasDist G d → 2 * e < d →
    (decS G e view Z f ρ y = .one u ↔ Decodes G e f ∧ view (dec G e f) = u ∧ Z.val ρ u = y) ∧
    decS G e view Z f ρ y ≠ .several

/-- The family: the list is at most the product of the lists of full messages. -/
def ood_list_fam : Prop :=
  ∀ (E A J : Type) (ι κ R : A → Type) [Field E] [Fintype A] [DecidableEq A] [∀ a, Fintype (ι a)]
      [∀ a, Fintype (κ a)] (G : ∀ a, Matrix (ι a) (κ a) E) (e : A → ℕ)
      (view : (∀ a, R a → κ a → E) → J → E) (f : ∀ a, R a → ι a → E) (L : A → ℕ),
    (∀ a, ListLE (DecodesTo (G a) (e a) (f a)) (L a)) → ListLE (InListFam G e view f) (∏ a, L a)

/-- The counting lemma for a family. -/
def ood_cnt_severalF : Prop :=
  ∀ (E A J : Type) (ι κ R : A → Type) [Field E] [Fintype A] [DecidableEq A] [∀ a, Fintype (ι a)]
      [∀ a, Fintype (κ a)] [Fintype J] (G : ∀ a, Matrix (ι a) (κ a) E) (e : A → ℕ)
      (view : (∀ a, R a → κ a → E) → J → E) (Z : Sample E J) (f : ∀ a, R a → ι a → E) (L : A → ℕ),
    (∀ a, ListLE (DecodesTo (G a) (e a) (f a)) (L a)) → Z.OK →
    cnt (fun ρ : Z.D => ∃ y, decF G e view Z f ρ y = .several) ≤ (∏ a, L a).choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ y, decF G e view Z f ρ y = .several) ≤ (∏ a, L a) ^ 2 * Z.err

/-- At a seed at which no answer gets the value "several", every candidate
is what the decoder of the family returns. -/
def ood_decF_good : Prop :=
  ∀ (E A J : Type) (ι κ R : A → Type) [Field E] [∀ a, Fintype (ι a)] [∀ a, Fintype (κ a)]
      [Fintype J] (G : ∀ a, Matrix (ι a) (κ a) E) (e : A → ℕ) (view : (∀ a, R a → κ a → E) → J → E)
      (Z : Sample E J) (f : ∀ a, R a → ι a → E) (ρ : Z.D),
    (¬ ∃ y, decF G e view Z f ρ y = .several) →
    ∀ (y : Z.S → E) (u : J → E),
      decF G e view Z f ρ y = .one u ↔
      (∃ M : ∀ a, R a → κ a → E, (∀ a, DecodesTo (G a) (e a) (f a) (M a)) ∧ view M = u) ∧
      Z.val ρ u = y

/-- The view "whole" loses nothing. -/
def ood_whole_inj : Prop := ∀ (E κ R : Type), Function.Injective (whole : (R → κ → E) → R × κ → E)

end Cb.Spec
