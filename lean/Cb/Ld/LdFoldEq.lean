-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFoldEq.lean: decoding commutes with the fold of the encoded index, beyond unique decoding,
at all but a counted number of points γ, under the hypotheses of the statements; the record's row on
the folded row.

In words: a table of words is folded into one word, the combination of its rows under the
coefficients eq(γ, ·) of a point γ. The main statements (`ldFe_cnt`, `ldFe_none`) bound, each under
its hypotheses, the number of points γ (the bad points, `X.Bad`) at which some codeword is within e'
positions of the folded word and has the record's folded answers, while the table does not decode or
the codeword's message part is not the fold of what the table decodes to. In `ldFe_cnt` the radii
may be, and need not be, beyond half the distance: the table is decoded with a record, the answers
to a sample.
Definitions and statements (`Cb.Spec`); the proofs are in Cb/Ld/LdFoldEqProofs.lean. Plain
mathematics on tables of words: no protocol, no oracle, no game; nothing is sent.

The setting (`LdIx`: the data). An encoded index is a table f with one row for each vertex r of a
cube (Fin v → Bool), under one generator matrix G (positions ι, coordinates κ of a full message:
message, pads and encoding randomness together).
  pl: the places of the message (pads included) in a full message.
  Z: the sample map of one row (Cb/Gen/OodDec.lean: seeds, names S of the answers, a matrix for each
    seed). Any sample map: no answer at all (`Sample.nil`), the row with a pad (`Sample.pad`),
    several answers.
  eM: the radius at which the encoded index is decoded, in columns (a column is off if some row of f
    differs there from its codeword: `Off`, Blocks/Decode.lean).
A record (`X.Rec`) is a seed and, for each row r, the answers y (r, ·). With Z = `Sample.nil` a
record holds nothing.
  `X.Coll f ρ`, collision: two tables of full messages within eM columns of f have different message
    parts and the same answers at the seed ρ (`Cb.Ood.ClashS`). It does not mention the answers of
    the record.
  `X.dec f rec`, the decoded index: the message part of the nearest table of codewords among those
    that have the record's answers, if it is within eM; else none (`Cb.Ood.decMinS`).
The fold. For γ in E^v the folded word is `foldAll γ f` = ∑_r eq(γ, r) f[r] (Cb/Gen/FoldWords.lean);
a symbol of it is computed from one column of f. Messages fold in the same way (`foldV`,
Cb/Ld/LdRel.lean, on message parts).
  `X.tgt rec γ`: the folded answers ∑_r eq(γ, r) y (r, ·): a public function of the record and of γ.
  `X.RecRow rec γ u`, the record's row on the folded row: the sample of the message part of the one
    full message u, at the record's seed, is the folded answers. As many rows as a row of the index
    has answers.
  `X.Exc f e' γ`: γ is exceptional for f: on some set of all but at most e' positions the folded
    word agrees with a codeword while some row of f does not.
  `X.MCAeq e' bad`: every table has at most "bad" exceptional points γ, of the |E|^v: an abstract
    number of the code at the radius e'.

The two regimes of the main statements. First: no collision at the record's seed, and e' ≤ eM below
the distance. Second: the index decodes, and e' + eM is below the distance.

Main names, all in `Cb.Spec`; d is a distance of G (`HasDist X.G d`), n the number of positions:
  `ldFe_cnt` (first regime): f without a collision at the record's seed, e' ≤ eM < distance,
    `X.MCAeq e' bad`, at most L tables of full messages within e' columns of f: #{γ : X.Bad f rec e'
    γ} ≤ bad + L · v · |E|^(v-1). As a probability: bad/|E|^v + L v/|E|. The index may or may not
    decode: one case.
  `ldFe_none` (second regime): the index decodes and e' + eM < distance: no γ is bad.

  `ldFe_loc`, `ldFe_loc_far`: what a draw of locations then costs. Let u be fixed before t positions
    are drawn, meet the record's row and not be "the fold of the decoded index". At a γ that is not
    bad: the codeword of u equals the folded word at all t drawn positions for at most
    (n - e' - 1)^t lists. If the index decodes (second regime), at every γ: at most (n + eM - d)^t
    lists.

Notation: `HasDist G d` (a proposition; Blocks/Decode.lean): every non-zero message has a codeword
with at least d non-zero symbols; `DecodesTo G e f M` (a proposition; Blocks/Decode.lean), "within e
columns": at most e columns are off; `ListLE` (Cb/Gen/OodDec.lean).

Limits: no bound on L or on "bad" is proved or assumed here: they are hypotheses, in the statements'
own text. A bound that reaches |E|^v says nothing. This file says nothing on how often a collision
occurs (Cb/Gen/OodDec*.lean), but for `ldFe_unique`: none for 2 eM below the distance. It says
nothing on hiding, on protocols. At a collision nothing is claimed by `ldFe_cnt`, `ldFe_cnt_nil`;
the other statements do not ask whether there is one.
DECLARED DIFFERENCES to this protocol's technical report. (a) Distances are counts: the radius
is the integer part of δ·n; (n - e' - 1)/n < 1 - δ'. (b) The table is any table over E; in the
protocol its symbols lie in the small field. (c) L counts tables of full messages (for a positive
distance: codewords of the interleaved code). (d) (No difference.) ldFe_none and ldFe_far do not ask
for 2 eM < distance: under their other hypotheses `ldFe_none` holds as soon as e' + eM is below the
distance, `ldFe_far` at every e₀ (its bound is below n - e' as soon as e' + e₀ is below the
distance); the technical report's lemma does not ask it either: it says only that this case
is of use within unique decoding. (e) Running times are not modelled.

What this file takes from Cb/Gen/FoldWords.lean and Code/Derived.lean:
`foldAll` and its laws; `Code.Bad`, the count for the generator eq(γ, ·) and, of "what not bad
gives", `Code.mem_agreeOn_of_not_bad` (all three hold at every radius); the count of agreements of a
wrong codeword.


Terms: lean/GLOSSARY.md.

The lemma follows this protocol's technical report, which follows Brakedown (GLSTW23); samples and
records follow advice, and the decoder follows the worked example named in lean/CREDITS.md.  The
count ldFe_mca_sum has the shape of a second lemma of that report, which follows (AER24) as (DG24)
restates it; the two proofs were not held side by side.
-/
import Cb.Gen.OodDecMin
import Cb.Gen.OodDecPad
import Cb.Gen.CodeErase
import Cb.Gen.FoldWords
import Cb.Ld.LdRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

/-- An encoded index with a record: the data. -/
structure LdIx (E ι κ J : Type) where
  /-- the number of row variables -/
  v : ℕ
  /-- the generator matrix of a row -/
  G : Matrix ι κ E
  /-- the places of the message (pads included) in a full message -/
  pl : J → κ
  /-- the sample map of one row -/
  Z : Sample E J
  /-- the radius of decoding, in columns -/
  eM : ℕ
  /-- a number for each table of full messages, by which the decoder orders those at equal
  distance -/
  rank : ((Fin v → Bool) → κ → E) → ℕ

namespace LdIx
variable {E ι κ J : Type} (X : LdIx E ι κ J)

/-- the rows -/
abbrev Row : Type := Fin X.v → Bool

/-- the message part of a full message, and of a table of full messages -/
def msg (u : κ → E) : J → E := fun j => u (X.pl j)
def view (M : X.Row → κ → E) : X.Row × J → E := fun n => M n.1 (X.pl n.2)

variable [Field E]

/-- one sample for each row, with the same seed -/
abbrev ZR : Sample E (X.Row × J) := X.Z.rows X.Row

/-- A record: a seed, and the answers of every row. -/
abbrev Rec : Type := X.Z.D × (X.Row × X.Z.S → E)

/-- The folded answers. -/
def tgt (rec : X.Rec) (γ : Fin X.v → E) : X.Z.S → E := fun s => ∑ r, Alg.eqk γ r * rec.2 (r, s)

variable [Fintype J]

/-- The record's row on the folded row. -/
def RecRow (rec : X.Rec) (γ : Fin X.v → E) (u : κ → E) : Prop :=
  X.Z.val rec.1 (X.msg u) = X.tgt rec γ

/-- The table M of full messages has the record's answers. -/
def HasRec (rec : X.Rec) (M : X.Row → κ → E) : Prop := X.ZR.val rec.1 (X.view M) = rec.2

variable [Fintype ι] [Fintype κ]

/-- Collision at a seed. -/
def Coll (f : X.Row → ι → E) (ρ : X.Z.D) : Prop := ClashS X.G X.eM X.view X.ZR f ρ

/-- The decoded index: a function of the table and the record. -/
def dec (f : X.Row → ι → E) (rec : X.Rec) : Option (X.Row × J → E) :=
  decMinS X.G X.eM X.rank X.view X.ZR f rec.1 rec.2

/-- The codeword of u is within e' positions of the word w. -/
def NearW (e' : ℕ) (w : ι → E) (u : κ → E) : Prop := cnt (fun j => w j ≠ X.G.mulVec u j) ≤ e'

/-- u is not "the fold of the decoded index": the index does not decode, or the message part of u is
another vector. -/
def Wrong (f : X.Row → ι → E) (rec : X.Rec) (γ : Fin X.v → E) (u : κ → E) : Prop :=
  ∀ U, X.dec f rec = some U → X.msg u ≠ foldV γ U

/-- The bad points of the fold. -/
def Bad (f : X.Row → ι → E) (rec : X.Rec) (e' : ℕ) (γ : Fin X.v → E) : Prop :=
  ∃ u : κ → E, X.NearW e' (foldAll γ f) u ∧ X.RecRow rec γ u ∧ X.Wrong f rec γ u

/-- The exceptional points: mutual correlated agreement fails for the coefficients eq(γ, ·). -/
def Exc (f : X.Row → ι → E) (e' : ℕ) (γ : Fin X.v → E) : Prop :=
  Code.Bad (LinearMap.range X.G.mulVecLin) e' (Alg.eqk γ) fun r (_ : Unit) => f r

/-- The agreement error for the generator eq(γ, ·), as a count of points. -/
def MCAeq [Finite E] (e' bad : ℕ) : Prop := ∀ f : X.Row → ι → E, cnt (X.Exc f e') ≤ bad

end LdIx

namespace Spec
section
variable (E ι κ J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J]

/-- If M has the record's answers, the record's row holds of the fold of M, at every point. (What
the honest prover needs.) -/
def ldFe_rec_fold : Prop :=
  ∀ (X : LdIx E ι κ J) (rec : X.Rec) (M : X.Row → κ → E),
    X.HasRec rec M → ∀ γ, X.RecRow rec γ (foldAll γ M)

/-- The message part of a fold is the fold of the message parts. -/
def ldFe_msg_fold : Prop :=
  ∀ (X : LdIx E ι κ J) (M : X.Row → κ → E) (γ : Fin X.v → E),
    X.msg (foldAll γ M) = foldV γ (X.view M)

/-- At a point that is not exceptional, for e' below the distance, whatever is near the folded word
is the fold of a member of the list, which erasure correction on the agreement set returns. Nothing
is decoded from errors. -/
def ldFe_lift : Prop :=
  ∀ (X : LdIx E ι κ J) (d e' : ℕ) (f : X.Row → ι → E) (γ : Fin X.v → E) (u : κ → E), HasDist X.G d →
    e' < d → ¬ X.Exc f e' γ → X.NearW e' (foldAll γ f) u →
    ∃ M,
      erase? X.G d (agr X.G (fun _ : Unit => foldAll γ f) fun _ => u) f = some M ∧
      DecodesTo X.G e' f M ∧
      foldAll γ M = u

/-- (Second regime.) For f within e₀ columns of the codewords of M, a codeword other than that of
the fold of M agrees with the folded word at no more than n - d + e₀ positions, d a distance of G
and n the number of positions, at every point. -/
def ldFe_far : Prop :=
  ∀ (X : LdIx E ι κ J) (d e₀ : ℕ) (f : X.Row → ι → E) (M : X.Row → κ → E)
      (γ : Fin X.v → E) (u : κ → E),
    HasDist X.G d → DecodesTo X.G e₀ f M → u ≠ foldAll γ M →
    cnt (fun j => X.G.mulVec u j = foldAll γ f j) + d ≤ Fintype.card ι + e₀

/-- (Second regime.) The index decodes, and the two radii together are below the distance: no point
is bad. -/
def ldFe_none : Prop :=
  ∀ (X : LdIx E ι κ J) (d e' : ℕ) (f : X.Row → ι → E) (rec : X.Rec),
    HasDist X.G d → e' + X.eM < d → X.dec f rec ≠ none → ∀ γ, ¬ X.Bad f rec e' γ

/-- The draw of locations, first regime: at a point that is not bad, for u that meets the record's
row and is not "the fold of the decoded index". -/
def ldFe_loc : Prop :=
  ∀ (X : LdIx E ι κ J) (e' t : ℕ) (f : X.Row → ι → E) (rec : X.Rec) (γ : Fin X.v → E) (u : κ → E),
    ¬ X.Bad f rec e' γ → X.RecRow rec γ u → X.Wrong f rec γ u →
    cnt (fun Q : Fin t → ι => ∀ i, X.G.mulVec u (Q i) = foldAll γ f (Q i)) ≤
      (Fintype.card ι - e' - 1) ^ t

/-- The draw of locations, second regime (the index decodes): at every point, d a distance of G, for
u that is not "the fold of the decoded index". -/
def ldFe_loc_far : Prop :=
  ∀ (X : LdIx E ι κ J) (d t : ℕ) (f : X.Row → ι → E) (rec : X.Rec) (γ : Fin X.v → E) (u : κ → E),
    HasDist X.G d → X.dec f rec ≠ none → X.Wrong f rec γ u →
    cnt (fun Q : Fin t → ι => ∀ i, X.G.mulVec u (Q i) = foldAll γ f (Q i)) ≤
      (Fintype.card ι + X.eM - d) ^ t

/-- The guard: for the table of the codewords of M with its true record, eM below the distance: the
index decodes to the message part of M, at every seed. -/
def ldFe_honest : Prop :=
  ∀ (X : LdIx E ι κ J) (d : ℕ) (M : X.Row → κ → E) (ρ : X.Z.D), HasDist X.G d → X.eM < d →
    X.dec (fun r => X.G.mulVec (M r)) (ρ, X.ZR.val ρ (X.view M)) = some (X.view M)

/-- The guard: within unique decoding (2 eM below the distance) the decoded index is that of
`Blocks.dec`, with the record as a further test, and no seed has a collision. -/
def ldFe_unique : Prop :=
  ∀ (X : LdIx E ι κ J) (d : ℕ) (f : X.Row → ι → E) (rec : X.Rec) (U : X.Row × J → E),
    HasDist X.G d → 2 * X.eM < d →
    (X.dec f rec = some U ↔
      Decodes X.G X.eM f ∧ X.view (Blocks.dec X.G X.eM f) = U ∧ X.ZR.val rec.1 U = rec.2) ∧
    ¬ X.Coll f rec.1

variable [Fintype E]

/-- (First regime.) The number of bad points, for a table without a collision at the record's seed.
(not all hypotheses are named here: see the statement below) -/
def ldFe_cnt : Prop :=
  ∀ (X : LdIx E ι κ J) (d e' bad L : ℕ) (f : X.Row → ι → E) (rec : X.Rec), HasDist X.G d →
    X.eM < d → e' ≤ X.eM → X.MCAeq e' bad → ListLE (DecodesTo X.G e' f) L → ¬ X.Coll f rec.1 →
    cnt (X.Bad f rec e') ≤ bad + L * (X.v * Fintype.card E ^ (X.v - 1))

/-- The same with no answers in a record: the exceptional points alone.
(not all hypotheses are named here: see the statement below) -/
def ldFe_cnt_nil : Prop :=
  ∀ (X : LdIx E ι κ J) (d e' bad : ℕ) (f : X.Row → ι → E) (rec : X.Rec), IsEmpty X.Z.S →
    HasDist X.G d → X.eM < d → e' ≤ X.eM → X.MCAeq e' bad →
    ¬ X.Coll f rec.1 → cnt (X.Bad f rec e') ≤ bad

/-- The agreement error for eq(γ, ·) is at most the sum of the errors for lines over the steps of
the fold; c j is the count for lines of tables with 2^j rows; as counts: the sum of the c j, j < v,
times |E|^(v-1). At every radius. -/
def ldFe_mca_sum : Prop :=
  ∀ (X : LdIx E ι κ J) (e' : ℕ) (c : ℕ → ℕ),
    (∀ j < X.v, Code.MCAFor (LinearMap.range X.G.mulVecLin) e' ((Fin j → Bool) × Unit) (c j)) →
    X.MCAeq e' ((∑ j ∈ Finset.range X.v, c j) * Fintype.card E ^ (X.v - 1))

end
end Spec
end Cb
