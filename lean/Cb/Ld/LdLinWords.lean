-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinWords.lean: the plain mathematics of the test for linear constraints on the encoded
index, beyond unique decoding: the rows that it leaves, the bad values of its three verifier
messages that are not seeds, their counts in the two regimes, the backward step, completeness.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinWordsProofs.lean. On vectors
and tables only: no protocol, no oracle type, no code but the index's generator matrix.

The setting (`LdLinW`: the data). X is an encoded index with a record (Cb/Ld/LdFoldEq.lean): a
table f with rows on the cube of v variables; U = `X.dec f rec` is the decoded index (message parts
of all rows, pads included), a function of the statement.
In standard terms: f is a received word for the interleaved linear code with generator matrix `X.G`;
a record is a seed of a linear sample map (`Sample`, Cb/Gen/OodDec.lean) with every row's answers;
`X.dec f rec` takes, among the tables of full messages whose message parts have these answers, one
whose codewords differ from f in the fewest columns (ties by `X.rank`), if these are at most `X.eM`,
and returns its message parts (`decMinS`, Cb/Gen/OodDecMin.lean). eq(γ, ·) is the multilinear
Lagrange kernel `Alg.eqk`, the extension of a vector on a cube its multilinear extension `Alg.mle`
(Alg/Mle.lean), and the fold at γ of a table the linear combination of its rows with the
coefficients eq(γ, r) (`foldAll`, Cb/Gen/FoldWords.lean).
The index matrix `D.mat U` has rows y : Y and columns c on the cube of v + klo variables: the first
v name the code row, the other klo a place in a block: entry (y, (r, j)) of the matrix = entry lay
(y, j) of the message part of the code row r. "lay" is the layout; pads and free places lie off its
range (so it is meant: no field and no hypothesis of this file asks it).
An instance claims one tensor row (`Claim`): ∑_(y, c) g[y] eq(ψ, c) mat[y, c] + rest = τ, "rest"
standing for its linear form on mask entries of the oracles that a preamble leaves.
The course, without the seeds and answers of the samples (these belong to the block that sends an
encoding). Each instance names w = gᵀ·mat; the verifier draws the shared point ψ* = (γ, ψlo), one
for all instances; the shared part names u = the fold at γ of the full messages of the code rows;
the verifier draws t locations Q of the encoded index; the shared part names ω = mat·eq(ψ*, ·); the
verifier draws ζ.

Main names:
The rows that are left (linear claims, which this test does not check itself: Limits), all linear
in (w, u, ω), all with public targets:
  `X.RecRow rec γ u`: the record's row on the folded row (Cb/Ld/LdFoldEq.lean); target: the folded
    answers.
  `ColR`: the codeword of u has, at each drawn location, the fold of the column read there.
  `FoldR`: the extension of ω at ζ is the extension at ζ of y ↦ ∑_j eq(ψlo, j) u_msg[lay (y, j)]
    (`omU`: ω is read off the message part of u, block by block).
  `Eval` (each instance): the extension of w at the instance's own ψ, plus rest, is τ.
  `Dot` (each instance): ⟨g, ω⟩ is the extension of w at ψ*.
The bad values:
  `BadPt U g w' ψ*` (depends on the instance), `BadZeta`.
  `BadSh`: the bad shared points for a batch: γ is bad for the fold (`X.Bad`, Cb/Ld/LdFoldEq.lean),
    or the index decodes and ψ* is bad for the w' of some instance.
  `BadLoc`: u' meets the record's row, is not "the fold of the decoded index" (`X.Wrong`), and yet
    meets `ColR` at Q.
w', u', ω' are any vectors that are fixed before the verifier's message is drawn (in the protocol:
what the prover's oracle messages decode to with their samples).
The statements (in `Cb.Spec`; the counts, `cnt` (Prob/Cnt.lean), are counts of values of one
verifier message; n = number of positions of the index, d a distance of its code, eM the radius at
which the encoded index is decoded, in columns, e' the radius at which the fold is tested):
  `ldLin_om_fold`: the identity behind `FoldR`: mat·eq(ψ*, ·) is read off the fold.
  `ldLin_complete`: the honest vectors meet all rows at every ψ*, Q, ζ, for every table of full
    messages that has the record's answers and of which the claim holds (`Eval` is then the claim
    itself: `ldLin_eval_iff`).
  `ldLin_cnt_pt`: at most (v + klo)·|E|^(v+klo-1) points ψ* have `BadPt`.
  `ldLin_cnt_sh`: first regime, at most N instances, under the hypotheses of its statement (f
    without a collision (`X.Coll`) at the record's seed; e' ≤ eM < distance; at most L tables of
    full messages within e' columns of f; `X.MCAeq e' bad`: every table has at most "bad"
    exceptional points γ; Cb/Ld/LdFoldEq.lean): at most
    (bad + L·v·|E|^(v-1))·|E|^klo + N·(v + klo)·|E|^(v+klo-1)
    of the |E|^(v+klo) points have `BadSh`: N(v + klo)/|E| plus the error of the fold.
  `ldLin_cnt_sh_far`: second regime (the index decodes, e' + eM below the distance): at most
    N·(v + klo)·|E|^(v+klo-1) points have `BadSh`: the second summand alone.
  `ldLin_cnt_loc`, `ldLin_cnt_loc_far`: at a γ that is not bad: at most (n - e' - 1)^t lists of
    locations have `BadLoc`; second regime (the index decodes), every γ: at most (n + eM - d)^t.
  `ldLin_cnt_zeta`: for an injective `D.py`: at most l·|E|^(l-1) values ζ have `BadZeta`.
  `ldLin_back`: the backward step: no bad value, and all rows true of any vectors w', u', ω': then
    the index decodes and the claim holds of the decoded index.


Of note in this test: the record's row; `X.Bad` in the shared point's round; "wrong" speaks of the
message part of u' only (a u' with the right message part and other randomness is harmless: later
rows read the message part); `BadZeta` compares ω' with what is read off u', not with the decoded
index; no case "the index does not decode"; cubes in the place of numbers, so that no order of bits
is fixed here.

Limits: this file says nothing on samples, collisions and lists of the oracle messages W, G_u, Ω
(the block that sends them), on the tests that close the rows, on splitting a row, on zero
knowledge. The rows are left, not tested. It says nothing on a bound on L or "bad".
The test follows this protocol's technical report, which follows the worked example named in
lean/CREDITS.md and the paper that this protocol builds on; for the shared point that report follows
Brakedown (GLSTW23) and TensorSwitch (BFRW25), and for the code switching that paper.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFoldEq

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

/-- The test for linear constraints on the encoded index, on vectors: the data. -/
structure LdLinW (E ι κ J Y : Type) where
  /-- the encoded index with its record -/
  X   : LdIx E ι κ J
  /-- the number of column variables inside a code row; the number of coordinates of ζ -/
  klo : ℕ
  l   : ℕ
  /-- the layout: where entry (y, j) of a code row's block stands in the message part -/
  lay : Y × (Fin klo → Bool) → J
  /-- the rows of the index matrix as vertices of a cube -/
  py  : Y → Fin l → Bool

namespace LdLinW
variable {E ι κ J Y : Type} (D : LdLinW E ι κ J Y)

/-- the column variables, the columns of the index matrix, the shared point -/
abbrev CV : Type := Fin D.X.v ⊕ Fin D.klo
abbrev Col : Type := D.CV → Bool
abbrev Pt (D : LdLinW E ι κ J Y) : Type := (Fin D.X.v → E) × (Fin D.klo → E)

/-- a point, as one vector of coordinates -/
def pt (ψ : D.Pt) : D.CV → E := Sum.elim ψ.1 ψ.2

/-- The index matrix that message parts hold. -/
def mat (U : D.X.Row × J → E) : Y → D.Col → E := fun y c =>
  U (fun i => c (Sum.inl i), D.lay (y, fun i => c (Sum.inr i)))

variable [Field E] [Fintype Y]

/-- The claim of an instance. -/
def Claim (U : D.X.Row × J → E) (g : Y → E) (ψ : D.Pt) (rest τ : E) : Prop :=
  ∑ y, ∑ c, g y * Alg.eqk (D.pt ψ) c * D.mat U y c + rest = τ

/-- w = gᵀ·mat;  ω = mat·eq(ψ, ·);  what is read off the message part of a folded row -/
def wOf (U : D.X.Row × J → E) (g : Y → E) : D.Col → E := fun c => ∑ y, g y * D.mat U y c
def omOf (U : D.X.Row × J → E) (ψ : D.Pt) : Y → E := fun y => ∑ c, Alg.eqk (D.pt ψ) c * D.mat U y c
def omU (um : J → E) (ψlo : Fin D.klo → E) : Y → E := fun y =>
  ∑ j, Alg.eqk ψlo j * um (D.lay (y, j))

/-- The rows that are left. -/
def Eval (ψ : D.Pt) (w : D.Col → E) (rest τ : E) : Prop := Alg.mle w (D.pt ψ) + rest = τ
def Dot (g ω : Y → E) (ψs : D.Pt) (w : D.Col → E) : Prop := ∑ y, g y * ω y = Alg.mle w (D.pt ψs)
def FoldR (ζ : Fin D.l → E) (ψlo : Fin D.klo → E) (um : J → E) (ω : Y → E) : Prop :=
  ∑ y, Alg.eqk ζ (D.py y) * ω y = ∑ y, Alg.eqk ζ (D.py y) * D.omU um ψlo y
def ColR [Fintype κ] {t : ℕ} (f : D.X.Row → ι → E) (γ : Fin D.X.v → E) (u : κ → E) (Q : Fin t → ι) :
    Prop :=
  ∀ i, D.X.G.mulVec u (Q i) = foldAll γ f (Q i)

/-- The shared point is bad for the w' of an instance. -/
def BadPt (U : D.X.Row × J → E) (g : Y → E) (w' : D.Col → E) (ψs : D.Pt) : Prop :=
  w' ≠ D.wOf U g ∧ Alg.mle w' (D.pt ψs) = Alg.mle (D.wOf U g) (D.pt ψs)

/-- ζ is bad for ω'. -/
def BadZeta (um : J → E) (ψlo : Fin D.klo → E) (ω' : Y → E) (ζ : Fin D.l → E) : Prop :=
  ω' ≠ D.omU um ψlo ∧ D.FoldR ζ ψlo um ω'

variable [Fintype ι] [Fintype κ] [Fintype J]

/-- The bad shared points of a batch; a c is (g, w') of the instance c (none: an empty slot, or an
oracle message that does not decode). -/
def BadSh {N : ℕ} (f : D.X.Row → ι → E) (rec : D.X.Rec) (e' : ℕ)
    (a : Fin N → Option ((Y → E) × (D.Col → E))) (ψs : D.Pt) : Prop :=
  D.X.Bad f rec e' ψs.1 ∨
  ∃ U, D.X.dec f rec = some U ∧ ∃ c gw, a c = some gw ∧ D.BadPt U gw.1 gw.2 ψs

/-- The bad lists of locations. -/
def BadLoc {t : ℕ} (f : D.X.Row → ι → E) (rec : D.X.Rec) (γ : Fin D.X.v → E)
    (u' : κ → E) (Q : Fin t → ι) : Prop :=
  D.X.RecRow rec γ u' ∧ D.X.Wrong f rec γ u' ∧ D.ColR f γ u' Q

end LdLinW

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The identity behind FoldR. -/
def ldLin_om_fold : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (U : D.X.Row × J → E) (ψs : D.Pt),
    D.omOf U ψs = D.omU (foldV ψs.1 U) ψs.2

/-- For w = gᵀ·mat the row Eval is the claim. -/
def ldLin_eval_iff : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (U : D.X.Row × J → E) (g : Y → E) (ψ : D.Pt) (rest τ : E),
    D.Eval ψ (D.wOf U g) rest τ ↔ D.Claim U g ψ rest τ

/-- Completeness, under the two hypotheses below: no exception. -/
def ldLin_complete : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (M : D.X.Row → κ → E) (rec : D.X.Rec) (g : Y → E) (ψ : D.Pt) (rest τ : E)
      (ψs : D.Pt) (t : ℕ) (Q : Fin t → ι) (ζ : Fin D.l → E),
    D.X.HasRec rec M → D.Claim (D.X.view M) g ψ rest τ →
    D.X.RecRow rec ψs.1 (foldAll ψs.1 M) ∧
    D.ColR (fun r => D.X.G.mulVec (M r)) ψs.1 (foldAll ψs.1 M) Q ∧
    D.FoldR ζ ψs.2 (D.X.msg (foldAll ψs.1 M)) (D.omOf (D.X.view M) ψs) ∧
    D.Eval ψ (D.wOf (D.X.view M) g) rest τ ∧
    D.Dot g (D.omOf (D.X.view M) ψs) ψs (D.wOf (D.X.view M) g)

/-- The draw of locations, first regime: at a γ that is not bad. -/
def ldLin_cnt_loc : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (e' t : ℕ) (f : D.X.Row → ι → E) (rec : D.X.Rec)
      (γ : Fin D.X.v → E) (u' : κ → E),
    ¬ D.X.Bad f rec e' γ → cnt (D.BadLoc (t := t) f rec γ u') ≤ (Fintype.card ι - e' - 1) ^ t

/-- The draw of locations, second regime: the index decodes; every γ. (not all hypotheses are named
here: see the statement below) -/
def ldLin_cnt_loc_far : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (d t : ℕ) (f : D.X.Row → ι → E) (rec : D.X.Rec)
      (γ : Fin D.X.v → E) (u' : κ → E),
    HasDist D.X.G d → D.X.dec f rec ≠ none →
    cnt (D.BadLoc (t := t) f rec γ u') ≤ (Fintype.card ι + D.X.eM - d) ^ t

/-- The backward step: no bad value (the first three hypotheses) and all rows (the other five) give
that the index decodes and the claim holds of the decoded index. -/
def ldLin_back : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (t : ℕ) (f : D.X.Row → ι → E) (rec : D.X.Rec) (g : Y → E)
      (ψ : D.Pt) (rest τ : E) (w' : D.Col → E) (ψs : D.Pt) (u' : κ → E) (Q : Fin t → ι)
      (ω' : Y → E) (ζ : Fin D.l → E),
    (∀ U, D.X.dec f rec = some U → ¬ D.BadPt U g w' ψs) → ¬ D.BadLoc f rec ψs.1 u' Q →
    ¬ D.BadZeta (D.X.msg u') ψs.2 ω' ζ → D.X.RecRow rec ψs.1 u' → D.ColR f ψs.1 u' Q →
    D.FoldR ζ ψs.2 (D.X.msg u') ω' → D.Eval ψ w' rest τ → D.Dot g ω' ψs w' →
    ∃ U, D.X.dec f rec = some U ∧ D.Claim U g ψ rest τ

variable [Fintype E]

def ldLin_cnt_pt : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (U : D.X.Row × J → E) (g : Y → E) (w' : D.Col → E),
    cnt (D.BadPt U g w') ≤ (D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1)

/-- The shared point's round, first regime, for at most N instances. -/
def ldLin_cnt_sh : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (d e' bad L N : ℕ) (f : D.X.Row → ι → E) (rec : D.X.Rec)
      (a : Fin N → Option ((Y → E) × (D.Col → E))),
    HasDist D.X.G d → D.X.eM < d → e' ≤ D.X.eM → D.X.MCAeq e' bad →
    ListLE (DecodesTo D.X.G e' f) L → ¬ D.X.Coll f rec.1 →
    cnt (D.BadSh f rec e' a) ≤
      (bad + L * (D.X.v * Fintype.card E ^ (D.X.v - 1))) * Fintype.card E ^ D.klo +
        N * ((D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1))

/-- The shared point's round, second regime. -/
def ldLin_cnt_sh_far : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (d e' N : ℕ) (f : D.X.Row → ι → E) (rec : D.X.Rec)
      (a : Fin N → Option ((Y → E) × (D.Col → E))),
    HasDist D.X.G d → e' + D.X.eM < d → D.X.dec f rec ≠ none →
    cnt (D.BadSh f rec e' a) ≤ N * ((D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1))

def ldLin_cnt_zeta : Prop :=
  ∀ (D : LdLinW E ι κ J Y) (um : J → E) (ψlo : Fin D.klo → E) (ω' : Y → E),
    Function.Injective D.py → cnt (D.BadZeta um ψlo ω') ≤ D.l * Fintype.card E ^ (D.l - 1)

end
end Spec
end Cb
