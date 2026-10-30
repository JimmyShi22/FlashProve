-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FoldWords.lean: folding tables of words along their row variables: definitions, and the
statements on decoding that carry the errors of the two folding protocols. Plain mathematics: no
protocol, no oracle, no game. The proofs are in Cb/Gen/FoldWordsProofs.lean.

In standard terms: the rows of an interleaved word are combined with the coefficients eq(γ, ·), as
in a proximity test for a linear code. The statements say, under the hypotheses below, that this
commutes with decoding (`Spec.decodesTo_foldAll`, `Spec.dec_foldAll`), and that a word that does
not decode keeps a combination that does not decode, but for a bounded number of γ
(`Spec.cnt_foldAll`).
A table has one row for each vertex of a cube (Fin k → Bool); a row is a word (a function on the
positions ι) or a message (a function on the coordinates κ of the generator matrix G), or any
vector.

Main names:
  `foldAll γ f`: in standard terms, the multilinear extension of the table, in its row index, at γ.
  `rep em f`: with it, for an injective em, tables with fewer row variables take part in a folding
    with more challenges: they use the challenges at the range of em only (`Spec.foldAll_rep`), and
    they decode exactly if f does (`Spec.decodes_rep_iff`).
  `FoldClean`: no step of the folding at γ turns a table that does not decode into one that decodes.
    The values that are not clean at a step are those counted by `Spec.cnt_fold1`.
"Decodes", "decodes to", "dec" are those of Blocks/Decode.lean: all rows agree with codewords
outside at most e common positions (the distance of interleaved words); a codeword is the image of
any vector under G. Errors are counts of values of the verifier's message; "bad" is the count of
`Code.MCA` (mutual correlated agreement on lines) for the range of G at the radius e; q is the
number of elements of E.

Limits: the statements say nothing on the size of "bad" (Code/Third.lean, Code/Half.lean,
Code/Circle.lean); nothing on protocols.
The notions follow definitions and lemmas of the paper that this protocol builds on
(lean/CREDITS.md); the counts come from Code/Derived.lean and Blocks/Decode.lean.

Terms: lean/GLOSSARY.md.
-/
import Blocks.Decode
import Alg.Mle
import Alg.Poly

set_option autoImplicit false

namespace Cb
open Prob Blocks

section Defs
variable {E : Type} [Field E]

/-- The first row variable is folded at x. -/
def fold1 {V : Type} [AddCommGroup V] [Module E V] {k : ℕ} (x : E) (f : (Fin (k + 1) → Bool) → V) :
    (Fin k → Bool) → V :=
  fun v => (1 - x) • f (Fin.cons false v) + x • f (Fin.cons true v)

/-- All row variables are folded at γ.  The variables may be indexed by any finite set. -/
def foldAll {V : Type} [AddCommGroup V] [Module E V] {N : Type} [Fintype N] [DecidableEq N]
    (γ : N → E) (f : (N → Bool) → V) : V :=
  ∑ v, Alg.eqk γ v • f v

/-- Rows repeated over the variables outside the range of e. -/
def rep {V N N' : Type} (e : N → N') (f : (N → Bool) → V) : (N' → Bool) → V := fun b =>
  f fun v => b (e v)

/-- ⟨u, v⟩. -/
def dot {κ : Type} [Fintype κ] (u v : κ → E) : E := ∑ c, u c * v c

/-- ∑_b ⟨L[b], m[b]⟩: a linear form L on a table m of messages. -/
def pair {N κ : Type} [Fintype N] [DecidableEq N] [Fintype κ] (L m : (N → Bool) → κ → E) : E :=
  ∑ b, dot (L b) (m b)

/-- The summand of the folding's sumcheck. -/
def summand {N κ : Type} [Fintype N] [DecidableEq N] [Fintype κ]
    (L m : (N → Bool) → κ → E) (z : N → E) : E :=
  dot (foldAll z L) (foldAll z m)

/-- No step of the folding at γ turns a table that does not decode into one that decodes. -/
def FoldClean {ι κ : Type} [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ) :
    {k : ℕ} → (Fin k → E) → ((Fin k → Bool) → ι → E) → Prop
  | 0, _, _ => True
  | _ + 1, γ, f =>
    (Decodes G e (fold1 (γ 0) f) → Decodes G e f) ∧ FoldClean G e (Fin.tail γ) (fold1 (γ 0) f)

end Defs

namespace Spec

/-- Folding all variables is folding the first and then the others. -/
def foldAll_cons : Prop :=
  ∀ (E : Type) [Field E] (V : Type) [AddCommGroup V] [Module E V] (k : ℕ) (x : E)
      (γ : Fin k → E) (f : (Fin (k + 1) → Bool) → V),
    foldAll (Fin.cons x γ : Fin (k + 1) → E) f = foldAll γ (fold1 x f)

/-- With no variable there is one row, and nothing is folded. -/
def foldAll_zero : Prop :=
  ∀ (E : Type) [Field E] (V : Type) [AddCommGroup V] [Module E V] (γ : Fin 0 → E)
      (f : (Fin 0 → Bool) → V) (b : Fin 0 → Bool),
    foldAll γ f = f b

/-- A fold of a table that decodes decodes to the fold of the messages. -/
def decodesTo_fold1 : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e k : ℕ) (x : E)
      (f : (Fin (k + 1) → Bool) → ι → E) (M : (Fin (k + 1) → Bool) → κ → E),
    DecodesTo G e f M → DecodesTo G e (fold1 x f) (fold1 x M)

/-- Decoding commutes with one step of folding, within unique decoding, for a table that decodes. -/
def dec_fold1 : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e k : ℕ)
      (x : E) (f : (Fin (k + 1) → Bool) → ι → E),
    HasDist G d → 2 * e < d → Decodes G e f →
    Decodes G e (fold1 x f) ∧ dec G e (fold1 x f) = fold1 x (dec G e f)

/-- If `Code.MCA` holds of the range of G at e with the count bad, a table that does not decode
folds to one that decodes for at most "bad" values. -/
def cnt_fold1 : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E)
      (e bad k : ℕ) (f : (Fin (k + 1) → Bool) → ι → E),
    Code.MCA (LinearMap.range G.mulVecLin) e bad → ¬ Decodes G e f →
    cnt (fun x : E => Decodes G e (fold1 x f)) ≤ bad

def decodesTo_foldAll : Prop :=
  ∀ (E ι κ N : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype N] [DecidableEq N]
      (G : Matrix ι κ E) (e : ℕ) (γ : N → E) (f : (N → Bool) → ι → E) (M : (N → Bool) → κ → E),
    DecodesTo G e f M → DecodesTo G e (fun _ : Unit => foldAll γ f) (fun _ => foldAll γ M)

/-- Decoding commutes with folding, within unique decoding, for a table that decodes. -/
def dec_foldAll : Prop :=
  ∀ (E ι κ N : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype N] [DecidableEq N]
      (G : Matrix ι κ E) (d e : ℕ) (γ : N → E) (f : (N → Bool) → ι → E),
    HasDist G d → 2 * e < d → Decodes G e f →
    Decodes G e (fun _ : Unit => foldAll γ f) ∧
    dec G e (fun _ : Unit => foldAll γ f) () = foldAll γ (dec G e f)

/-- The equality generator (the coefficients eq(γ, ·)): if `Code.MCA` holds of the range of G at e
with the count bad, a table that does not decode has a full fold that decodes for at most
k · bad · q^(k-1) points. -/
def cnt_foldAll : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E)
      (e bad k : ℕ) (f : (Fin k → Bool) → ι → E),
    Code.MCA (LinearMap.range G.mulVecLin) e bad → ¬ Decodes G e f →
    cnt (fun γ : Fin k → E => Decodes G e fun _ : Unit => foldAll γ f) ≤
      k * bad * Fintype.card E ^ (k - 1)

/-- The backward step of the folding: at a clean γ, if the full fold decodes, so does the table. -/
def decodes_of_clean : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e k : ℕ)
      (γ : Fin k → E) (f : (Fin k → Bool) → ι → E),
    FoldClean G e γ f → Decodes G e (fun _ : Unit => foldAll γ f) → Decodes G e f

/-- The summand has degree at most 2 in each variable. -/
def degLE_summand : Prop :=
  ∀ (E N κ : Type) [Field E] [Fintype N] [DecidableEq N] [Fintype κ] (L m : (N → Bool) → κ → E),
    Alg.DegLE (fun _ => 2) (summand L m)

/-- Over the cube the summand sums to the form at the table. -/
def sum_summand : Prop :=
  ∀ (E N κ : Type) [Field E] [Fintype N] [DecidableEq N] [Fintype κ] (L m : (N → Bool) → κ → E),
    ∑ b : N → Bool, summand L m (Alg.corner b) = pair L m

/-- For an injective em, a table with repeated rows decodes exactly if the table does. -/
def decodes_rep_iff : Prop :=
  ∀ (E ι κ N N' : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ)
      (em : N → N') (f : (N → Bool) → ι → E),
    Function.Injective em → (Decodes G e (rep em f) ↔ Decodes G e f)

/-- The messages of a table with repeated rows are the messages of the table, repeated: within
unique decoding, for a table that decodes. -/
def dec_rep : Prop :=
  ∀ (E ι κ N N' : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e : ℕ)
      (em : N → N') (f : (N → Bool) → ι → E),
    HasDist G d → 2 * e < d → Decodes G e f → dec G e (rep em f) = rep em (dec G e f)

/-- For an injective em, the fold of a table with repeated rows is the fold of the table at the
challenges of its own variables. -/
def foldAll_rep : Prop :=
  ∀ (E V N N' : Type) [Field E] [AddCommGroup V] [Module E V] [Fintype N] [DecidableEq N]
      [Fintype N'] [DecidableEq N'] (em : N → N') (γ : N' → E) (f : (N → Bool) → V),
    Function.Injective em → foldAll γ (rep em f) = foldAll (fun v => γ (em v)) f

/-- For an injective em, the pairing of two tables with repeated rows is the pairing of the tables,
once for each repetition. -/
def pair_rep : Prop :=
  ∀ (E κ N N' : Type) [Field E] [Fintype κ] [Fintype N] [DecidableEq N] [Fintype N']
      [DecidableEq N'] (em : N → N') (L m : (N → Bool) → κ → E),
    Function.Injective em →
    pair (rep em L) (rep em m) = (2 : E) ^ (Fintype.card N' - Fintype.card N) * pair L m

end Spec
end Cb
