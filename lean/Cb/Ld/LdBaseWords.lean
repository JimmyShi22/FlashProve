-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseWords.lean: the base case "with lists", on words: definitions, and the statements that
carry its two errors, its backward step, its completeness and its honest-verifier zero knowledge;
and the agreement bound below a third of the distance.

The base case is that of the proximity test beyond unique decoding (Cb/Ld/LdBase.lean); "with
lists": its first error counts a list (`ldw_cnt_bad1`).
Plain linear algebra and counting: no protocol, no oracle, no game, no particular code. The proofs
are in Cb/Ld/LdBaseWordsProofs.lean and Cb/Ld/LdBaseThird.lean.

The setting. E is a finite field; W is the space of what is encoded (message and encoding randomness
together); P is the finite set of the positions at which the verifier reads, Y the space of the
symbols that it reads there; cw : W → P → Y is linear: "encode, then read through the verifier's
transformation of the oracle". A word is any function P → Y. Distance counts positions of P. Nothing
else is known of cw: one code, interleaved rows, a group of codes of different lengths read under a
repetition are all instances. f is the word of which a claim is made, L a linear form on W, tg its
claimed value, e any radius (a number of positions).
The claim, relaxed (`LdwIn`, a relation between f and M): f is near cw M at the radius e, and L M =
tg. M is the claim's witness: there is no decoder, and a word may have several such M.
The test. The prover names a second word g (honest: cw h for uniform h) and a scalar u (honest: L
h); the verifier draws μ; the prover names ms in W, in full (honest: h + μ m); the verifier draws a
list Q of t positions and accepts (`LdwAccept`) if L ms = u + μ tg and cw ms = g + μ f at every
position of Q.

Main names (each a `Prop` in `Cb.Spec`). That cw is linear (`LdwLin`) and L a linear form
(`LdwForm`) are premises of `ldw_back`, `ldw_complete`, `ldw_law`; that cw is linear, of
`ldw_third`, `ldw_third_fold`.
  `ldw_cnt_bad1`: the first error: at most `bad` + `L2` values μ are bad (`LdwBad1`), under the
    hypotheses of its statement.
  `ldw_cnt_bad2`: the second error: at most (N - e - 1)^t lists Q are bad (`LdwBad2`), N the number
    of positions.
  `ldw_back`: the backward step. Let S be the largest set on which g + μ f agrees with cw ms. If μ
    and Q are not bad and the verifier accepts, then f is on the code on S, and every M whose word
    agrees with f on S is a witness of the relaxed claim. So "correct the erasures of f outside S"
    is an extractor, whichever corrector is used. No condition on e, on distances or on lists.
  `ldw_unique`: if the code is D apart and S misses fewer than D positions, all M that agree with f
    on S have the same word: below the distance a corrector has no choice of the corrected word (and
    none of M, if cw is injective).
  `ldw_complete`: if f = cw m and L m = tg, the honest answers are accepted, for every μ and Q.
  `ldw_law`: if L m = tg, what the honest prover shows, (u, ms, all of g), has over uniform h the
    law of: ms uniform, u := L ms - μ tg, g := cw ms - μ cw m. Under the hypotheses of its
    statement: so u and ms give away nothing, and a position of g gives away the same position of f
    = cw m and nothing else.
  `ldw_third`: agreement below a third of the distance, nothing assumed beyond the hypotheses of the
    statements: if the code is D apart and 3 e < D, every line has at most e + 1 exceptional values.
    `ldw_third_fold`: the same for the lines (1 - μ) g + μ f.

Limits: the statements say nothing on the sizes of bad and L2 beyond a third of the distance, nor
that bad + L2 is below the number of values of μ; nothing on the size of L2 at any radius; nothing
on protocols (Cb/Ld/LdBase.lean).
DECLARED DIFFERENCES to the paper that this protocol builds on (lean/CREDITS.md). (1) There: a
finite ring, modules, a challenge set in the centre (for the agreement bound: with invertible
differences); here: a field E, and μ from all of E. So "two different polynomials of degree at most
one agree" costs one value of μ. (2) There the form reads the message part of W only; here any
linear form on W. (3) There the radius is below the distance, because the corrector of erasures
gives no result otherwise; here the backward step needs no such condition, and that condition is
what makes the corrected word unique (`ldw_unique`). (4) There the witness of the relaxed claim also
holds the corrected word; here that word is cw M and is not written. (5) There lists and agreement
errors are maxima over all words that come from native words; here the two counts are hypotheses on
the words g, f at hand. (6) There a list holds codewords, and one passes to (message, randomness) by
the injectivity of the encoder; here a list holds elements of W: the same number if cw is injective,
and never fewer.

Terms: lean/GLOSSARY.md.
-/
import Prob.LawKit
import Prob.Count
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Field.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob

section Defs
variable {E W Y P : Type} [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y]

/-- cw is linear. -/
def LdwLin (cw : W → P → Y) : Prop :=
  ∀ (a b : W) (μ : E) (x : P), cw (a + μ • b) x = cw a x + μ • cw b x

/-- L is a linear form. -/
def LdwForm (L : W → E) : Prop := ∀ (a b : W) (μ : E), L (a + μ • b) = L a + μ * L b

omit [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
/-- Some word of the code agrees with f on S. -/
def LdwOn (cw : W → P → Y) (f : P → Y) (S : Finset P) : Prop := ∃ M, ∀ x ∈ S, f x = cw M x

variable [Fintype P]

omit [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
/-- f differs from the word of M at no more than e positions. -/
def LdwNear (cw : W → P → Y) (e : ℕ) (f : P → Y) (M : W) : Prop := cnt (fun x => f x ≠ cw M x) ≤ e

omit [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
/-- (Mg, Mf) is in the list of the pair (g, f): no more than e positions at which g or f is off. -/
def LdwNear2 (cw : W → P → Y) (e : ℕ) (g f : P → Y) (Mg Mf : W) : Prop :=
  cnt (fun x => g x ≠ cw Mg x ∨ f x ≠ cw Mf x) ≤ e

omit [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
open Classical in
/-- The largest set on which f agrees with the word of M. -/
def ldwAgree (cw : W → P → Y) (f : P → Y) (M : W) : Finset P :=
  Finset.univ.filter fun x => f x = cw M x

omit [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
/-- Two different words of the code differ at D positions or more (the distance of the image of cw;
cw need not be injective). -/
def LdwApart (cw : W → P → Y) (D : ℕ) : Prop :=
  ∀ M M' : W, cw M ≠ cw M' → D ≤ cnt fun x => cw M x ≠ cw M' x

omit [AddCommGroup W] [Module E W] in
/-- μ is exceptional for the line g + μ f: on some set that misses at most e positions the line is
on the code while g and f are not both (the event of mutual correlated agreement). -/
def LdwExc (cw : W → P → Y) (e : ℕ) (g f : P → Y) (μ : E) : Prop :=
  ∃ S : Finset P,
    Fintype.card P ≤ S.card + e ∧
    LdwOn cw (fun x => g x + μ • f x) S ∧
    ¬ (LdwOn cw g S ∧ LdwOn cw f S)

omit [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y] in
/-- The relaxed claim, with its witness M. -/
def LdwIn (cw : W → P → Y) (e : ℕ) (L : W → E) (tg : E) (f : P → Y) (M : W) : Prop :=
  LdwNear cw e f M ∧ L M = tg

omit [AddCommGroup W] [Module E W] [Fintype P] in
/-- The verifier's decision. -/
def LdwAccept (cw : W → P → Y) (L : W → E) (tg : E) (f g : P → Y) (u μ : E) (ms : W)
    {t : ℕ} (Q : Fin t → P) : Prop :=
  L ms = u + μ * tg ∧ ∀ i, cw ms (Q i) = g (Q i) + μ • f (Q i)

omit [AddCommGroup W] [Module E W] in
/-- The bad values of the first verifier message: either μ is exceptional for the line g + μ f, or
some pair (Mg, Mf) in the list of the pair (g, f) at the radius e has L Mf ≠ tg and yet
L Mg + μ L Mf = u + μ tg. -/
def LdwBad1 (cw : W → P → Y) (e : ℕ) (L : W → E) (tg : E) (f g : P → Y) (u μ : E) : Prop :=
  LdwExc cw e g f μ ∨
  ∃ Mg Mf : W, LdwNear2 cw e g f Mg Mf ∧ L Mf ≠ tg ∧ L Mg + μ * L Mf = u + μ * tg

omit [AddCommGroup W] [Module E W] in
/-- The bad values of the second verifier message: cw ms agrees with g + μ f at all positions of Q,
though g + μ f is not near cw ms at the radius e. -/
def LdwBad2 (cw : W → P → Y) (e : ℕ) (f g : P → Y) (μ : E) (ms : W) {t : ℕ} (Q : Fin t → P) :
    Prop :=
  (∀ i, cw ms (Q i) = g (Q i) + μ • f (Q i)) ∧ ¬ LdwNear cw e (fun x => g x + μ • f x) ms

end Defs

namespace Spec

/-- The first error: at most `bad` + `L2` values of μ are bad, if at most `bad` values are
exceptional for the line and the list of the pair has at most `L2` members. -/
def ldw_cnt_bad1 : Prop :=
  ∀ (E W Y P : Type) [Field E] [Fintype E] [Finite W] [AddCommGroup Y] [Module E Y] [Fintype P]
      (cw : W → P → Y) (e bad L2 : ℕ) (L : W → E) (tg : E) (f g : P → Y) (u : E),
    cnt (fun μ : E => LdwExc cw e g f μ) ≤ bad →
    cnt (fun MM : W × W => LdwNear2 cw e g f MM.1 MM.2) ≤ L2 →
    cnt (fun μ : E => LdwBad1 cw e L tg f g u μ) ≤ bad + L2

/-- The second error: at most (N - e - 1)^t lists of positions are bad, N the number of positions.
-/
def ldw_cnt_bad2 : Prop :=
  ∀ (E W Y P : Type) [Field E] [AddCommGroup Y] [Module E Y] [Fintype P] (cw : W → P → Y) (e : ℕ)
      (f g : P → Y) (μ : E) (ms : W) (t : ℕ),
    cnt (fun Q : Fin t → P => LdwBad2 cw e f g μ ms Q) ≤ (Fintype.card P - e - 1) ^ t

/-- The backward step. -/
def ldw_back : Prop :=
  ∀ (E W Y P : Type) [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y]
      [Fintype P] (cw : W → P → Y) (e : ℕ) (L : W → E) (tg : E) (f g : P → Y) (u μ : E) (ms : W)
      (t : ℕ) (Q : Fin t → P),
    LdwLin (E := E) cw → LdwForm L → ¬ LdwBad1 cw e L tg f g u μ →
    ¬ LdwBad2 cw e f g μ ms Q → LdwAccept cw L tg f g u μ ms Q →
    LdwOn cw f (ldwAgree cw (fun x => g x + μ • f x) ms) ∧
    ∀ M, (∀ x ∈ ldwAgree cw (fun x => g x + μ • f x) ms, f x = cw M x) → LdwIn cw e L tg f M

/-- Below the distance a corrector of erasures has no choice of the corrected word. -/
def ldw_unique : Prop :=
  ∀ (W Y P : Type) [Fintype P] (cw : W → P → Y) (D : ℕ) (f : P → Y) (S : Finset P) (M M' : W),
    LdwApart cw D → Fintype.card P < S.card + D → (∀ x ∈ S, f x = cw M x) →
    (∀ x ∈ S, f x = cw M' x) → cw M = cw M'

/-- Completeness: no exception. -/
def ldw_complete : Prop :=
  ∀ (E W Y P : Type) [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y]
      (cw : W → P → Y) (L : W → E) (tg : E) (m h : W) (μ : E) (t : ℕ) (Q : Fin t → P),
    LdwLin (E := E) cw → LdwForm L → L m = tg →
    LdwAccept cw L tg (cw m) (cw h) (L h) μ (h + μ • m) Q

/-- What the honest prover shows, computed from a uniform answer. -/
def ldw_law : Prop :=
  ∀ (E W Y P : Type) [Field E] [AddCommGroup W] [Module E W] [Fintype W] [AddCommGroup Y]
      [Module E Y] (cw : W → P → Y) (L : W → E) (tg : E) (m : W) (μ : E),
    LdwLin (E := E) cw → LdwForm L → L m = tg →
    (unif W).map (fun h => (L h, h + μ • m, cw h)) =
      (unif W).map (fun ms => (L ms - μ * tg, ms, fun x => cw ms x - μ • cw m x))

/-- Mutual correlated agreement on lines below a third of the distance. -/
def ldw_third : Prop :=
  ∀ (E W Y P : Type) [Field E] [Fintype E] [AddCommGroup W] [Module E W] [AddCommGroup Y]
      [Module E Y] [Fintype P] (cw : W → P → Y) (D e : ℕ) (g f : P → Y),
    LdwLin (E := E) cw → LdwApart cw D → 3 * e < D → cnt (fun μ : E => LdwExc cw e g f μ) ≤ e + 1

/-- The same for the lines (1 - μ) g + μ f. -/
def ldw_third_fold : Prop :=
  ∀ (E W Y P : Type) [Field E] [Fintype E] [AddCommGroup W] [Module E W] [AddCommGroup Y]
      [Module E Y] [Fintype P] (cw : W → P → Y) (D e : ℕ) (g f : P → Y),
    LdwLin (E := E) cw → LdwApart cw D → 3 * e < D →
    cnt (fun μ : E =>
        ∃ S : Finset P,
          Fintype.card P ≤ S.card + e ∧
          LdwOn cw (fun x => (1 - μ) • g x + μ • f x) S ∧
          ¬ (LdwOn cw g S ∧ LdwOn cw f S)) ≤ e + 1

end Spec
end Cb
