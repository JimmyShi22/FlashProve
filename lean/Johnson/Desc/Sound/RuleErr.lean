-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleErr.lean: FROM A KIND's RULE OF BAD ELEMENTS WITH A CEILING TO A BLOCK's
ERRORS: the carrier from a law in the form "there is a rule `bad` from a front of the transcript to
a list of field elements, of at most c elements, and where no drawn element is bad ..." into the
errors of a piece (`Piece.err`), which count values of the WRITTEN round's challenge. A SHEET OF
STATEMENTS: definitions with code, and eight propositions written as `def … : Prop`. NOTHING IS
PROVED IN THIS FILE.

Why. The law of a sumcheck-shaped kind is proved over field values: in each round at most c values
of the drawn element are bad, given all that came before. `GoodInOfBadFam`
(Johnson/Desc/Sound/GoodIn.lean) wants a family of bad sets of the written rounds' challenges
(`Iop.BadFam`) within the piece's errors. Between the two lies the reading of a round: what the view
shows as drawn is `C.dr` of the written challenge.

THE LOWER HALF IS CALLED HERE, NOT TYPED ANEW: Johnson/Desc/First/Prod/FamL.lean: from a judge on
prefixes, at any list of rounds and any reading of a round, to a family of bad sets (`famL`), with
`famL_clean`, `BoundL`, `famL_within`, `cnt_mem_le`. This file is its instance at the written rounds
and the view's reading (`encRV`, `ReadIsView`), at the judge that a rule gives (`judgeOf`), and what
lies above: the rule as a list with a ceiling; the count where the reading is NOT one-to-one
(`CoordMeasure`); errors that bear the counts; the result at a piece.

The rule's form (ITS DEFINITIONS STAND IN A LIGHT FILE OF THEIR OWN,
Johnson/Desc/Sound/RuleForm.lean, which a kind's law can import without the rule of composition).
bad : List Fmt.RoundView → List E: from a front to a list of elements. A FRONT: the rounds in front, whole,
as the view shows them; of this round the message AND THE ELEMENTS OF ITS DRAW THAT STAND BEFORE THE
ONE IN QUESTION (positions, matrix entries and the digest are struck). So a round that draws a point
of several coordinates, whose bad event is the zero set of a polynomial in all of them, is served
coordinate by coordinate; the judge reads the whole round, so no letter of FamL.lean turns for it.
`NoBad bad t`: no element that a round of t draws is in the rule's list at its front: EVERY element
of the round's draw is asked. ANOTHER FORM (the whole draw struck) is the case of a rule that does
not look at the last round's draw: `NoBadStruck`, `StruckIsCase`. Johnson/Desc/Kinds/Law/Bad.lean
carries a rule over polynomials and field values into its form.

What is said. `ReadIsView`: the reading is the view's list of rounds. `CleanIsNoBad`: clean is
`NoBadFrom`. `CoordMeasure C d k f`: round d draws at most k elements; and for each place j of the
draw, and every rule L from the elements before it to a list of at most n elements, at most n * f
values of the written challenge draw at place j an element of L's list. TWO NUMBERS, KEPT APART: k:
how many elements; f: how many written challenges draw a given element at place j, ALL OTHER PLACES
FREE (at most, over the rules): at a round that draws k independent elements of a field of q
members, with w bits of work: q ^ (k - 1) * 2 ^ w: the whole number of challenges over q (not 2 ^
w). `OneToOne`: where a round draws just one element, read one-to-one, the measure is k = 1, f = 1:
that is `cnt_mem_le`. `RuleBound`: ceilings and measures give FamL.lean's `BoundL` at k j * (ceil j
* f j). `ErrBears`, `RuleWithin`: errors that bear these numbers. `GoodInOfRule`: `GoodInOfBadFam`
with the rule in the family's place: THE RULE IS A FUNCTION OF THE STATEMENT AND THE FRONT: BY ITS
TYPE NEVER OF A WITNESS. `DoomedOfRule`: the same into the plain form (no extractor): elsewhere
called `Leads`.

Limits. (1) `CoordMeasure` IS A PREMISE: at the kit of the release it is shown by nobody here: it is
a law on the format's drawing. (2) PROOF OF WORK AND BIAS: a written challenge is the old challenge
WITH the round's proof-of-work bits (`Iop.GChal`); `cnt` counts these pairs: so f holds the factor 2
^ work, as the piece's errors do, and the sampler's bias; what grinding costs or gains is the law of
the reading of the whole file, paid there once, not here. (3) ELEMENTS ALONE: a kind whose bad set
is of drawn POSITIONS (a proximity test; a code switch's places), of a sending's SEED as far as the
format draws it apart from `elems`, or of MATRIX ENTRIES (the smallness test's matrix) is not
served: these carry the library's typed blocks (`PieceGoodIn`). (4) The ceiling is one number for
each round, by the round's number in the stretch, for all places of its draw: at a round that draws
a point and a factor of high degree the largest ceiling is paid at every place: loose by a factor up
to k. (5) Two writings of one field element are two elements for "is in the list": that every drawn
element is below the prime is the test on the view in front of all blocks. (6) The degenerate cases
of GoodIn.lean's limits make these statements true and empty too: errors at or above the number of
challenges bear every rule; a rule that lists every element makes the two clauses free, and is borne
by such errors alone (Johnson/Desc/Sound/RuleErrToy.lean: `all_bad_not_within`; there too: a member,
and a block that says yes to all, which no rule with the toy's ceiling serves). (7) `NoBad` SPEAKS
OF THE STRETCH's ROUNDS AS THE WRITTEN READING SHOWS THEM (`rvSL`); a kind's law is over what its
block's decide is shown (the digest struck; what is handed back appended at the last block): that
equation is Johnson/Desc/Sound/ShownRounds.lean's: the two together are the carriage.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn
import Johnson.Desc.Sound.RuleForm
import Johnson.Desc.First.Prod.FamL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)
open _root_.Run.PQ (CK SgX PlainOf)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Prob (cnt)
open VerifiableInference.Desc.First.Prod (Enc trL famL errL BoundL)

/-- The reading of the written rounds: each round as the view shows it. -/
def encRV (C : CK) : (ds : List RD) → Enc Fmt.RoundView (uL C ds)
  | [] => ()
  | d :: ds =>
    (fun m c => ⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work) m.2),
      C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)⟩, encRV C ds)

/-- **The judge that a rule gives**: the round r, behind the rounds pre, has drawn an element that
is in the rule's list at the front cut before that element. -/
def judgeOf (bad : List Fmt.RoundView → List E) (pre : List Fmt.RoundView) (r : Fmt.RoundView) : Prop :=
  ∃ j x, r.drawn.elems[j]? = some x ∧ E.ofTriple x ∈ bad (pre ++ [cutTo r j])

/-- What round d draws at the written challenge c: its elements. -/
def elemsAt (C : CK) (d : RD) (c : Iop.GChal d.entry.work (C.Ch d.entry d.kind)) : List Fmt.Ext :=
  (C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)).elems

/-- **The measure of a round's draw.** k: the round draws at most k elements. f: at each place j of
the draw, for every rule L from the elements before it to a list of at most n elements, at most n *
f values of the written challenge, all other places free, draw there an element of L's list. -/
def CoordMeasure (C : CK) (d : RD) (k f : ℕ) : Prop :=
  (∀ c, (elemsAt C d c).length ≤ k) ∧
  ∀ (j n : ℕ) (L : List Fmt.Ext → List E), (∀ pre, (L pre).length ≤ n) →
    cnt (fun c => ∃ x, (elemsAt C d c)[j]? = some x ∧
      E.ofTriple x ∈ L ((elemsAt C d c).take j)) ≤ n * f

/-- The errors bear the number `need j` at the round number j; n: the number of the first round. -/
def ErrBears (C : CK) (need : ℕ → ℕ) : (ds : List RD) → ℕ → Err (uL C ds) → Prop
  | [], _, _ => True
  | _ :: ds, n, (e, ε) => need n ≤ e ∧ ErrBears C need ds (n + 1) ε

/-- The reading is the view's list of rounds. -/
def ReadIsView : Prop :=
  ∀ (C : CK) (ds : List RD) (τ : Iop.Tr (uL C ds)), trL (encRV C ds) τ = rvSL C ds τ

/-- **A transcript is clean just where no drawn element is bad.** -/
def CleanIsNoBad : Prop :=
  ∀ (C : CK) (bad : List Fmt.RoundView → List E) (ds : List RD) (h : List Fmt.RoundView) (τ : Iop.Tr (uL C ds)),
    (famL (judgeOf bad) (uL C ds) (encRV C ds) h).Clean τ ↔ NoBadFrom bad h (rvSL C ds τ)

/-- The other form is the case of a rule that strikes the last round's draw. -/
def StruckIsCase : Prop :=
  ∀ (bad : List Fmt.RoundView → List E) (t : List Fmt.RoundView),
    NoBadStruck bad t ↔ NoBad (fun g => bad (strikeLast g)) t

/-- Where a round draws just one element, and the written challenges are read one-to-one into it,
the measure is 1 and 1. -/
def OneToOne : Prop :=
  ∀ (C : CK) (d : RD) (val : Iop.GChal d.entry.work (C.Ch d.entry d.kind) → Fmt.Ext),
    (∀ c, elemsAt C d c = [val c]) → Function.Injective (fun c => E.ofTriple (val c)) →
    CoordMeasure C d 1 1

/-- **The counts.** ceil j: the rule's ceiling at a front of j + 1 rounds. k j, f j: the measure of
the round number j. n: the number of the first round of ds. -/
def RuleBound : Prop :=
  ∀ (C : CK) (bad : List Fmt.RoundView → List E) (ceil k f : ℕ → ℕ) (ds : List RD) (n : ℕ),
    (∀ g, (bad g).length ≤ ceil (g.length - 1)) →
    (∀ j d, ds[j]? = some d → CoordMeasure C d (k (n + j)) (f (n + j))) →
    BoundL (judgeOf bad) (fun j => k j * (ceil j * f j)) (uL C ds) (encRV C ds) n

/-- **The family is within errors that bear the counts.** -/
def RuleWithin : Prop :=
  ∀ (C : CK) (bad : List Fmt.RoundView → List E) (ceil k f : ℕ → ℕ) (ds : List RD) (h : List Fmt.RoundView)
    (ε : Err (uL C ds)),
    (∀ g, (bad g).length ≤ ceil (g.length - 1)) →
    (∀ j d, ds[j]? = some d → CoordMeasure C d (k (h.length + j)) (f (h.length + j))) →
    ErrBears C (fun j => k j * (ceil j * f j)) ds h.length ε →
    (famL (judgeOf bad) (uL C ds) (encRV C ds) h).Within ε

/-- **From a rule with a ceiling to `GoodIn` at the piece's errors.** -/
def GoodInOfRule : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (bad : S × F.E.Str → List Fmt.RoundView → List E)
    (ceil k f : ℕ → ℕ),
    (∀ a g, on a → (bad a g).length ≤ ceil (g.length - 1)) →
    (∀ j d, (toRDs p.ds)[j]? = some d → CoordMeasure C d (k j) (f j)) →
    ErrBears C (fun j => k j * (ceil j * f j)) (toRDs p.ds) 0 p.err →
    (∀ a τ b, on a → NoBad (bad a) (rvSL C (toRDs p.ds) τ) → p.ior.red.out a τ = some b → on' b) →
    (∀ a τ b w, on a → NoBad (bad a) (rvSL C (toRDs p.ds) τ) → p.ior.red.out a τ = some b →
      R' b w → R a (p.ext a τ w)) →
    p.GoodIn on on' R R'

/-- **The same into the plain form**: no extractor: Q: what holds of the statements in front and
behind wherever the block says yes on a transcript without a bad element. -/
def DoomedOfRule : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on : S × F.E.Str → Prop)
    (Q : S × F.E.Str → S × F.E.Str → Prop) (bad : S × F.E.Str → List Fmt.RoundView → List E)
    (ceil k f : ℕ → ℕ),
    (∀ a g, on a → (bad a g).length ≤ ceil (g.length - 1)) →
    (∀ j d, (toRDs p.ds)[j]? = some d → CoordMeasure C d (k j) (f j)) →
    ErrBears C (fun j => k j * (ceil j * f j)) (toRDs p.ds) 0 p.err →
    (∀ a τ b, on a → NoBad (bad a) (rvSL C (toRDs p.ds) τ) → p.ior.red.out a τ = some b → Q a b) →
    ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → Q a b


end VerifiableInference.Desc.Sound
