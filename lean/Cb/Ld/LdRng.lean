-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRng.lean: the approximate range check with packing, as an interactive oracle reduction over
oracle messages with samples.

This file states an approximate range proof as a three-round reduction. The verifier draws a random
matrix with entries in {-1, 0, 1}; the prover sends, as new oracles, the digits of the combinations
of its integers with that matrix. The claim that the messages behind the old oracles pack integers
below a bound in absolute value (B on the honest side, 2 D in the relaxed relation), and that the
reads are the weights times these integers (`RngRd`, below), is reduced to linear equations on the
two components read off the old messages and on the digits, and to the claim that all digits are in
their tables.

Definitions and statements (Cb.Spec.ldRng_*); the proofs are in Cb/Ld/LdRngProofs.lean.
The mathematics is Cb/Ld/LdRngAlg.lean; the joints are those of Cb/Ld/LdSig.lean; the sending is
Cb/Ld/LdSigSum.lean's (Cb/Ld/LdSendFam.lean, Cb/Ld/LdSend.lean); the rule that lifts a reduction on
claims about messages is Cb/Ld/LdSigLift.lean's.
`S.over A` (Cb/Ld/LdSig.lean) claims a base joint A of the messages of the oracle messages of a
signature S; in its relaxed relation these are the messages that the decoder with a sample returns.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

The parameters (`RngPar`): packed rows Rp, reads Rd, columns C, combinations U (finite sets; C is
not empty); P, the number of rows of cells that are packed into one; ϱ, the radix (`rdx`); B, the
honest bound; D, the half-width of the window; q, H, the sizes of the two tables of digits.
  `p.OK`: 1 ≤ B ≤ 2 D, 0 < q, q H = 2 D. No condition on P, ϱ or the characteristic is asked by this
    block. They are asked where the cells are read as a virtual matrix: Cb/Ld/LdRead.lean.
How the check reads (`RngRd`): W st: the weight vectors of the reads, a function of the explicit
part of the input statement; pk m, rd m: the two components, the packed matrix and the reads,
functions of the tuple m of all messages of the statement (so they may be in several oracle
messages); yz k: the integer matrix behind them, a function of the core of the honest witness.

From `S.over (rngIn p r A₀)`: the predicate `Rng` on (pk m, rd m) with the weights W st, beside any
base joint A₀ (what else the statement claims; it rides along). Honest: bound B, the integer matrix
is that of the core. Relaxed, by decoding with a sample: bound 2 D, some integer matrix.
To `(S.sum N).over (S.grow N (rngOut p r A₀) ..)`: all digits are in their tables, and the rows
    pk m · Θ_u = pack (digits' values), rd m · Θ_u = W st · (digits' values)
hold, beside A₀. The digits are, unpacked, in the messages of the family N that was sent (`get`
reads them). The same predicate on both sides.

Three rounds, none merged; two verifier messages are not empty.
  Round 1: the prover sends nothing. The verifier sends Θ: |U| · |C| coefficients in {-1, 0, 1},
  independent, 0 with probability 1/2, each sign with probability 1/4 (two uniform bits each).
  Rounds 2, 3: the sending of the family N with its samples: the words; a joint seed; the answers;
  an empty verifier message.
  The verifier reads nothing and never rejects.
The order holds by the form of the term. The words and the samples (seeds and answers) of all oracle
messages that the predicate speaks of are in the input statement, and so is all that W reads: they
are fixed before Θ. Θ is a verifier message of its own: it shares a message with no seed. The seeds
of the digits' oracle messages come after Θ.

The errors, counts of values of one verifier message: round 1: `p.err` = |challenges| / 2^|U|
(`Spec.ldRng_err`: exactly the fraction 2^(-|U|)); rounds 2, 3: those of the sending.
  No list size enters the first: the messages are a function of words and samples. Under `p.OK` the
  count holds on all statements, collision-free or not. The bundles below (`Spec.ldRng_at`,
  `Spec.ldRng_draw`, `Spec.ldRng_goodT`) state knowledge soundness at the joint's condition only,
  and hand the condition on (`Spec.ldRng_goodT`: through `.cf`; that the new samples do not collide
  is not handed on: a collision is counted in the sending's error). Over a signature that condition
  is: the samples do not collide, and the condition of what rides along holds. Knowledge soundness
  of round 1, as an interactive reduction, on all statements is stated and proved in
  Cb/Ld/LdRngKnowAll.lean (`ldRng_knowAll`, under `p.OK`).
  The first is one error for range, packing and the tie of the reads.
  The first error is not algebraic: it does not shrink with the field. It shrinks with |U|, and with
  proof of work: w test bits in that round (Ior/GrindK.lean: the count stays, the verifier's message
  has 2^w times as many values) make it 2^(-|U| - w) (`Spec.ldRng_work`, arithmetic only).
The extractor forgets what was sent: it keeps the pairs of the old oracle messages and the further
witness.
The honest side: the witness gets the digits of the integer combinations (`hdig`). Withheld in
secret (`Hid`, Ior/Honest.lean): the window event of the core's integer matrix (an entry of some
combination leaves [-D, D)) (`rngEv`: that event if all entries of the matrix are below B in
absolute value, else the empty set); its probability is at most `p.pWin` = 2 · (rows of cells) · |U|
· exp(-D² / (|C| (B - 1)²)), and 0 if B = 1 (`Spec.ldRng_pWin`, under `p.OK`). It is the
completeness error and an honest-verifier zero-knowledge error. Nothing is withheld in public
(`Bad := ∅`).
Honest-verifier zero knowledge, in the exact form of Ior/Honest.lean: outside the window
event, which is withheld in secret (`Hid` := `rngEv`), round 1 shows nothing; the rest is the
sending's, under its hypotheses (`Dn.Blind Sd`: answers that do not depend on the witness;
`Dn.Nn.Hides (N.budT t)`: an encoding that hides).

Main names: the block in two layers.
  `rngDraw`, `rngDrawH`, `rngDrawN`: round 1 alone, between base joints (no code): the digits become
    a further part of the witness. `Spec.ldRng_at`: under `p.OK` it has the bundle `GoodAt`
    (knowledge soundness for each fixed tuple of messages); `Spec.ldRng_exact`: see its statement.
  `ldRngDraw ..`: round 1 over a signature: `Spec.ldRng_draw` (`IOR.GoodT`, under `p.OK`). Any
    sending may follow it.
  `ldRng ..`: all three rounds: `Spec.ldRng_goodT`, under the hypotheses of its statement.
  `rngRow`, `rngTgt`, `Spec.ldRng_rows`: the rows as linear forms. If the entries of the two
    components and the digits are at places (`RngAt`) of one vector v of entries, the rows are
    (|Rp| + |Rd|) · |U| linear forms with a state (Cb/Ld/LdRel.lean: `Slf`; the state is (st, Θ))
    with public targets: the form that a batching takes (Cb/Ld/LdBatSig.lean). A packed entry is
    read by them as an element of the field.

What the sending's hypotheses ask; each stands in `Spec.ldRng_goodT` as a premise (in these rows C
is `(N.om a).C`, not the columns; o is `N.om a`; L is `L a`; D is `Dn`; back is
`S.backN N (rngBk p N get)`; the last row's `N.Hides bud` is `Dn.Nn.Hides (N.budT t)`; the clauses
on one oracle message are for Cb/Ld/LdSend.lean):
  The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
    `C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native
    words to long words, are linear over E; the encoder sends only the zero message with zero
    randomness to zero; and, for every long position x, any two native words that agree at the
    native positions `C.src x` have the same long symbol at x.
  `Sd.Fair` (`Sig.Seeds.Fair`) asks of the joint seeds of a family: for each member a and each seed
    ρ of that member's sample map `(N.om a).Z`, at most `Sd.mult a` joint seeds s have
    `Sd.sd a s = ρ`.
  The list of a word f as sent (`o.InList f`) consists of the messages m for which, for some
    randomness r, the long words `o.C.T (o.upW f)` and `o.C.T (o.C.enc m r)` differ at no more than
    `o.e` long positions; `o.ListLE L` (`OMsg.ListLE`) asks that, for every word f as sent, that
    list has at most L members.
  `o.Evades` (`OMsg.Evades`) asks: for every word f as sent and any two different messages m and m'
    of the list `o.InList f`, the seeds ρ of the sample map `o.Z` at which m and m' have the same
    answers (`o.Z.val ρ m = o.Z.val ρ m'`) number at most `o.Z.err`.
  The laws of a sender (`D.Laws back`, that is `Sig.Sender.Laws`; for one oracle message
    `OMsg.Sender.Laws`) ask two things: for every m and r, the word `D.Nn.enc m r` (for one oracle
    message, `D.N.enc m r`), read as a native word through `upW`, is the code's encoding of
    `D.upM m` with randomness `D.upR r`, for a family at each member a
    (`(N.om a).upW (D.Nn.enc m r a) = (N.om a).C.enc (D.upM m a) (D.upR r a)`); and `back` returns w
    from `D.upM (D.put w k)` and `D.rest w`, for every witness w and every k in `D.Mk`.
  `D.Blind Sd` (`Sig.Sender.Blind`) asks that, for every joint seed s and all witnesses w and w',
    the distribution of `D.ans Sd s w k` over uniform k in `D.Mk` equal that of `D.ans Sd s w' k`;
    `D.ans Sd s w k` gives the family, over the members a, of the answers
    `(N.om a).Z.val (Sd.sd a s)` of `D.upM (D.put w k) a`, and the distribution is of that whole
    family. For one oracle message o, `D.Blind` (`OMsg.Sender.Blind`) asks the same with a seed ρ of
    `o.Z` in place of s: that, for every ρ and all w and w', the distribution of `D.ans ρ w k` over
    uniform k in `D.Mk` equal that of `D.ans ρ w' k`, where `D.ans ρ w k` is
    `o.Z.val ρ (D.upM (D.put w k))`.
  `N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages
    m and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
    `N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S.

Notation: `S`: a signature: the oracle messages of the input statement; `N`: the family that is
sent, a signature too (`Sig E`, Cb/Ld/LdSig.lean); `Sd`: how the seeds of the members of N are drawn
(`N.Seeds`); `Dn`: the honest sender of the family N (`N.Sender`; both: Cb/Ld/LdSendFam.lean); `L`,
`t`: a number for each member of N (`N.O → ℕ`).

Limits: the declared differences to this protocol's technical report are these, beside those on the
digits, the tables and the bound B, which Cb/Ld/LdRng2Alg.lean and Cb/Ld/LdRng2.lean tell.
(a) The rows of cells are the pairs (packed row, lane): their number is a multiple of P.
(b) The radix of the digits is any q (the report: a power of two).
(c) "The digits are in their tables" is stated outright (`Cb.Rng.InTab`); it is the input predicate
    of a lookup (Cb/Gen/RngLkp.lean has it in the lookup's letters). No lookup is run here. The
    multiplicities of that lookup are not this block's: whoever calls the lookup sends them. Since N
    is a family, they can go in the same prover message as the digits.
(d) The honest relation names the integer matrix through the core of the witness.
(e) The batching of the rows is not run here.
(f) Errors are counts; radii are not seen.
That the check comes after all evaluations of the segment's cells is a matter of the protocol that
uses it: here, W reads the input statement. `p.err` says nothing if |U| = 0. `p.pWin` at or above 1
says nothing. This file says nothing on running times or sizes, and nothing on what the honest
prover sends in the window event.
The block follows this protocol's technical report, which follows the paper that this protocol
builds on and advice (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRngAlg
import Cb.Ld.LdSigLift
import Cb.Ld.LdSigSum
import Cb.Ld.LdBatSig
import Ior.Draw
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk
open scoped ENNReal

/-! ## 1. Parameters -/

/-- The parameters of a range check with packing. -/
structure RngPar where
  /-- packed rows, reads, columns, combinations -/
  Rp : Type
  Rd : Type
  C : Type
  U : Type
  [finRp : Fintype Rp]
  [finRd : Fintype Rd]
  [finC : Fintype C]
  [decC : DecidableEq C]
  [neC : Nonempty C]
  [finU : Fintype U]
  [decU : DecidableEq U]
  /-- how many rows of cells are packed into one; the radix -/
  P : ℕ
  rdx : ℤ
  /-- the honest bound; the half-width of the window; the sizes of the two tables -/
  B : ℤ
  D : ℤ
  q : ℕ
  H : ℕ

attribute [instance] RngPar.finRp RngPar.finRd RngPar.finC RngPar.decC
  RngPar.neC RngPar.finU RngPar.decU

namespace RngPar
variable (p : RngPar)

/-- the rows of cells; matrices of cells; the verifier's message; the digits -/
abbrev Row : Type := p.Rp × Fin p.P
abbrev Cells : Type := p.Row → p.C → ℤ
abbrev Chal : Type := p.U → p.C → Coef
abbrev Dg (E : Type) : Type := Dig E p.Rp p.P p.U

structure OK : Prop where
  B1 : 1 ≤ p.B
  BD : p.B ≤ 2 * p.D
  q0 : 0 < p.q
  qH : (p.q : ℤ) * p.H = 2 * p.D

/-- The error of the draw, a count of challenges. -/
def err : ℕ := Fintype.card p.Chal / 2 ^ Fintype.card p.U

/-- the bound on the probability of the window event -/
def pWin : ℝ≥0∞ :=
  if p.B ≤ 1 then 0
  else
    (Fintype.card (p.Row × p.U) : ℝ≥0∞) *
      ENNReal.ofReal
        (2 * Real.exp (-((p.D : ℝ) ^ 2 / (Fintype.card p.C * ((p.B - 1 : ℤ) : ℝ) ^ 2))))

end RngPar

/-- How the check reads: the weights of the reads off the explicit part, the two components off the
messages, the integer matrix off the core. -/
structure RngRd (p : RngPar) (E St M Kc : Type) where
  W  : St → p.Rd → p.Row → E
  pk : M → p.Rp → p.C → E
  rd : M → p.Rd → p.C → E
  yz : Kc → p.Cells

/-! ## 2. The base joints -/

section
variable {E St M Kc Wp Wt : Type} [CommRing E] {E₀ : ExtSpec} (p : RngPar)

/-- The predicate beside a joint A, for any kind of witness: pk, rd say how the two components are
read off a witness. -/
def rngJ (W : St → p.Rd → p.Row → E) (yz : Kc → p.Cells) (pk : Wt → p.Rp → p.C → E)
    (rd : Wt → p.Rd → p.C → E) (A : IOR.Rels Kc St E₀ Wt) : IOR.Rels Kc St E₀ Wt where
  rel  := fun st y w => RngBy p.B p.rdx (W st) (yz (A.core w)) (pk w) (rd w) ∧ A.rel st y w
  relR := fun a w => Rng (2 * p.D) p.rdx (W a.1) (pk w) (rd w) ∧ A.relR a w
  on   := A.on
  core := A.core

variable (r : RngRd p E St M Kc) (A₀ : IOR.Rels Kc St E₀ (M × Wp))

/-- The input joint, at the base: the two components are read off the messages. -/
def rngIn : IOR.Rels Kc St E₀ (M × Wp) := rngJ p r.W r.yz (fun w => r.pk w.1) (fun w => r.rd w.1) A₀

/-- The joint after the draw, at the base: the digits are a further part of the witness. -/
def rngOut : IOR.Rels Kc (St × p.Chal) E₀ (M × (Wp × p.Dg E)) where
  rel  := fun x y w =>
    Out p.D p.rdx p.q p.H (r.W x.1) x.2 (r.pk w.1) (r.rd w.1) w.2.2 ∧ A₀.rel x.1 y (w.1, w.2.1)
  relR := fun a w =>
    Out p.D p.rdx p.q p.H (r.W a.1.1) a.1.2 (r.pk w.1) (r.rd w.1) w.2.2 ∧
    A₀.relR (a.1.1, a.2) (w.1, w.2.1)
  on   := fun a => A₀.on (a.1.1, a.2)
  core := fun w => A₀.core (w.1, w.2.1)

/-! ## 3. The draw, at the base -/

/-- Round 1: the verifier draws Θ, which joins the explicit part. -/
abbrev rngDraw (St : Type) (E₀ : ExtSpec) : IOR St E₀ (St × p.Chal) E₀ :=
  IOR.draw p.Chal (fun st Θ => (st, Θ)) E₀

/-- The window event of an integer matrix with entries below B, as a set of values of the verifier's
randomness. -/
def rngEv (Y : p.Cells) : Set (Rho [IOR.drawRound p.Chal]) :=
  {ρ | (∀ r c, |Y r c| < p.B) ∧ Event p.D Y (show p.Chal × Unit from ρ).1}

/-- The honest side of round 1: nothing is sent; the witness gets the digits of the integer
combinations; the window event is withheld in secret. -/
def rngDrawH : (rngDraw p St E₀).Honest (M × Wp) (M × (Wp × p.Dg E)) where
  Coin := Unit
  strat w x _ := ((((), ()), fun Θ => ((x, Θ), (w.1, (w.2, hdig p.D p.q (r.yz (A₀.core w)) Θ)))) :
    Strat [IOR.drawRound p.Chal] ((St × p.Chal) × (M × (Wp × p.Dg E))))
  Bad := ∅
  Hid w _ := rngEv p (r.yz (A₀.core w))

/-- The numbers of round 1. -/
def rngDrawN : IOR.Nums Kc (rngDraw p St E₀) :=
  ⟨((p.err, ()) : ℕ × Unit), 0, p.pWin, fun _ _ => True, fun k => rngEv p (r.yz k)⟩

end

/-! ## 4. Over a signature; with the sending of the digits -/

section
variable {E St Kc Wp : Type} [Field E] {E₀ : ExtSpec} (p : RngPar) (S N : Sig E)
  (r : RngRd p E St S.Msg Kc) (A₀ : IOR.Rels Kc St E₀ (S.Msg × Wp))

/-- Round 1 over a signature: words and samples are copied. -/
abbrev ldRngDraw (St : Type) (E₀ : ExtSpec) :
    IOR (St × S.Smp) (E₀.prod S.ext) ((St × p.Chal) × S.Smp) (E₀.prod S.ext) :=
  (rngDraw p St E₀).keep S.Smp S.ext

abbrev ldRngDrawH : (ldRngDraw p S St E₀).Honest (S.Wit × Wp) (S.Wit × (Wp × p.Dg E)) :=
  S.liftH (rngDrawH p r A₀)

abbrev ldRngDrawN : IOR.Nums Kc (ldRngDraw p S St E₀) :=
  (rngDrawN (E₀ := E₀) p r).keep S.Smp S.ext

/-- the digits are read off the new messages -/
def rngBk (get : N.Msg → p.Dg E) : N.Msg → Wp → Wp × p.Dg E := fun m wp => (wp, get m)

variable (Sd : N.Seeds)

/-- The range check: the draw, then the sending of the family that holds the digits. -/
abbrev ldRng (St : Type) (E₀ : ExtSpec) :
    IOR (St × S.Smp) (E₀.prod S.ext) ((St × p.Chal) × (S.sum N).Smp) (E₀.prod (S.sum N).ext) :=
  (ldRngDraw p S St E₀).seq (ldSendSig S N Sd (St × p.Chal) E₀)

abbrev ldRngH (Dn : N.Sender (S.Wit × (Wp × p.Dg E)) (S.Wit × Wp)) :
    (ldRng p S N Sd St E₀).Honest (S.Wit × Wp) ((S.sum N).Wit × Wp) :=
  (ldRngDrawH p S r A₀).seq (ldSendSigHon Sd (St × p.Chal) E₀ Dn)

abbrev ldRngN (L t : N.O → ℕ) : IOR.Nums Kc (ldRng p S N Sd St E₀) :=
  (ldRngDrawN (E₀ := E₀) p S r).seq (ldSendSigNums S N Sd (St × p.Chal) E₀ Kc L t)

end

/-! ## 5. The rows as linear forms -/

namespace RngPk

/-- Coefficients a x laid at the places at x of a vector with coordinates J (added up where places
coincide). -/
def placed {I J E : Type} [Fintype I] [DecidableEq J] [AddCommMonoid E] (at' : I → J) (a : I → E) :
    J → E :=
  fun n => ∑ x, if at' x = n then a x else 0

end RngPk

/-- The places of the entries of the two components and of the digits in one vector of entries. -/
structure RngAt (p : RngPar) (J : Type) where
  pk : p.Rp → p.C → J
  rd : p.Rd → p.C → J
  lo : p.Row → p.U → J
  hi : p.Row → p.U → J

section
variable {E St J : Type} [Field E] [DecidableEq J] (p : RngPar)
  (W : St → p.Rd → p.Row → E) (l : RngAt p J)

/-- The rows: one for each packed row and each read, for each combination. The state is (st, Θ). -/
def rngRow : (p.Rp ⊕ p.Rd) × p.U → Slf E (St × p.Chal) J
  | (.inl i, u) =>
    fun s n =>
      placed (l.pk i) (fun c => (((s.2 u c).val : ℤ) : E)) n -
        placed (fun k : Fin p.P => l.lo (i, k) u) (fun k => (p.rdx : E) ^ (k : ℕ)) n -
        (p.q : E) * placed (fun k : Fin p.P => l.hi (i, k) u) (fun k => (p.rdx : E) ^ (k : ℕ)) n
  | (.inr k, u) => fun s n => placed (l.rd k) (fun c => (((s.2 u c).val : ℤ) : E)) n
      - placed (fun r => l.lo r u) (W s.1 k) n - (p.q : E) * placed (fun r => l.hi r u) (W s.1 k) n

/-- Their targets: public. -/
def rngTgt (st : St) : (p.Rp ⊕ p.Rd) × p.U → E
  | (.inl _, _) => - (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ)
  | (.inr k, _) => - (p.D : E) * ∑ r, W st k r

/-- the two components and the digits, read at their places -/
def RngAt.pkOf (v : J → E) : p.Rp → p.C → E := fun i c => v (l.pk i c)
def RngAt.rdOf (v : J → E) : p.Rd → p.C → E := fun k c => v (l.rd k c)
def RngAt.dgOf (v : J → E) : p.Dg E := (fun r u => v (l.lo r u), fun r u => v (l.hi r u))

end

/-! ## The statements -/

namespace Spec
open IOR

/-- The error of the draw is exactly the fraction 2^(-|U|). -/
def ldRng_err : Prop := ∀ p : RngPar, p.err * 2 ^ Fintype.card p.U = Fintype.card p.Chal

/-- With w further uniform bits in the verifier's message the same count is the fraction
2^(-|U| - w). -/
def ldRng_work : Prop :=
  ∀ (p : RngPar) (w : ℕ), p.err * 2 ^ (Fintype.card p.U + w) = Fintype.card p.Chal * 2 ^ w

/-- The probability of the window event. -/
def ldRng_pWin : Prop := ∀ (p : RngPar) (Y : p.Cells), p.OK → prRho (rngEv p Y) ≤ p.pWin

/-- Under `p.OK`: the exact relation of the input joint is contained in the relaxed one, if that
holds of what rides along. -/
def ldRng_sub : Prop :=
  ∀ (E St M Kc Wp : Type) [CommRing E] (E₀ : ExtSpec) (p : RngPar)
      (r : RngRd p E St M Kc) (A₀ : Rels Kc St E₀ (M × Wp)),
    p.OK → (∀ x y w, A₀.rel x y w → A₀.relR (x, y) w) →
    ∀ x y w, (rngIn p r A₀).rel x y w → (rngIn p r A₀).relR (x, y) w

/-- Round 1, for each fixed tuple of messages. The extractor forgets the digits. -/
def ldRng_at : Prop :=
  ∀ (E St M Kc Wp : Type) [CommRing E] (E₀ : ExtSpec) (p : RngPar)
      (r : RngRd p E St M Kc) (A₀ : Rels Kc St E₀ (M × Wp)),
    p.OK → GoodAt (rngDraw p St E₀) (rngDrawH p r A₀) (rngIn p r A₀) (rngOut p r A₀)
      (fun _ _ _ w => w.1) (rngDrawN p r)

/-- Honest-verifier zero knowledge, in the exact form of Ior/Honest.lean: outside the window
event, which is withheld in secret (`Hid` := `rngEv`), round 1 shows nothing. -/
def ldRng_exact : Prop :=
  ∀ (E St M Kc Wp : Type) [CommRing E] (E₀ : ExtSpec) (p : RngPar) (r : RngRd p E St M Kc)
      (A₀ : Rels Kc St E₀ (M × Wp)) (Ri : St → E₀.Str → M × Wp → Prop),
    (rngDrawH p r A₀).Exact Ri fun _ _ => True

/-- Round 1 over a signature: relaxation by decoding with a sample on both sides; knowledge
soundness at the joint's condition (on all statements: Cb/Ld/LdRngKnowAll.lean). -/
def ldRng_draw : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar) (S : Sig E)
      (r : RngRd p E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    p.OK → GoodT (ldRngDraw p S St E₀) (ldRngDrawH p S r A₀) (S.over (rngIn p r A₀))
      (S.over (rngOut p r A₀)) (fun _ _ w => (w.1, w.2.1)) (ldRngDrawN p S r)

/-- The range check with packing. The statement has eight hypotheses: `p.OK`; for every member a of
N, `(N.om a).C.Laws` (Cb/Ld/LdRel.lean), `ListLE (L a)` and `Evades` (Cb/Ld/LdSig.lean); `Sd.Fair`,
`Dn.Laws` and `Dn.Blind Sd` (Cb/Ld/LdSendFam.lean); `Dn.Nn.Hides (N.budT t)` (Cb/Gen/Code.lean); the
head tells what each asks.
Under these the three rounds (`ldRng`), with the honest side `ldRngH`, have the bundle `GoodT`
(Ior/KnowCollGood.lean) from `(S.over (rngIn ..)).cf` to
`((S.sum N).over (S.grow N (rngOut ..) ..)).cf`, with the extractor that the head tells, at the
numbers `ldRngN` (`.cf`: `Rels.cf`, Ior/KnowCollGood.lean: the condition is moved into the relaxed
relation). -/
def ldRng_goodT : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar) (S N : Sig E)
      (r : RngRd p E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (get : N.Msg → p.Dg E)
      (Sd : N.Seeds) (Dn : N.Sender (S.Wit × (Wp × p.Dg E)) (S.Wit × Wp)) (L t : N.O → ℕ),
    p.OK → (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) →
    (∀ a, (N.om a).Evades) → Dn.Laws (S.backN N (rngBk p N get)) →
    Dn.Blind Sd → Dn.Nn.Hides (N.budT t) →
    GoodT (ldRng p S N Sd St E₀) (ldRngH p S N r A₀ Sd Dn) (S.over (rngIn p r A₀)).cf
      ((S.sum N).over (S.grow N (rngOut p r A₀) (rngBk p N get))).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, w.2)) (ldRngN p S N r Sd L t)

/-- Three rounds. -/
def ldRng_rounds : Prop :=
  ∀ (E St : Type) [Field E] (E₀ : ExtSpec) (p : RngPar) (S N : Sig E) (Sd : N.Seeds),
    (ldRng p S N Sd St E₀).shape.length = 3

/-- What coefficients laid at places do. -/
def ldRng_placed : Prop :=
  ∀ (I J E : Type) [Fintype I] [Fintype J] [DecidableEq J] [CommRing E] (at' : I → J)
      (a : I → E) (v : J → E),
    ∑ n, placed at' a n * v n = ∑ x, a x * v (at' x)

/-- The rows are linear forms with public targets. -/
def ldRng_rows : Prop :=
  ∀ (E St J : Type) [Field E] [Fintype J] [DecidableEq J] (p : RngPar) (W : St → p.Rd → p.Row → E)
      (l : RngAt p J) (st : St) (Θ : p.Chal) (v : J → E),
    Rows p.D p.rdx p.q (W st) Θ (l.pkOf p v) (l.rdOf p v) (l.dgOf p v) ↔
    Slf.All (rngRow p W l) (rngTgt p W st, fun _ => (st, Θ)) v

/-- their number -/
def ldRng_rows_card : Prop :=
  ∀ p : RngPar,
    Fintype.card ((p.Rp ⊕ p.Rd) × p.U) = (Fintype.card p.Rp + Fintype.card p.Rd) * Fintype.card p.U

/-- What the relaxed relation of the output joint says, if components and digits are at places of
the entries of all messages, old and new: the messages are the decoding; the digits are in their
tables; the rows hold; and what rode along. -/
def ldRng_end : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar) (S N : Sig E)
      (l : RngAt p (S.sum N).Ent) (r : RngRd p E St S.Msg Kc)
      (get : N.Msg → p.Dg E) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    (∀ m : (S.sum N).Msg,
      r.pk (S.left N (T := OMsg.Msg) m) = l.pkOf p ((S.sum N).ents m) ∧
      r.rd (S.left N (T := OMsg.Msg) m) = l.rdOf p ((S.sum N).ents m) ∧
      get (S.right N (T := OMsg.Msg) m) = l.dgOf p ((S.sum N).ents m)) →
    ∀ a w,
      ((S.sum N).over (S.grow N (rngOut p r A₀) (rngBk p N get))).relR a w ↔
      (∀ i, (S.sum N).decs a.1.2 a.2.2 i = some (w.1 i).1) ∧
      InTabs p.q p.H (l.dgOf p ((S.sum N).ents ((S.sum N).msgs w.1))) ∧
      Slf.All (rngRow p r.W l) (rngTgt p r.W a.1.1.1, fun _ => a.1.1)
        ((S.sum N).ents ((S.sum N).msgs w.1)) ∧
      A₀.relR (a.1.1.1, a.2.1) (S.left N (T := OMsg.Msg) ((S.sum N).msgs w.1), w.2)

end Spec
end Cb
