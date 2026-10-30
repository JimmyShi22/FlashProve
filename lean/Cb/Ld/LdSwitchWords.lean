-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchWords.lean: the code switch "with lists", on vectors: definitions, and the statements
that carry its errors, its backward step and its completeness.

In standard terms: a linear map made from a seed (the sample) separates the members of a list, but
for the bad seeds `Bad1`; after a good seed at most one member of the list has the answers; spot
checks at t positions compare the long word of its old part with y; a linear combination with
coefficients made from a seed batches all linear equations into one.

Plain mathematics: no protocol, no oracle, no game. The statements are each a `Prop` in `Cb.Spec`;
the proofs are in Cb/Ld/LdSwitchWordsProofs.lean.

The setting. K names the coordinates of an old full message (message and encoding randomness of the
old code together), Qo those of a fresh pad; a new message is a vector on K ⊕ Qo: the old message,
the old encoding randomness, the pad.
The old code is read at long positions x : P; a long symbol has the coordinates c : Co; G x c is the
row of the old encoder, under the verifier's way of reading, for the coordinate c of the long symbol
at x.
  y: the long word that the verifier can read (any table).
  form, tgt: the old claim: the linear form "form" has the value tgt at the old full message (a form
  on messages is 0 on the randomness).
  `LdSwIn`: the old claim, relaxed, with its witness v: y differs from the long word of v at no more
    than e long positions, and form at v is tgt. There is no decoder: y may have several such v.
  Lst: the new messages that are represented in the list of the word that the prover has just sent
  (any set of vectors here).
The data of a switch (`LdSwW`): G; a sample map Zo on new messages (Cb/Gen/OodDec.lean); the number
t of long positions that the verifier draws; a zero-evader Zb (Cb/Gen/BatEvader.lean) with one
coefficient for each row (`LdRow`).
  `gap`: row (`rows`) at u minus claimed value (`vals`).
The course. The prover has sent a word (here: Lst); the verifier draws a seed ρo; the prover names
answers ans; the verifier draws, in one message, the list Qs of t long positions and the seed ρb of
the coefficients.
The bad values.
  `Bad1` ρo: two different members of Lst have the same answers at ρo (`Cb.Ood.Clash`). It does not
    mention the prover's answers.
  `Bad2a` Qs: ρo was not bad, and some member u of Lst has all gaps 0 at Qs, though its old part is
    no witness of the relaxed old claim.
  `Bad2b` (Qs, ρb): some member u of Lst has a gap other than 0 at Qs, and yet the combination of
    its gaps with the coefficients of ρb is 0.
  `Bad2`: the one or the other: the bad values of the second verifier message.

Main names:
  `Spec.cnt_ldSwBad1`: a list of at most L members, and `W.Zo.OK`: at most (L choose 2) · Zo.err bad
    seeds; twice their number is at most L² · Zo.err.
  `Spec.cnt_ldSwBad2a`: at most (|P| - e - 1)^t lists Qs: after a good seed at most one member of
    the list has the answers, so the word that is compared with y is fixed before Qs is drawn. No
    list size in this term.
  `Spec.cnt_ldSwBad2b`: a list of at most L members, and `W.Zb.OK`: at every Qs at most L · Zb.err
    seeds ρb.
  `Spec.cnt_ldSwBad2`: under the same two hypotheses, together at most
    (|P| - e - 1)^t · |seeds of Zb| + |P|^t · (L · Zb.err) values of (Qs, ρb);
    as a probability ((|P| - e - 1)/|P|)^t + L · Zb.err / |seeds|.
  `Spec.ldSw_back`: the backward step: no bad value, u in Lst, the new claim (`form'`, `tgt'`) holds
    of u: then the old part of u is a witness of the relaxed old claim.
  `Spec.ldSw_complete`: y the long word of v, form at v = tgt, the true answers of (v, pad): the new
    claim holds of (v, pad), for every pad, ρo, Qs, ρb.

Limits: the statements say nothing on the sizes of L, Zo.err, Zb.err; a bound that exceeds the
number of values says nothing.
For t = 0 the first term of `Spec.cnt_ldSwBad2` is everything.
They say nothing on hiding (Cb/Ld/LdSwitch.lean), on protocols, on running times or succinctness of
forms.
DECLARED DIFFERENCES to the paper that this protocol builds on (lean/CREDITS.md).
(1) There a finite ring, a module over it for forms, targets and symbols, coefficients in the
    centre; here one field for all of them. Distances are counts of long positions: with e the
    integer part of δ |P|, (|P| - e - 1)/|P| < 1 - δ.
(2) There the old form reads the message part only and is 0 on the old randomness and on the pad;
    here it is any form on old full messages (Cb/Ld/LdSwitch.lean feeds a form that is 0 on the
    randomness).
(3) There L is the number of codewords of the new code, under its transformation, within the new
    distance of the word sent; here Lst holds the messages that these codewords represent, which are
    as many or fewer (two codewords may share a message), so a bound on the codewords is a bound on
    Lst; Cb/Ld/LdSwitch.lean feeds the number of pairs (message, randomness), which for an injective
    encoder is the text's L.
(4) There the witness of a relaxed claim also holds the corrected word, and the extractor encodes
    anew to give it; here that word is a function of v (`ldWord G v`) and is not written.
(5) There y is the transform of some native word; here any table.
(6) There the numbers of answers, of drawn positions and of coordinates of a long symbol are at
    least 1; here 0 is allowed.
All but (1) make the statements here wider.
The construction restates, in our own words, one of that text (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDec

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

/-- The names of the rows that a code switch batches: the old claim; the answers of the sample; the
coordinates of the long symbols at the drawn positions. -/
abbrev LdRow (S : Type) (t : ℕ) (Co : Type) : Type := Unit ⊕ S ⊕ Fin t × Co

/-- The data of a code switch on vectors. -/
structure LdSwW (E K Qo P Co : Type) where
  /-- the old encoder under the verifier's way of reading: the row for the coordinate c of the long
  symbol at x -/
  G  : P → Co → K → E
  /-- the sample on new messages -/
  Zo : Sample E (K ⊕ Qo)
  /-- the number of long positions that the verifier draws -/
  t  : ℕ
  /-- the coefficients of the batching -/
  Zb : Evader E (LdRow Zo.S t Co)

section Defs
variable {E K Qo P Co : Type}

/-- The old part of a new message. -/
def ldOld (u : K ⊕ Qo → E) : K → E := fun k => u (Sum.inl k)

/-- Old full message and pad, as a new message. -/
def ldNew (v : K → E) (ro : Qo → E) : K ⊕ Qo → E := Sum.elim v ro

/-- Two long words differ at no more than e long positions. -/
def LdNear [Finite P] (e : ℕ) (y y' : P → Co → E) : Prop := cnt (fun x => y x ≠ y' x) ≤ e

variable [Field E]

/-- A form on old full messages, as a form on new messages: 0 on the pad. -/
def ldPad (f : K → E) : K ⊕ Qo → E := Sum.elim f fun _ => 0

/-- The value of a form at a vector. -/
def ldAt {N : Type} [Fintype N] (f u : N → E) : E := ∑ n, f n * u n

/-- The long word of an old full message. -/
def ldWord [Fintype K] (G : P → Co → K → E) (v : K → E) : P → Co → E := fun x c => ldAt (G x c) v

/-- The old claim, relaxed, with its witness v. -/
def LdSwIn [Fintype K] [Finite P] (G : P → Co → K → E) (e : ℕ) (form : K → E) (tgt : E)
    (y : P → Co → E) (v : K → E) : Prop :=
  LdNear e y (ldWord G v) ∧ ldAt form v = tgt

namespace LdSwW
variable (W : LdSwW E K Qo P Co)

/-- The verifier's second message: the list of long positions, the seed of the coefficients. -/
abbrev Ch2 : Type := (Fin W.t → P) × W.Zb.D

/-- The rows, as forms on new messages. -/
def rows (form : K → E) (ρo : W.Zo.D) (Qs : Fin W.t → P) : LdRow W.Zo.S W.t Co → K ⊕ Qo → E
  | .inl _ => ldPad form
  | .inr (.inl s) => W.Zo.mat ρo s
  | .inr (.inr ic) => ldPad (W.G (Qs ic.1) ic.2)

/-- The values claimed for the rows. -/
def vals (tgt : E) (ans : W.Zo.S → E) (y : P → Co → E) (Qs : Fin W.t → P) : LdRow W.Zo.S W.t Co → E
  | .inl _ => tgt
  | .inr (.inl s) => ans s
  | .inr (.inr ic) => y (Qs ic.1) ic.2

variable [Fintype K] [Fintype Qo] [Fintype Co]

/-- Row at u minus claimed value. -/
def gap (form : K → E) (tgt : E) (y : P → Co → E) (ρo : W.Zo.D) (ans : W.Zo.S → E)
    (Qs : Fin W.t → P) (u : K ⊕ Qo → E) : LdRow W.Zo.S W.t Co → E :=
  fun ν => ldAt (W.rows form ρo Qs ν) u - W.vals tgt ans y Qs ν

/-- The new form: the rows, batched into one. -/
def form' (form : K → E) (ρo : W.Zo.D) (c : W.Ch2) : K ⊕ Qo → E := fun n =>
  ∑ ν, W.Zb.ze c.2 ν * W.rows form ρo c.1 ν n

/-- The new target: the values, batched into one. -/
def tgt' (tgt : E) (ans : W.Zo.S → E) (y : P → Co → E) (c : W.Ch2) : E :=
  ∑ ν, W.Zb.ze c.2 ν * W.vals tgt ans y c.1 ν

/-- The bad seeds of the sample. -/
def Bad1 (Lst : (K ⊕ Qo → E) → Prop) (ρo : W.Zo.D) : Prop := Clash Lst W.Zo.val ρo

/-- The bad lists of long positions. -/
def Bad2a [Finite P] (Lst : (K ⊕ Qo → E) → Prop) (e : ℕ) (form : K → E) (tgt : E) (y : P → Co → E)
    (ρo : W.Zo.D) (ans : W.Zo.S → E) (Qs : Fin W.t → P) : Prop :=
  ¬ W.Bad1 Lst ρo ∧
    ∃ u, Lst u ∧ W.gap form tgt y ρo ans Qs u = 0 ∧ ¬ LdSwIn W.G e form tgt y (ldOld u)

/-- The bad seeds of the coefficients, at a list of long positions. -/
def Bad2b (Lst : (K ⊕ Qo → E) → Prop) (form : K → E) (tgt : E) (y : P → Co → E) (ρo : W.Zo.D)
    (ans : W.Zo.S → E) (c : W.Ch2) : Prop :=
  ∃ u,
    Lst u ∧ W.gap form tgt y ρo ans c.1 u ≠ 0 ∧
    ∑ ν, W.Zb.ze c.2 ν * W.gap form tgt y ρo ans c.1 u ν = 0

/-- The bad values of the second verifier message. -/
def Bad2 [Finite P] (Lst : (K ⊕ Qo → E) → Prop) (e : ℕ) (form : K → E) (tgt : E) (y : P → Co → E)
    (ρo : W.Zo.D) (ans : W.Zo.S → E) (c : W.Ch2) : Prop :=
  W.Bad2a Lst e form tgt y ρo ans c.1 ∨ W.Bad2b Lst form tgt y ρo ans c

/-- The two errors, as counts. -/
def err1 (L : ℕ) : ℕ := L.choose 2 * W.Zo.err
def err2 [Fintype P] (e L : ℕ) : ℕ :=
  (Fintype.card P - e - 1) ^ W.t * Fintype.card W.Zb.D + Fintype.card P ^ W.t * (L * W.Zb.err)

end LdSwW
end Defs

namespace Spec
section
variable (E K Qo P Co : Type)
  [Field E] [Fintype E] [Fintype K] [Fintype Qo] [Fintype P] [Fintype Co]

/-- The first error. -/
def cnt_ldSwBad1 : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (Lst : (K ⊕ Qo → E) → Prop) (L : ℕ), ListLE Lst L → W.Zo.OK →
    cnt (W.Bad1 Lst) ≤ W.err1 L ∧ 2 * cnt (W.Bad1 Lst) ≤ L ^ 2 * W.Zo.err

/-- The second error, first part: the lists of long positions. -/
def cnt_ldSwBad2a : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (Lst : (K ⊕ Qo → E) → Prop) (e : ℕ) (form : K → E) (tgt : E)
      (y : P → Co → E) (ρo : W.Zo.D) (ans : W.Zo.S → E),
    cnt (W.Bad2a Lst e form tgt y ρo ans) ≤ (Fintype.card P - e - 1) ^ W.t

/-- The second error, second part: the seeds of the coefficients, at every list of long
positions. -/
def cnt_ldSwBad2b : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (Lst : (K ⊕ Qo → E) → Prop) (L : ℕ) (form : K → E) (tgt : E)
      (y : P → Co → E) (ρo : W.Zo.D) (ans : W.Zo.S → E) (Qs : Fin W.t → P),
    ListLE Lst L → W.Zb.OK →
    cnt (fun ρb : W.Zb.D => W.Bad2b Lst form tgt y ρo ans (Qs, ρb)) ≤ L * W.Zb.err

/-- The second error. -/
def cnt_ldSwBad2 : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (Lst : (K ⊕ Qo → E) → Prop) (e L : ℕ) (form : K → E) (tgt : E)
      (y : P → Co → E) (ρo : W.Zo.D) (ans : W.Zo.S → E),
    ListLE Lst L → W.Zb.OK → cnt (W.Bad2 Lst e form tgt y ρo ans) ≤ W.err2 e L

end

section
variable (E K Qo P Co : Type) [Field E] [Fintype K] [Fintype Qo] [Fintype Co]

/-- What the new claim says of a new message. -/
def ldSw_eq_iff : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (form : K → E) (tgt : E) (y : P → Co → E) (ρo : W.Zo.D)
      (ans : W.Zo.S → E) (c : W.Ch2) (u : K ⊕ Qo → E),
    ldAt (W.form' form ρo c) u = W.tgt' tgt ans y c ↔
    ∑ ν, W.Zb.ze c.2 ν * W.gap form tgt y ρo ans c.1 u ν = 0

/-- What "all gaps are 0" says. -/
def ldSw_gap_iff : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (form : K → E) (tgt : E) (y : P → Co → E) (ρo : W.Zo.D)
      (ans : W.Zo.S → E) (Qs : Fin W.t → P) (u : K ⊕ Qo → E),
    W.gap form tgt y ρo ans Qs u = 0 ↔
    ldAt form (ldOld u) = tgt ∧ W.Zo.val ρo u = ans ∧ ∀ i, ldWord W.G (ldOld u) (Qs i) = y (Qs i)

/-- The backward step. -/
def ldSw_back [Finite P] : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (Lst : (K ⊕ Qo → E) → Prop) (e : ℕ) (form : K → E) (tgt : E)
      (y : P → Co → E) (ρo : W.Zo.D) (ans : W.Zo.S → E) (c : W.Ch2) (u : K ⊕ Qo → E),
    ¬ W.Bad1 Lst ρo → ¬ W.Bad2 Lst e form tgt y ρo ans c → Lst u →
    ldAt (W.form' form ρo c) u = W.tgt' tgt ans y c → LdSwIn W.G e form tgt y (ldOld u)

/-- Completeness: no exception. -/
def ldSw_complete : Prop :=
  ∀ (W : LdSwW E K Qo P Co) (form : K → E) (tgt : E) (v : K → E) (ro : Qo → E)
      (ρo : W.Zo.D) (c : W.Ch2),
    ldAt form v = tgt →
    ldAt (W.form' form ρo c) (ldNew v ro) = W.tgt' tgt (W.Zo.val ρo (ldNew v ro)) (ldWord W.G v) c

end
end Spec
end Cb
