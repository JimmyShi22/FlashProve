-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecMin.lean: nearest-codeword decoding among the messages that fit an out-of-domain sample
(the decoder by a constrained minimum). It is a second form of the decoder with samples of
Cb/Gen/OodDec.lean, with two kinds of value.

Definitions and statements (Cb.Spec.ood_*); proofs in Cb/Gen/OodDecMinProofs.lean.

The two forms: `Cb.Ood.pick` has three kinds of value: the only candidate, none, several. The
decoder of this file never says "several": among all objects t (say pairs of a message and encoding
randomness, or tables of full messages) whose message part has the answers it takes those at the
least distance from the word, among these the first in a fixed total order (given by `rank`; it is a
total order if `rank` is injective), and returns its message part if that least distance is within
the radius, else none. With no sample it is nearest-codeword decoding. Where there is no collision
(`Cb.Ood.Coll`) the two forms agree, and both return the only candidate, if there is one:
`ood_decMin_good`, `ood_decMin_pick`. `Cand` (a candidate: a member of the list with the given
answers), `Coll` (two different candidates), `Clash` and the lemma on the number of bad seeds are
those of Cb/Gen/OodDec.lean, unchanged: a protocol may use either form.

Main names:
  `Within dist view e`: the list that a distance defines.
  `First`: t is the first minimizer. The fixed total order is given by a function rank : T → ℕ,
    which the statements that need it ask to be injective (every total order of a finite set is of
    this form). The definitions do not ask it: if rank is not injective there can be several first
    minimizers, and `decMin` takes one of them by choice.
  `decMin`: the decoder, abstract; `decMinS`: for a table of words (objects = tables of full
    messages, distance = number of columns that are off: `Blocks.Off`).
  `ood_first_exists`, `ood_first_unique`: if anything has the answers there is a first minimizer; it
    is unique if rank is injective.
  `ood_decMin_iff`: if rank is injective, `decMin` returns u if and only if u is the message part of
    the first minimizer and that one is within the radius.
  `ood_decMin_none_iff`, `ood_decMin_cand`: `decMin` returns none if and only if there is no
    candidate; what it returns is a candidate.
  `ood_decMin_good`: without a collision: `decMin` returns u if and only if u is a candidate. (No
    hypothesis on rank: the order does not matter then.)
  `ood_decMin_pick`: without a collision `decMin` is `pick` (with none for "none"); always: the one
    says none if and only if the other does.
  `ood_decMinS_good`, `ood_decMinS_main`: for tables: outside the bad seeds of the table (`ClashS`),
    for every answer; and as one count, under a bound on the list and `Sample.OK`.
  `ood_decMinS_near`, `ood_decMinS_mulVec`: under `HasDist G d`, at every seed: for a table within
    e' ≤ e columns of the codewords of M, with e + e' < d, and the true answers of M, `decMinS`
    returns the view of M; with the same answers, decoding undoes encoding for every e < d.

Limits: at a collision `decMin` returns one of the candidates, and which one depends on distances
and on the order: nothing is claimed about it beyond `ood_decMin_iff`. If rank is not injective,
which one depends on the choice too, and `ood_decMin_iff` does not apply. No relaxed relation, no
protocol, nothing on hiding or running times.
Where twice the radius is below d, what `decMinS` returns does
not depend on rank: `ood_decMinS_unique` (under `HasDist G d`; for any rank); so for `LdIx.dec`:
`ldFe_unique` (Cb/Ld/LdFoldEq.lean).

The nearest-codeword form with a fixed order follows the worked example named in lean/CREDITS.md.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDec
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Ood
open Prob Blocks

/-- The list that a distance defines. -/
def Within {T U : Type} (dist : T → ℕ) (view : T → U) (e : ℕ) (u : U) : Prop :=
  ∃ t, dist t ≤ e ∧ view t = u

/-- The first minimizer among the objects whose message part has the answers. -/
def First {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y)
    (ρ : D) (y : Y) (t : T) : Prop :=
  ev ρ (view t) = y ∧
  ∀ t', ev ρ (view t') = y → dist t < dist t' ∨ (dist t = dist t' ∧ rank t ≤ rank t')

open Classical in
/-- The decoder by a constrained minimum: the message part of the first minimizer (of one of them,
taken by choice, if rank is not injective), if it is within the radius; else none. -/
def decMin {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y)
    (e : ℕ) (ρ : D) (y : Y) : Option U :=
  if h : ∃ t, First dist rank view ev ρ y t ∧ dist t ≤ e then some (view h.choose) else none

/-- The same for a table of words. -/
def decMinS {E ι κ R J : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J]
    (G : Matrix ι κ E) (e : ℕ) (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E)
    (Z : Sample E J) (f : R → ι → E) (ρ : Z.D) (y : Z.S → E) : Option (J → E) :=
  decMin (fun M => cnt (Off G f M)) rank view Z.val e ρ y

end Cb.Ood

namespace Cb.Spec
open Prob Blocks Cb.Ood

def ood_first_exists : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (ρ : D) (y : Y),
    (∃ t, ev ρ (view t) = y) → ∃ t, First dist rank view ev ρ y t

def ood_first_unique : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (ρ : D) (y : Y),
    Function.Injective rank →
    ∀ t t', First dist rank view ev ρ y t → First dist rank view ev ρ y t' → t = t'

def ood_decMin_iff : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
      (ρ : D) (y : Y) (u : U),
    Function.Injective rank →
    (decMin dist rank view ev e ρ y = some u ↔
      ∃ t, First dist rank view ev ρ y t ∧ dist t ≤ e ∧ view t = u)

def ood_decMin_none_iff : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ) (ρ : D) (y : Y),
    decMin dist rank view ev e ρ y = none ↔ ∀ u, ¬ Cand (Within dist view e) ev ρ y u

def ood_decMin_cand : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
      (ρ : D) (y : Y) (u : U),
    decMin dist rank view ev e ρ y = some u → Cand (Within dist view e) ev ρ y u

/-- Without a collision there is at most one candidate. -/
def ood_one_cand : Prop :=
  ∀ (U D Y : Type) (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (y : Y),
    ¬ Coll Lst ev ρ y → ∀ u u', Cand Lst ev ρ y u → Cand Lst ev ρ y u' → u = u'

/-- Without a collision the decoder returns the only candidate, if there is one, whatever the
order. -/
def ood_decMin_good : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ) (ρ : D) (y : Y),
    ¬ Coll (Within dist view e) ev ρ y →
    ∀ u, decMin dist rank view ev e ρ y = some u ↔ Cand (Within dist view e) ev ρ y u

/-- The two forms of the decoder. -/
def ood_decMin_pick : Prop :=
  ∀ (T U D Y : Type) (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ) (ρ : D) (y : Y),
    (decMin dist rank view ev e ρ y = none ↔ pick (Within dist view e) ev ρ y = .none) ∧
    (¬ Coll (Within dist view e) ev ρ y →
      decMin dist rank view ev e ρ y = (pick (Within dist view e) ev ρ y).opt)

def ood_within_inList : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ)
      (view : (R → κ → E) → J → E) (f : R → ι → E),
    Within (fun M => cnt (Off G f M)) view e = InList G e view f

/-- Outside the bad seeds of the table, for every answer: the view of whatever is within the radius
and has the answers is what the decoder returns. -/
def ood_decMinS_good : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
      (e : ℕ) (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J)
      (f : R → ι → E) (ρ : Z.D),
    ¬ ClashS G e view Z f ρ →
    ∀ (y : Z.S → E) (u : J → E),
      decMinS G e rank view Z f ρ y = some u ↔ (∃ M, DecodesTo G e f M ∧ view M = u) ∧ Z.val ρ u = y

/-- All in one count. -/
def ood_decMinS_main : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
      (e : ℕ) (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J)
      (f : R → ι → E) (L : ℕ),
    ListLE (DecodesTo G e f) L → Z.OK →
    cnt (fun ρ : Z.D =>
        ∃ (y : Z.S → E) (M : R → κ → E),
          DecodesTo G e f M ∧
          Z.val ρ (view M) = y ∧
          decMinS G e rank view Z f ρ y ≠ some (view M)) ≤
      L.choose 2 * Z.err

def ood_decMinS_near : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E)
      (d e e' : ℕ) (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J)
      (f : R → ι → E) (M : R → κ → E),
    HasDist G d → e' ≤ e → e + e' < d → DecodesTo G e' f M →
    ∀ ρ : Z.D, decMinS G e rank view Z f ρ (Z.val ρ (view M)) = some (view M)

def ood_decMinS_mulVec : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (d e : ℕ)
      (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (M : R → κ → E),
    HasDist G d → e < d →
    ∀ ρ : Z.D,
      decMinS G e rank view Z (fun a => G.mulVec (M a)) ρ (Z.val ρ (view M)) = some (view M)

/-- The guard: under `HasDist G d`, for 2 e < d, `decMinS` returns u if and only if the table
decodes, u is the view of `Blocks.dec`, and u has the answers. -/
def ood_decMinS_unique : Prop :=
  ∀ (E ι κ R J : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] (G : Matrix ι κ E) (d e : ℕ)
      (rank : (R → κ → E) → ℕ) (view : (R → κ → E) → J → E) (Z : Sample E J) (f : R → ι → E)
      (ρ : Z.D) (y : Z.S → E) (u : J → E),
    HasDist G d → 2 * e < d →
    (decMinS G e rank view Z f ρ y = some u ↔ Decodes G e f ∧ view (dec G e f) = u ∧ Z.val ρ u = y)

end Cb.Spec
