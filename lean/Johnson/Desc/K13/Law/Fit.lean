-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Fit.lean: the batching of the rows on the committed matrix, as kind K13's text
computes it, is the library's batching of tensor rows with short messages. Definitions and
statements; the proofs are in Johnson/Desc/K13/Law/FitProofs.lean.

K13's text (Johnson/Desc/K13/Text.lean: `batt`) draws one element x, hears a sumcheck, and hands on
the row `Batt.rowOf pile o`, with o what `Psc.run` gives at `Batt.claimOf pile x` and
`Batt.summandOf pile x`. It tests no value. The library's block (`Cb.Pv.BattShort.R`) is proved
knowledge sound (`Cb.Pv.BattShort.hAt`). Here the block's parameters are written for a pile, the
text's rounds are read as a transcript of the block, and three statements tie the two.
Main names:
  `parOf ρ nR k pile`: the library's parameters: the coefficients are the powers of one element, the
    degree is 2, the state is trivial: all that is public lies in the parameters.
  `msgOf ρ w pile fresh`: the entries that the parameters name, read off a witness w.
  `targets`, `trRounds`, `trOf`: the pile's targets; what was heard, as a transcript.
  `outOf`: what the library's verifier puts out on a transcript, as a total function.
  `Spec.inHolds_iff`: all rows of the pile are true exactly if the library's input claim holds.
  `Spec.row_iff`: the row handed on is true exactly if the library's output claim holds of what its
    verifier puts out on the rounds as read.
  `Spec.batt_doomed`: for each fixed witness: a prover has lost, round by round, towards "if the row
    handed on is true, all rows of the pile are true". `Spec.batt_errs`, `Spec.batt_vals`: the
    errors are J - 1, 1, and k times 2, each out of as many values as the field has elements.
Used of `verify-on-bytes`, as data or as pure functions, none of them a routine in a context:
`TensorRow`, `Slot`, `Batt.fits`, `Batt.claimOf`, `Batt.summandOf`, `Batt.rowOf`, `Batt.masksOf`,
`Psc.Heard`, `Psc.Out`, `Psc.run`.

What is not claimed. `batt_doomed` by itself is not the kind's law: it bounds the bad draws for each
fixed witness, while a rule of composition has the witness behind all draws. With the witness free
there the bound does not hold: the witness whose hiding polynomial has the sumcheck's last value as
its constant meets the row handed on, whatever the pile's rows say; that argument is typed in no
file of this folder. The law (Johnson/Desc/K13/Law/Law.lean, Johnson/Desc/K13/Law/Agree.lean) pins
what a row reads of the witness to what was committed. The witness is fixed before x is drawn: that
the matrix and all mask entries that a row names are committed to by then is the caller's. A
transcript here holds elements of the field K; the text hears triples of words: `batt_doomed` speaks
of every hearing that reads as the transcript. Nothing on an honest prover or on hiding: that the
fresh mask entries differ from each other and from those that the pile names is not asked, and
soundness does not need it.

-/
import Johnson.Desc.K13.Law.Means
import OnBytes.Tie.Pv.Psc.StepWalk
import Cb.Pv.BattShort
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd sRounds)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The variables of the batching's sumcheck: k plain variables of degree 2. -/
abbrev fmtOf (K : Type) [Field K] [Fintype K] (k : ℕ) : List (PFmt K) :=
  List.replicate k (pfCube K 2)

/-- The same as variables of a hiding polynomial. -/
abbrev varsOf (K : Type) [Field K] [Fintype K] (k : ℕ) : List (HVar K) :=
  pVars (fmtOf K k) (pdPlains K 2 k)

/-- **The library's parameters for a pile.** The entries: those of the matrix; the coefficients of
the hiding polynomial; for each row of the pile the value of its mask form. -/
@[reducible] noncomputable def parOf (nR k : ℕ) (pile : List TensorRow) : BattPar K where
  St := Unit
  J := (Fin nR × (Fin k → Bool)) ⊕ (PIdx (fmtOf K k) ⊕ Fin pile.length)
  Rw := Fin nR
  k := k
  mAt := Sum.inl
  Q := Fin pile.length
  g := fun _ q => weights ρ nR (pile.get q).g
  pt := fun _ q => rd ρ k (pile.get q).psi
  slM := fun q _ j =>
    match j with
    | .inr (.inr q') => if q' = q then 1 else 0
    | _ => 0
  Z := Evader.powers K pile.length
  n := 2
  wAt := fun i => Sum.inr (Sum.inl i)

variable {nR k : ℕ}

/-- The entries, read off a witness. fresh: the mask entries taken for the hiding polynomial, in the
text's order. -/
noncomputable def msgOf (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot) :
    (parOf ρ nR k pile).J → K
  | .inl a => w.mat a.1 a.2
  | .inr (.inl i) =>
    OnBytes.Road.Hd.place (fun j => w.mask (fresh.getD j default)) (varsOf K k) 0
      ((pIx (fmtOf K k) (pdPlains K 2 k)).symm i)
  | .inr (.inr q) => formVal ρ w.mask (pile.get q).masks

/-- The pile's targets. -/
def targets (pile : List TensorRow) : Fin pile.length → K := fun q => ρ.val (pile.get q).target

/-- The rounds of the variables, as a short transcript. Where the list ends early: zeros. -/
def trRounds : (k : ℕ) → List (List E × E) → Tr (sRounds (fmtOf K k))
  | 0, _ => ()
  | k + 1, [] => (((), fun _ => 0), (0 : K), trRounds k [])
  | k + 1, (q, g) :: rs => (((), rd ρ 2 q), ρ.val g, trRounds k rs)

/-- The element drawn and what was heard, as a transcript of the library's block. -/
def trOf (nR : ℕ) (pile : List TensorRow) (Ex : ExtSpec) (x : E) (h : Psc.Heard) :
    Tr (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape :=
  (((), ()), ρ.val x, ((), ρ.val h.mu), ρ.val h.eps, trRounds ρ k h.rounds)

/-- What the library's verifier puts out, as a total function of the transcript. -/
noncomputable def outOf (nR : ℕ) (pile : List TensorRow) (Ex : ExtSpec)
    (τ : Tr (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape) : (parOf ρ nR k pile).par.Mid :=
  TWhole.shortVC (parOf ρ nR k pile).par (Cb.Pv.BattShort.F₁ (parOf ρ nR k pile))
    ((parOf ρ nR k pile).nx (targets ρ pile, ()) τ.2.1) τ.2.2

namespace Spec

/-- All rows of the pile are true exactly if the library's input claim holds. -/
def inHolds_iff : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ) (w : Wit K nR k)
      (pile : List TensorRow) (fresh : List Slot),
    (parOf ρ nR k pile).InHolds (targets ρ pile, ()) (msgOf ρ w pile fresh) ↔
      ∀ r ∈ pile, Holds ρ w r

/-- The row handed on is true exactly if the library's output claim holds. -/
def row_iff : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ) (w : Wit K nR k)
      (pile : List TensorRow) (fresh : List Slot) (Ex : ExtSpec) (x : E) (h : Psc.Heard)
      (o : Psc.Out),
    Batt.fits k pile = true →
    Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o →
    (Holds ρ w (Batt.rowOf pile o) ↔
      (parOf ρ nR k pile).par.MidHolds (outOf ρ nR pile Ex (trOf ρ nR pile Ex x h))
        (msgOf ρ w pile fresh))

/-- For each fixed witness the prover has lost, round by round, towards: whatever hearing reads as
the transcript, if the row that the text hands on is true, all rows of the pile are true. -/
def batt_doomed : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ) (w : Wit K nR k)
      (pile : List TensorRow) (fresh : List Slot) (Ex : ExtSpec) (_ : Ex.Str),
    Batt.fits k pile = true →
    Doomed (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex)
      fun τ => ∀ (x : E) (h : Psc.Heard) (o : Psc.Out), trOf ρ nR pile Ex x h = τ →
        Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o →
        Holds ρ w (Batt.rowOf pile o) → ∀ r ∈ pile, Holds ρ w r

/-- The errors, round by round. -/
def batt_errs : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ) (pile : List TensorRow)
      (Ex : ExtSpec),
    (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex).toList =
      (pile.length - 1) :: 1 :: List.replicate k 2

/-- The numbers of values of the challenges, round by round. -/
def batt_vals : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ) (pile : List TensorRow)
      (Ex : ExtSpec),
    (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape.chalList =
      Fintype.card K :: Fintype.card K :: List.replicate k (Fintype.card K)

end Spec
end VerifiableInference.Desc.K13.Law
