-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecRows.lean: under the hypotheses below, the record hides: an index in rows, one answer for
each row, each answer masked by a pad of its row.

This file is about the record phase of the holographic interactive oracle proof: the verifier's seed
and the prover's answers; for an index in rows (`C.Rows`), one answer for each row of the index.

Definitions, statements and proofs, over a configuration with a record (Hiop/RecConf.lean). No code,
no field occurs here.

Main names, in the order of the argument: `ConfigurationWithOutOfDomainSample.Props` asks that, at every seed, the law of
(answers, the encoded index at any b positions) does not depend on the index (`hides`). Here that
law of the configuration is derived from two facts of another kind:
  `C.Strong b`: the encoding is strong: the law of a word at any b positions, over the encoding
    randomness alone, is the same for every message, pads included. (So the positions are simulated
    for every fixed message.)
  `C.Masked`: the pads mask the answers: at every seed the law of the answers, over the pads alone,
    does not depend on the index.
  `Spec.rec_hides`: `Strong b` and `Masked` give the clause `hides` of `ConfigurationWithOutOfDomainSample.Props` at b;
    `Spec.rec_hides_law`: more exactly, the pair has the law "answers, and independently of them b
    positions of a word of any fixed message".
An index in rows (`C.Rows`: the data; `Rows.Laws`). The rows have names in K. The pads are one pad
for each row; the answers are one answer for each row; the answer of row k to the seed s is a
function `ansRow s` of what the row holds of the index (`lay i k`) and of the row's own pad; and for
every seed and every content of the row that function is a bijection from pads to answers.
  (In the construction: the answer is a constant plus β times the element of the large field that
  the pad's entries spell; that no seed has β = 0 is a hypothesis there (`Cb.Spec.ldCf_padBij_pad`,
  Cb/Obj/LdObjectConf.lean). At β = 0 the law fails; a construction whose seeds may have β = 0 does
  not meet `Rows.Laws`.)
  `Spec.rec_answers_uniform`: then, for every index and every seed, the answers are uniform on K →
    A.
  `Spec.rec_masked_of_rows`: so the pads mask the answers.
  `Spec.rec_hides_of_rows`: and with a strong encoding the record hides.

Limits: why one record only. All this is for one seed. Two records of one encoded index use each pad
twice, and the pads cancel from a combination of the two answers of a row: `Rows.Laws` gives nothing
for the joint law at two seeds. [No theorem here.]
Exact laws (an encoding with a positive error is not covered). This file does not say that every
word has a collision at no more than eR seeds (`ConfigurationWithOutOfDomainSample.Props.rcd`, Hiop/RecConf.lean); it says
nothing on the row that a record gives on a folded row (`Cb.LdIx.RecRow`, Cb/Ld/LdFoldEq.lean).

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecConf
import Prob.LawKit

set_option autoImplicit false

namespace Hiop
open Iop Prob

namespace ConfigurationWithOutOfDomainSample
variable (C : ConfigurationWithOutOfDomainSample)

/-- The encoding is strong. -/
def Strong (b : ℕ) : Prop :=
  ∀ (S : Finset (Fin C.n)), S.card ≤ b →
    ∀ m m', (unif C.Rnd).map (fun r => fun p : S => C.enc m r p) =
      (unif C.Rnd).map (fun r => fun p : S => C.enc m' r p)

/-- The pads mask the answers. -/
def Masked : Prop :=
  ∀ (s : C.Seed) i i', (unif C.Pad).map (fun η => C.smp s (C.hold i η)) =
    (unif C.Pad).map (fun η => C.smp s (C.hold i' η))

/-- the clause "hides" of ConfigurationWithOutOfDomainSample.Props -/
def Hides (b : ℕ) : Prop :=
  ∀ (S : Finset (Fin C.n)), S.card ≤ b →
    ∀ (s : C.Seed) i i',
      (unif (C.Pad × C.Rnd)).map
          (fun r => (C.smp s (C.hold i r.1), fun p : S => C.enc (C.hold i r.1) r.2 p)) =
        (unif (C.Pad × C.Rnd)).map
          (fun r => (C.smp s (C.hold i' r.1), fun p : S => C.enc (C.hold i' r.1) r.2 p))

/-- An index in rows: the data. -/
structure Rows where
  /-- the names of the rows -/
  K    : Type
  /-- what a row holds beside its pad; the pad of one row; an answer -/
  Row  : Type
  PadR : Type
  A    : Type
  [finK : Fintype K]
  [decK : DecidableEq K]
  [finP : Fintype PadR]
  [neP  : Nonempty PadR]
  [finA : Fintype A]
  [neA  : Nonempty A]
  lay  : C.I → K → Row
  /-- the pads: one for each row; the answers: one for each row -/
  pads : C.Pad ≃ (K → PadR)
  answers : C.Ans ≃ (K → A)
  /-- the answer of one row -/
  ansRow : C.Seed → Row → PadR → A

attribute [instance] Rows.finK Rows.decK Rows.finP Rows.neP Rows.finA Rows.neA

variable {C}

structure Rows.Laws (R : C.Rows) : Prop where
  /-- the answer of row k reads that row alone -/
  smp_hold : ∀ s i η k, R.answers (C.smp s (C.hold i η)) k = R.ansRow s (R.lay i k) (R.pads η k)
  /-- the pad masks it -/
  mask     : ∀ s m, Function.Bijective (R.ansRow s m)

end ConfigurationWithOutOfDomainSample

namespace Spec

/-- Under the hypotheses of its statement: The pair has the law "answers, and independently of them
the positions of a word of the fixed message m₀". -/
def rec_hides_law : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (b : ℕ), C.Strong b →
    ∀ (S : Finset (Fin C.n)), S.card ≤ b →
      ∀ (s : C.Seed) (i : C.I) (m₀ : C.Msg),
        (unif (C.Pad × C.Rnd)).map
            (fun r => (C.smp s (C.hold i r.1), fun p : S => C.enc (C.hold i r.1) r.2 p)) =
          ((unif C.Pad).map fun η => C.smp s (C.hold i η)).bind fun a =>
            ((unif C.Rnd).map fun r => fun p : S => C.enc m₀ r p).map fun v => (a, v)

/-- Under the hypotheses of its statement: The record hides. -/
def rec_hides : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (b : ℕ), C.Strong b → C.Masked → C.Hides b

/-- Under the hypotheses of its statement: The answers are uniform. -/
def rec_answers_uniform : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (R : C.Rows), R.Laws →
    ∀ (s : C.Seed) (i : C.I),
      (unif C.Pad).map (fun η => R.answers (C.smp s (C.hold i η))) = unif (R.K → R.A)

def rec_masked_of_rows : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (R : C.Rows), R.Laws → C.Masked

def rec_hides_of_rows : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (R : C.Rows) (b : ℕ), R.Laws → C.Strong b → C.Hides b

end Spec

theorem rec_hides_law : Spec.rec_hides_law := by
  intro C b hS S hb s i m₀
  refine map_unif_bind_factor _ (fun η => C.smp s (C.hold i η)) _ fun η => ?_
  rw [← hS S hb (C.hold i η) m₀, PMF.map_comp]
  rfl

theorem rec_hides : Spec.rec_hides := by
  intro C b hS hM S hb s i i'
  obtain ⟨η₀⟩ := C.nePad
  rw [rec_hides_law C b hS S hb s i (C.hold i η₀),
    rec_hides_law C b hS S hb s i' (C.hold i η₀), hM s i i']

theorem rec_answers_uniform : Spec.rec_answers_uniform := by
  intro C R hR s i
  have e : (fun η => R.answers (C.smp s (C.hold i η))) =
      (R.pads.trans (Equiv.piCongrRight fun k => Equiv.ofBijective _ (hR.mask s (R.lay i k)))) := by
    funext η k
    exact hR.smp_hold s i η k
  rw [e]
  exact map_unif_equiv _

theorem rec_masked_of_rows : Spec.rec_masked_of_rows := by
  intro C R hR s i i'
  have h : ∀ j,
      (unif C.Pad).map (fun η => C.smp s (C.hold j η)) = (unif (R.K → R.A)).map R.answers.symm := by
    intro j
    rw [← rec_answers_uniform C R hR s j, PMF.map_comp]
    refine congrArg (fun F => (unif C.Pad).map F) (funext fun η => ?_)
    exact (R.answers.symm_apply_apply _).symm
  rw [h i, h i']

theorem rec_hides_of_rows : Spec.rec_hides_of_rows := fun C R b hR hS =>
  rec_hides C b hS (rec_masked_of_rows C R hR)

end Hiop
