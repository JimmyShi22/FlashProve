-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchPriv.lean: private sample maps over one finite field: any sample map is made private
by a random onto block over a pad.

In standard terms: a sample map (Cb/Gen/OodDec.lean) is a family of matrices indexed by seeds; its
answers are the seed's matrix applied to the message. This file extends a sample map by a block of
further columns, a surjective matrix drawn with the seed, over further message coordinates, and
states a bound on the error count (`err`) of the extended map.

Definitions and statements (the statements in `Cb.Spec`); the proofs are in
Cb/Ld/LdSwitchPrivProofs.lean, which also proves `Spec.ldSwitch_blind_of_sim` and
`Spec.ldSwitch_blind_of_private`, which Cb/Ld/LdSwitch.lean states.

Why: the answers of a sample (Cb/Gen/OodDec.lean) are linear functionals of the message. The code
switch wants them to give nothing away. The cure: the message gets further coordinates Qo (a pad of
uniform entries, read by nothing else), and the sample's matrix gets a further block M over them,
drawn with the seed among the matrices that are onto. Then the pad's share M · pad of the answers is
uniform, whatever the seed, and hides the rest. The price is a second way to annihilate a vector:
its pad part r ≠ 0 may be sent by M to minus what the first block gives.
The code switch of Cb/Ld/LdSwitch.lean takes any sample map that is blind; this file shows that
there is always one (with `Spec.ldSwitch_blind_of_private`, Cb/Ld/LdSwitch.lean); that an onto
matrix exists is an instance argument of `Sample.boot` (`Spec.ldPriv_nonempty`: |S| ≤ |Qo|). Under
the hypotheses of its statement, the row with a pad of Cb/Gen/OodDecPad.lean is another private
sample map in this sense: `(Sample.pad E μ J₀ P B pl w b).Private F fun ρ => b ρ.2 ≠ 0`
(`Spec.ood_private_pad`), with a much shorter seed and for messages over a smaller field; a protocol
that takes that row does not call this file.

Main names (E is a finite field; S names the answers, Qo the pad coordinates; both are finite):
  `Sample.boot Z Qo`: the sample map with the block: err = the larger of Z.err · (number of onto
    matrices) and (number of seeds of Z) · mxErr (the number of the block). As fractions of the
    seeds: the larger of the error of Z and of mxErr / (number of onto matrices). It needs that
    there is an onto matrix (an instance argument; `Spec.ldPriv_nonempty` says when).
  `Spec.ldPriv_nonempty`: there is an onto matrix if and only if |S| ≤ |Qo|.
  `Spec.ldPriv_le_mxErr`, `Spec.ldPriv_mxErr_le`: mxErr bounds every count of onto M with M r = t
    (for r ≠ 0), and is the least such bound.
  `Spec.ldPriv_fibre`: the bound: for r ≠ 0 and every t:
    (number of onto M with M r = t) · (|E|^|S| - 1) ≤ number of onto matrices.
  `Spec.ldPriv_mxErr_bound`: so mxErr · (|E|^|S| - 1) ≤ number of onto matrices: as a fraction at
    most 1 / (|E|^|S| - 1).
  `Spec.ldPriv_val_boot`: the answers: those of Z on the entries proper, plus M applied to the pad.
  `Spec.ldPriv_ok_boot`: if Z has the property of a sample map (`Sample.OK`, Cb/Gen/OodDec.lean: a
    vector other than 0 has all answers 0 for at most err seeds), so has Z.boot.
  `Spec.ldPriv_private_boot`: at every seed and for all entries proper the answers, over a uniform
    pad, are uniform (`Sample.Private` of Cb/Gen/OodDecPad.lean, with F = E).
  `Spec.ldPriv_sim_boot`: hence privacy with a simulator, error 0 (`Sample.PrivateSim`): uniform
    seed, uniform answers.

Limits: for |S| = 0 the bound `Spec.ldPriv_fibre` (and with it `Spec.ldPriv_mxErr_bound`,
`Spec.ldPriv_frac_boot`) says nothing (its factor is 0), and mxErr is then the number of onto
matrices (one) if the pad is not empty.
This file says nothing on privacy jointly with opened positions of an encoding (Cb/Ld/LdSwitch.lean
puts the two together).
It says nothing on running times.
DECLARED DIFFERENCES to the paper that this protocol builds on (lean/CREDITS.md).
There a finite ring and a module over it for the entries of matrices and answers, and a matrix is
admitted if its columns span all tuples of answers over the ring; the general statement takes the
number of the block as it is, and the bound is proved for a field. Here one finite field throughout.
There the number of answers is at least 1 in the bound; here 0 is allowed and the bound is then
empty.
There privacy is defined with a simulator and a statistical error; here the two exact forms of
Cb/Gen/OodDecPad.lean.
The construction restates, in our own words, one of that text (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecPad
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Ood
open Prob

/-- A matrix applied to a vector. -/
def mxApp {E S Qo : Type} [Field E] [Fintype Qo] (M : S → Qo → E) (r : Qo → E) : S → E := fun s =>
  ∑ q, M s q * r q

/-- The matrix is onto: its columns span E^S. -/
def MxOnto {E S Qo : Type} [Field E] [Fintype Qo] (M : S → Qo → E) : Prop :=
  Function.Surjective (mxApp M)

/-- The onto matrices. -/
abbrev OntoMx (E S Qo : Type) [Field E] [Fintype Qo] : Type := {M : S → Qo → E // MxOnto M}

instance OntoMx.fintype
    (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo] : Fintype (OntoMx E S Qo) :=
  Fintype.ofFinite _

open Classical in
/-- The number of the block: the largest, over r ≠ 0 and t, of the number of onto matrices that send
r to t. -/
def mxErr (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo] : ℕ :=
  Finset.univ.sup fun x : (Qo → E) × (S → E) =>
    if x.1 = 0 then 0 else cnt fun M : OntoMx E S Qo => mxApp M.1 x.1 = x.2

/-- A sample map with a random onto block over a pad. -/
@[reducible] def Sample.boot {E J₀ : Type} [Field E] [Fintype E] (Z : Sample E J₀)
    (Qo : Type) [Fintype Qo] [Nonempty (OntoMx E Z.S Qo)] : Sample E (J₀ ⊕ Qo) :=
  { D := Z.D × OntoMx E Z.S Qo, S := Z.S, mat := fun ρ s => Sum.elim (Z.mat ρ.1 s) (ρ.2.1 s),
    err := max (Z.err * Fintype.card (OntoMx E Z.S Qo)) (Fintype.card Z.D * mxErr E Z.S Qo) }

end Cb.Ood

namespace Cb.Spec
open Prob Cb.Ood

def ldPriv_nonempty : Prop :=
  ∀ (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo],
    Nonempty (OntoMx E S Qo) ↔ Fintype.card S ≤ Fintype.card Qo

def ldPriv_le_mxErr : Prop :=
  ∀ (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo] (r : Qo → E) (t : S → E),
    r ≠ 0 → cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t) ≤ mxErr E S Qo

def ldPriv_mxErr_le : Prop :=
  ∀ (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo] (k : ℕ),
    (∀ (r : Qo → E) (t : S → E), r ≠ 0 → cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t) ≤ k) →
    mxErr E S Qo ≤ k

/-- The bound. -/
def ldPriv_fibre : Prop :=
  ∀ (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo] (r : Qo → E) (t : S → E), r ≠ 0 →
    cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t) * (Fintype.card E ^ Fintype.card S - 1) ≤
      Fintype.card (OntoMx E S Qo)

def ldPriv_mxErr_bound : Prop :=
  ∀ (E S Qo : Type) [Field E] [Fintype E] [Fintype S] [Fintype Qo],
    mxErr E S Qo * (Fintype.card E ^ Fintype.card S - 1) ≤ Fintype.card (OntoMx E S Qo)

def ldPriv_val_boot : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo] (Z : Sample E J₀)
      [Nonempty (OntoMx E Z.S Qo)] (ρ : Z.D) (M : OntoMx E Z.S Qo) (a : J₀ → E) (r : Qo → E),
    (Z.boot Qo).val (ρ, M) (Sum.elim a r) = Z.val ρ a + mxApp M.1 r

/-- Under the hypotheses below, the property of a sample map is kept. -/
def ldPriv_ok_boot : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo]
      (Z : Sample E J₀) [Nonempty (OntoMx E Z.S Qo)],
    Z.OK → (Z.boot Qo).OK

/-- Its number (`err`) against the number of seeds: the fraction is at most the larger of the error
of Z and 1 / (|E|^|S| - 1). (for |S| = 0: see Limits in the head) -/
def ldPriv_frac_boot : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype Qo]
      (Z : Sample E J₀) [Nonempty (OntoMx E Z.S Qo)],
    (Z.boot Qo).err * (Fintype.card E ^ Fintype.card Z.S - 1) ≤
      max (Z.err * (Fintype.card E ^ Fintype.card Z.S - 1)) (Fintype.card Z.D) *
        Fintype.card (OntoMx E Z.S Qo)

/-- Privacy at every seed. -/
def ldPriv_private_boot : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo]
      (Z : Sample E J₀) [Nonempty (OntoMx E Z.S Qo)],
    (Z.boot Qo).Private E fun _ => True

/-- Privacy with a simulator, error 0. -/
def ldPriv_sim_boot : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo]
      (Z : Sample E J₀) [Nonempty (OntoMx E Z.S Qo)],
    (Z.boot Qo).PrivateSim E

end Cb.Spec
