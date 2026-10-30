-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/BatEvader.lean: many linear claims are reduced to one by a random linear combination whose
coefficients are computed from a seed (batching of linear rows by a zero-evader), on vectors.
Definitions and statements; the proofs are in Cb/Gen/BatEvaderProofs.lean.

A block (`Blocks.Block`, Blocks/Block.lean) is a step of a protocol on vectors. Its three
properties are soundness (`Block.Clean`: round-by-round soundness, the error of each round being a
count of bad verifier messages), completeness (`Hon.AccOn`) and masked form (`Hon.Masked`, both in
Blocks/BlockHon.lean).

The protocol. Claim: each of the rows f_j (j in a finite set J) has the value 0. A row with its
target is one form (`Blocks.Forms`, `Blocks.Form`: affine in the entries; the target is minus the
constant term), and its value is "row times message minus target". The prover sends nothing. The
verifier sends a seed ρ. New claim: the one form ∑_j ze(ρ)_j f_j has the value 0; this is the row
ze(ρ)·Λ with the target ze(ρ)·t (`Spec.comb_form`).

Main names:
  `Evader`: a zero-evader, the data: a finite non-empty set D of seeds, ze : D → J → E, and a number
    err.
  `Evader.OK`: its property: every vector v ≠ 0 is annihilated (∑_j ze(ρ)_j v_j = 0) by at most err
    seeds. It is a hypothesis of the statements, not a field of the data.
  `batB`: the block on forms.
  `batS`: the same block with a state: the explicit input is any x, the rows are a function of x,
    the output is (x, ρ), which determines the one form. This is the print's shape
    (state, then state with the seed).
  `batK`: the block on forms with rows that are kept (the J' rows).
  `Evader.indep`: independent coefficients.
  `Evader.powers`: the powers of one challenge, J = Fin n.
  `Evader.eqPt`: the equality kernel at a point: J = the vertices of a cube with v variables,
    err = v |E|^(v-1).
  `Evader.comap`: an evader for fewer rows.
  `Spec.clean_batB`, `Spec.clean_batS`: if the evader has its property (`Z.OK`), soundness from "all
    J values are 0" to "the one value is 0", with at most err bad seeds.
  `Spec.accOn_batB`, `Spec.accOn_batS`: completeness, from any relation of the honest run under
    which the claim is true; `Spec.withheld_batB`, `Spec.withheld_batS`: at every seed (nothing is
    withheld, the verifier never rejects).
  `Spec.masked_batB`, `Spec.masked_batS`: masked form: no pad is spent, none is read, the plain part
    is empty.
  `Spec.clean_batK` (again if `Z.OK`), `Spec.accOn_batK` (again from any relation of the honest run
    under which all values, of the J and of the J' rows, are 0), `Spec.withheld_batK`,
    `Spec.masked_batK`: the properties of the block with kept rows.
  `Spec.ok_eqPt`, `Spec.lt_eqPt`, `Spec.ok_comap`: the equality kernel is an evader (its number is
    below the number of seeds if v < |E|); an evader stays one on fewer rows, if the embedding `e`
    is injective.
  `Spec.ok_indep`, `Spec.ok_powers`: these two evaders have the property. `Spec.lt_indep`:
    err · |E| = |D| if J is not empty (the fraction is 1/|E|). `Spec.lt_powers`: err < |D| if
    n ≤ |E|.

Dictionary (the print's notions, in our words ↔ Lean). Linear constraint predicate with
J rows ↔ ∀ j, 𝔉.val y (f j) = 0. Error of the evader, a fraction ↔ err / |D|: here every error is a
count of bad seeds (`Prob.cnt`).

Notation: `𝔉` : `Forms E Y P` (Blocks/RelForm.lean): a system of forms, Y the type of implicit
parts, P the set of places of pads; `Ii`, `Io` : Type: the honest prover's states before and after
(`Hon`, Blocks/BlockHon.lean); `nx` : Ii → Z.D → Io (`batH`); `V` : Ii → Prop: in `Hon.Masked`
(Blocks/BlockHon.lean), validity of the honest state; `(Z.err, ())` : `Err` (Iop/Rbr.lean) of the
block's `shape`: one number for each round, here one round.

Limits: `Evader.OK` with err ≥ |D| holds for free, and soundness with that number says nothing: the
statements are as good as err / |D| is small. This file says nothing on oracles, decoding or
knowledge soundness.
No difference to the print in this block: the seed is drawn from all of D there too,
nobody divides by it, and completeness is perfect.
Terms: lean/GLOSSARY.md.
"The print": a print of this protocol's technical report (lean/CREDITS.md); it is
not in this repository.
-/
import Blocks.BlockLib
import Blocks.RelForm
import Alg.Poly
import Blocks.ClosingBlock
import Cb.Gen.Code

set_option autoImplicit false

namespace Cb
open Blocks Iop Prob Alg

/-- A zero-evader: the data. -/
structure Evader (E J : Type) where
  /-- the seeds -/
  D : Type
  [fin : Fintype D]
  [ne : Nonempty D]
  /-- the coefficients that a seed gives -/
  ze : D → J → E
  /-- the number of seeds that may annihilate a vector other than 0 -/
  err : ℕ

attribute [instance] Evader.fin Evader.ne

section
variable {E J : Type} [Field E] [Fintype J]

/-- The property of a zero-evader: a vector other than 0 is annihilated by at most err seeds. -/
def Evader.OK (Z : Evader E J) : Prop :=
  ∀ v : J → E, v ≠ 0 → cnt (fun ρ : Z.D => ∑ j, Z.ze ρ j * v j = 0) ≤ Z.err

/-- the combination under a seed -/
def Evader.comb {M : Type} [AddCommGroup M] [Module E M] (Z : Evader E J) (ρ : Z.D) (f : J → M) :
    M :=
  ∑ j, Z.ze ρ j • f j

/-- Independent coefficients. -/
@[reducible] def Evader.indep (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J] :
    Evader E J :=
  { D := J → E, ze := fun ρ => ρ, err := Fintype.card E ^ (Fintype.card J - 1) }

/-- The powers of one challenge. -/
@[reducible] def Evader.powers (E : Type) [Field E] [Fintype E] (n : ℕ) : Evader E (Fin n) :=
  { D := E, ze := fun γ j => γ ^ (j : ℕ), err := n - 1 }

/-- The equality kernel at a point. -/
@[reducible] def Evader.eqPt (E ι : Type) [Field E] [Fintype E] [Fintype ι] [DecidableEq ι] :
    Evader E (ι → Bool) :=
  { D := ι → E, ze := fun β b => eqk β b,
    err := Fintype.card ι * Fintype.card E ^ (Fintype.card ι - 1) }

omit [Field E] [Fintype J] in
/-- An evader for fewer rows. -/
@[reducible] def Evader.comap {J₀ : Type} (Z : Evader E J₀) (e : J → J₀) : Evader E J :=
  { D := Z.D, ze := fun ρ j => Z.ze ρ (e j), err := Z.err }

variable {X Y P Ii Io : Type}

/-- The batching on forms: J forms in, one form out. -/
@[reducible] def batB (𝔉 : Forms E Y P) (Z : Evader E J) : Block (J → 𝔉.Fm) Y 𝔉.Fm Y :=
  Block.one (Block.chalRound E Z.D) (fun x ρ _ => some (Z.comb ρ x)) (fun y _ _ => y)

/-- its honest side: nothing is sent, nothing is withheld; the state records the seed by nx -/
@[reducible] def batH (𝔉 : Forms E Y P) (Z : Evader E J) (nx : Ii → Z.D → Io) :
    Hon (batB 𝔉 Z) P E Ii Io :=
  Hon.one (fun _ _ => (fun a => Empty.elim a, fun k => Empty.elim k)) nx ∅ fun _ => ∅

/-- the rows that are joined, and the output: the one row, then the rows that are kept -/
def joinedRows {M J' : Type} (x : J ⊕ J' → M) : J → M := fun j => x (.inl j)
def keptRows {M J' : Type} (x : J ⊕ J' → M) (f : M) : Unit ⊕ J' → M :=
  Sum.elim (fun _ => f) fun j' => x (.inr j')

/-- The batching on forms, with rows that are kept. -/
@[reducible] def batK (𝔉 : Forms E Y P) (Z : Evader E J) (J' : Type) :
    Block (J ⊕ J' → 𝔉.Fm) Y (Unit ⊕ J' → 𝔉.Fm) Y :=
  Block.on (batB 𝔉 Z) (joinedRows (J' := J')) keptRows (id : Y → Y) (fun (_ : Y) (y : Y) => y)

@[reducible] def batKH (𝔉 : Forms E Y P) (Z : Evader E J) (J' : Type) (nx : Ii → Z.D → Io) :
    Hon (batK 𝔉 Z J') P E Ii Io :=
  Hon.on (batH 𝔉 Z nx) (joinedRows (J' := J')) keptRows (id : Y → Y) (fun (_ : Y) (y : Y) => y)
    (id : Ii → Ii) (fun (_ : Ii) (b : Io) => b)

/-- The batching with a state: the seed joins the state. -/
@[reducible] def batS (X Y : Type) (Z : Evader E J) : Block X Y (X × Z.D) Y :=
  Block.sample X Y E Z.D fun _ => true

@[reducible] def batSH (X Y P : Type) (Z : Evader E J) (nx : Ii → Z.D → Io) :
    Hon (batS X Y Z) P E Ii Io :=
  Hon.sample (P := P) (E := E) X Y (fun _ : Z.D => true) nx

end

namespace Spec

def clean_batB : Prop :=
  ∀ (E J Y P : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J), Z.OK →
    (batB 𝔉 Z).Clean (fun x y => ∀ j, 𝔉.val y (x j) = 0) (fun f y => 𝔉.val y f = 0) (Z.err, ())

def clean_batS : Prop :=
  ∀ (E J X Y P : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P)
      (Z : Evader E J) (rows : X → J → 𝔉.Fm),
    Z.OK → (batS X Y Z).Clean (fun x y => ∀ j, 𝔉.val y (rows x j) = 0)
      (fun xo y => 𝔉.val y (Z.comb xo.2 (rows xo.1)) = 0) (Z.err, ())

/-- Hi is any relation of the honest run under which the claim is true. It is kept (for the input x
of which the output is the combination), the state records the seed, and the new claim holds. -/
def accOn_batB : Prop :=
  ∀ (E J Y P Ii Io : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J)
      (nx : Ii → Z.D → Io) (Hi : Ii → (P → E) → (J → 𝔉.Fm) → Y → Prop),
    (∀ a π x y, Hi a π x y → ∀ j, 𝔉.val y (x j) = 0) →
    (batH 𝔉 Z nx).AccOn Hi fun ao π f y =>
      (∃ a x ρ, Hi a π x y ∧ ao = nx a ρ ∧ f = Z.comb ρ x) ∧ 𝔉.val y f = 0

def accOn_batS : Prop :=
  ∀ (E J X Y P Ii Io : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J)
      (rows : X → J → 𝔉.Fm) (nx : Ii → Z.D → Io) (Hi : Ii → (P → E) → X → Y → Prop),
    (∀ a π x y, Hi a π x y → ∀ j, 𝔉.val y (rows x j) = 0) →
    (batSH X Y P Z nx).AccOn Hi fun ao π xo y =>
      (∃ a, Hi a π xo.1 y ∧ ao = nx a xo.2) ∧ 𝔉.val y (Z.comb xo.2 (rows xo.1)) = 0

/-- Completeness is perfect: no seed is withheld. -/
def withheld_batB : Prop :=
  ∀ (E J Y P Ii Io : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J)
      (nx : Ii → Z.D → Io) (a : Ii),
    (batH 𝔉 Z nx).withheld a = ∅

def withheld_batS : Prop :=
  ∀ (E J X Y P Ii Io : Type) [Field E] [Fintype J] (Z : Evader E J) (nx : Ii → Z.D → Io) (a : Ii),
    (batSH X Y P Z nx).withheld a = ∅

def masked_batB : Prop :=
  ∀ (E J Y P Ii Io : Type) [Field E] [Fintype E] [Fintype J] [Fintype P] [DecidableEq P]
      (𝔉 : Forms E Y P) (Z : Evader E J) (nx : Ii → Z.D → Io) (V : Ii → Prop),
    (batH 𝔉 Z nx).Masked V ∅ ∅ fun _ => PMF.pure ((fun k => Empty.elim k), ())

def masked_batS : Prop :=
  ∀ (E J X Y P Ii Io : Type) [Field E] [Fintype E] [Fintype J] [Fintype P] [DecidableEq P]
      (Z : Evader E J) (nx : Ii → Z.D → Io) (V : Ii → Prop),
    (batSH X Y P Z nx).Masked V ∅ ∅ fun _ => PMF.pure ((fun k => Empty.elim k), ())

def clean_batK : Prop :=
  ∀ (E J J' Y P : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J), Z.OK →
    (batK 𝔉 Z J').Clean (fun x y => ∀ k, 𝔉.val y (x k) = 0)
      (fun x y => ∀ k, 𝔉.val y (x k) = 0) (Z.err, ())

def accOn_batK : Prop :=
  ∀ (E J J' Y P Ii Io : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J)
      (nx : Ii → Z.D → Io) (Hi : Ii → (P → E) → (J ⊕ J' → 𝔉.Fm) → Y → Prop),
    (∀ a π x y, Hi a π x y → ∀ k, 𝔉.val y (x k) = 0) →
    (batKH 𝔉 Z J' nx).AccOn Hi fun ao π xo y =>
      (∃ a x ρ, Hi a π x y ∧ ao = nx a ρ ∧ xo = keptRows x (Z.comb ρ (joinedRows x))) ∧
      ∀ k, 𝔉.val y (xo k) = 0

def withheld_batK : Prop :=
  ∀ (E J J' Y P Ii Io : Type) [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J)
      (nx : Ii → Z.D → Io) (a : Ii),
    (batKH 𝔉 Z J' nx).withheld a = ∅

def masked_batK : Prop :=
  ∀ (E J J' Y P Ii Io : Type) [Field E] [Fintype E] [Fintype J] [Fintype P] [DecidableEq P]
      (𝔉 : Forms E Y P) (Z : Evader E J) (nx : Ii → Z.D → Io) (V : Ii → Prop),
    (batKH 𝔉 Z J' nx).Masked V ∅ ∅ fun _ => PMF.pure ((fun k => Empty.elim k), ())

def ok_eqPt : Prop :=
  ∀ (E ι : Type) [Field E] [Fintype E] [Fintype ι] [DecidableEq ι], (Evader.eqPt E ι).OK

def lt_eqPt : Prop :=
  ∀ (E ι : Type) [Field E] [Fintype E] [Fintype ι] [DecidableEq ι],
    Fintype.card ι < Fintype.card E → (Evader.eqPt E ι).err < Fintype.card (Evader.eqPt E ι).D

def ok_comap : Prop :=
  ∀ (E J J₀ : Type) [Field E] [Fintype J] [Fintype J₀] (Z : Evader E J₀) (e : J → J₀),
    Function.Injective e → Z.OK → (Z.comap e).OK

def ok_indep : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J], (Evader.indep E J).OK

def ok_powers : Prop := ∀ (E : Type) [Field E] [Fintype E] (n : ℕ), (Evader.powers E n).OK

def lt_indep : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] [DecidableEq J] [Nonempty J],
    (Evader.indep E J).err * Fintype.card E = Fintype.card (Evader.indep E J).D

def lt_powers : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (n : ℕ),
    n ≤ Fintype.card E → (Evader.powers E n).err < Fintype.card (Evader.powers E n).D

/-- Row and target of the output: the combinations of the rows and of the targets. -/
def comb_form : Prop :=
  ∀ (E J N : Type) [Field E] [Fintype J] (Z : Evader E J) (ρ : Z.D)
      (f : J → Form N E) (o : Option N),
    Z.comb ρ f o = ∑ j, Z.ze ρ j * f j o

end Spec
end Cb
