-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPsc.lean: the pieces of a chain of masked blocks: the sumcheck for a polynomial
summand and the step into a sumcheck, as `MJ` records (Cb/Ld/LdLkpMaskChain.lean); rules for these
records.
This file is about the sumcheck protocol for a polynomial summand, and the verifier's draw that
turns several claims into one sum claim, each as one step of a chain of reductions.

Definitions, and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpMaskPscProofs.lean.

1. Rules for `MJ`.
  `D.Reads S`, `D.Writes S`: messages and claim of D depend on the entries in S only; D's own masks
    lie in S. `Spec.mj_blind_of`: if what the earlier block reads and what the later block writes
    are disjoint, the earlier is blind to the later (`Blind`).
  `D.narrow Cl'`: the same block with a stronger claim (what rides along and is needed by later
    blocks is put into the claim). `Spec.mj_narrow`: it still fits, if the stronger claim does not
    read the own masks. `D.reJ e`: the same block with its entries named otherwise (e : J' ≃ J).
    `Spec.mj_reJ`: see its statement.
2. The sumcheck (Cb/Ld/LdPsc.lean: `PscPar`; item "masked messages": Cb/Ld/LdPscZk.lean).
  `Y.nxtOf Ex x pl ρ`: what the verifier outputs if it accepts, from the explicit part, the plain
    parts and its own messages: state, coefficient, point, last value (the last round polynomial at
    the last challenge), the revealed values.
  `Y.mj Ex O`: the `MJ` record: own masks, claim (the sum claim), closed-form messages and simulator
    are those of `Y.maskData`; `nxt` is `Y.nxtOf`.
  `Spec.mjPsc_fits`: under `Y.VarsOK`, `Y.DegOK`, `Y.OwnOK O`: it fits, with the reading "the
    entries in O.Rd, all others forgotten", if there is at least one variable (the instance with the
    dummy variable always has one).
  `Spec.mjPsc_reads`: it reads the entries in O'.Rd only, for any O' with the same places that meets
    the conditions (so: a small set for blindness, a large one for the common reading of a chain).
  `Spec.mjPsc_writes`: its own masks lie at the places `O.at`.
  `Spec.mjPsc_out`: under `Y.VarsOK`, `Y.DegOK`, and if there is at least one variable: at what the
    honest messages fix, the output rows (`Y.OutHolds`) hold of the entries, whether or not the
    claim held: so the block steps to every claim that the output rows (and what rides along) give.
  `Spec.mjOur_mono`: the conditions `T.OwnOur Rd` of the instance (`PscOur`, Cb/Ld/LdPsc.lean) pass
    to every larger set Rd.
3. The step into a sumcheck (Cb/Ld/LdZero.lean: `PscIn`: zerocheck, line, point of a forest).
   `Z.mj Ex`: the verifier draws a seed: no masks; claim: all claims hold. `Spec.mjIn_fits`: see its
   docstring. `Spec.mjIn_step`: under `Z.Link`, it steps to the sumcheck's claim.

Limits: no chain is assembled here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskChain
import Cb.Ld.LdPscGood
import Cb.Ld.LdZero

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

noncomputable section

namespace MJ
variable {E J J' : Type} {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}

/-- Messages and claim depend on the entries in S only. -/
structure Reads (D : MJ E J R) (S : J → Prop) : Prop where
  msg : ∀ k k' x ρ, (∀ j, S j → k j = k' j) → D.msg k x ρ = D.msg k' x ρ
  cl  : ∀ k k' x, (∀ j, S j → k j = k' j) → D.Cl x k → D.Cl x k'

/-- The own masks lie in S. -/
def Writes (D : MJ E J R) (S : J → Prop) : Prop := ∀ M k j, ¬ S j → D.put M k j = k j

/-- The same block with a stronger claim (the claim `Cl'` in the place of its own; `Spec.mj_narrow`
asks that it be stronger). -/
def narrow (D : MJ E J R) (Cl' : Xi → (J → E) → Prop) : MJ E J R := { D with Cl := Cl' }

/-- The same block, its entries named otherwise. -/
def reJ (D : MJ E J' R) (e : J' ≃ J) : MJ E J R where
  Mk  := D.Mk
  put := fun M k j => D.put M (fun j' => k (e j')) (e.symm j)
  Cl  := fun x k => D.Cl x fun j' => k (e j')
  msg := fun k x ρ => D.msg (fun j' => k (e j')) x ρ
  nxt := D.nxt
  sim := D.sim

end MJ

namespace PscPar
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

/-- What the verifier outputs if it accepts, from the explicit part, the plain parts and its own
messages. -/
def nxtOf (x : E × Y.St) (pl : Plains (Y.psc Ex).shape) (ρ : Rho (Y.psc Ex).shape) : Y.Out :=
  ⟨x.2, Y.zEps Ex ρ, Y.zPt Ex ρ,
    hFin (Y.vars x.2) ((Plains.fst (s := Y.shapeC) (t := [pRoundV E Y.A]) pl).1 + Y.zEps Ex ρ * x.1)
      (pQ Y.fmt (Y.dat x.2) (Plains.fst (s := Y.shapeC) (t := [pRoundV E Y.A]) pl).2)
      (Y.hp x.2 (Y.zPt Ex ρ)),
    (Plains.snd (s := Y.shapeC) (t := [pRoundV E Y.A]) pl).1⟩

/-- The `MJ` record of the sumcheck. -/
def mj (O : Y.Own) : MJ E Y.J (Y.psc Ex) where
  Mk  := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).Mk
  finMk := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).finMk
  neMk := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).neMk
  put := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).put
  Cl  := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).Cl
  msg := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).msg
  nxt := Y.nxtOf Ex
  sim := (Y.maskData Ex (Wt := Y.J → E) (fun m => m) O).sim

end PscPar

/-- The `MJ` record of the step into a sumcheck. -/
def PscIn.mj {E : Type} [Field E] [Fintype E] (Z : PscIn E) (Ex : ExtSpec) :
    MJ E Z.T.J (IOR.draw Z.ev.D Z.nxX Ex) :=
  MJ.silent Z.ev.D Z.nxX Ex Z.AllHold

namespace Spec

def mj_blind_of : Prop :=
  ∀ (E J X₁ X₂ Xi Xo : Type) (E₁ E₂ Ei Eo : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR Xi Ei Xo Eo)
      (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) (S₁ S₂ : J → Prop),
    D₁.Reads S₁ → D₂.Writes S₂ → (∀ j, S₁ j → ¬ S₂ j) → D₁.Blind D₂

def mj_narrow : Prop :=
  ∀ (E J Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MJ E J R) (rdi : Wi → J → E) (rdo : Wo → J → E) (Cl' : Xi → (J → E) → Prop),
    D.Fits H rdi rdo → (∀ x k, Cl' x k → D.Cl x k) →
    (∀ x k M, Cl' x k → Cl' x (D.put M k)) → (D.narrow Cl').Fits H rdi rdo

def mj_reJ : Prop :=
  ∀ (E J J' Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (D : MJ E J' R) (e : J' ≃ J) (rdi : Wi → J → E) (rdo : Wo → J → E),
    D.Fits H (fun w j' => rdi w (e j')) (fun w j' => rdo w (e j')) → (D.reJ e).Fits H rdi rdo

section
variable (E : Type) [Field E] [Fintype E]

/-- States: under the hypotheses below, the sumcheck fits. -/
def mjPsc_fits : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O : Y.Own), Y.VarsOK → Y.DegOK →
    Y.OwnOK O → Y.fmt ≠ [] →
    (Y.mj Ex O).Fits (Y.hon Ex msg) (fun w => O.cut (msg w)) fun w => O.cut (msg w)

def mjPsc_reads : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (O O' : Y.Own), Y.OwnOK O' → (Y.mj Ex O).Reads O'.Rd

def mjPsc_writes : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (O : Y.Own), (Y.mj Ex O).Writes fun j => ∃ i, j = O.at i

/-- States: under the hypotheses below, at what the honest messages fix, the output rows hold. -/
def mjPsc_out : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (O : Y.Own), Y.VarsOK → Y.DegOK → Y.fmt ≠ [] →
    ∀ (k : Y.J → E) (x : E × Y.St) (ρ : Rho (Y.psc Ex).shape),
      Y.OutHolds ((Y.mj Ex O).nxt x ((Y.mj Ex O).msg k x ρ) ρ) k ∧
      ((Y.mj Ex O).nxt x ((Y.mj Ex O).msg k x ρ) ρ).st = x.2

/-- The conditions of the instance (`PscOur`) pass to larger sets of entries. -/
def mjOur_mono : Prop :=
  ∀ (T : PscOur E) (Rd Rd' : T.J → Prop), (∀ j, Rd j → Rd' j) → T.OwnOur Rd → T.OwnOur Rd'
/-- The instance (`PscOur`) has a variable. -/
def mjOur_ne : Prop := ∀ T : PscOur E, T.par.fmt ≠ []

/-- The step into a sumcheck fits (`mjIn_fits`), and, under `Z.Link`, steps to the sumcheck's claim
(`mjIn_step`). -/
def mjIn_fits : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (W : Type) (rd : W → Z.T.J → E),
    (Z.mj Ex).Fits (Honest.draw Z.ev.D Z.nxX Ex W) rd rd
def mjIn_step : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (O : Z.T.par.Own), Z.Link → (Z.mj Ex).Step (Z.T.par.mj Ex O)

end
end Spec
end
end Cb
