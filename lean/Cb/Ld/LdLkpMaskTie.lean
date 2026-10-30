-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskTie.lean: under the hypotheses of its statements, the tie of a lookup has the item
"masked messages", as a whole (`Honest.MM`, Ior/Masked.lean).
This file is about one part of the lookup argument: the chain of sumchecks that ties the product
over the keys to the products over the table. Here PK, PT and Q are any functions of the state and
the entries (`TieP`); that they are a lookup's products is the caller's matter (Cb/Ld/LdLkpTie.lean,
Limits).

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the conclusion of
`Spec.ldLkpMaskTie_mm`; `GoodM` stands in no statement of this file. (In the first two sentences
`D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; below `D : TieP E`, and the
statement has `((D.mjTie ..).narrow (D.claim 0)).data ..` for that `D`.)

Definitions (with one proved lemma, `toJ_bij`), and statements (in `Cb.Spec`). Proofs:
Cb/Ld/LdLkpMaskTieProofs.lean.
The tie (Cb/Ld/LdLkpTie.lean: `D : TieP E`, `D.tieA`) is a chain of n + 1 sumchecks without
variable on values that are never sent. It sends no oracle; all its masks are entries of oracle
messages sent before.

The conditions on the places of the masks (`D.MaskOK n Dt`), all on the parameters:
  `inj`: within a step, different own masks lie at different places.
  `disj`: the own masks of different steps lie at different places.
  `rd`: the virtual scalars PK, PT, Q read the entries in Dt only ("the data").
  `dt`: no own mask of a step lies in the data.
That no own mask and no datum is an entry that blinds the answer to a sample cannot be said at this
level; it comes in through Rd: the chain's reading forgets those entries (that Rd leaves them out is
the caller's to show: of Rd the statements here ask only that it holds `D.srAt Dt n`), and Rd must
hold the data and the own masks (Cb/Ld/LdPscZk.lean, Limits).
(`D.ownAt l`: the places of the own masks of step l: the coefficients of its hiding polynomial and
its two inner masks.)

In `Spec.ldLkpMaskTie_link` and `Spec.ldLkpMaskTie_mm` M is any tuple type, msg any reading of the
entries; `Spec.ldLkpMaskTie_sound` is stated at the tuple type `M` = D.J → E, read by the identity
(`msg`).
Rd: the entries that the reading of the chain in which the tie stands keeps (all others are
forgotten); it must hold the data and the tie's own masks.

Main names:
  `D.mjTie`: the `MJ` record of the whole tie (Cb/Ld/LdLkpMaskChain.lean): own masks: those of all
    steps; simulator: the steps' simulators in a row, each at the explicit part that the earlier
    outputs fix (`sim : Xi → Rho R.shape → PMF (Plains R.shape)`; `MJ.seq`:
    `sim := fun x ρ => (D₁.sim x (Rho.fst ρ)).bind fun p₁ =>`
    `(D₂.sim (D₁.nxt x p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)`).
  `Spec.ldLkpMaskTie_link`: under `D.StepTo n`, `D.MaskOK n Dt`, and `D.srAt Dt n` inside Rd:
    started with any claim C that gives the tie's first claim (PK - Q_0 = target) and reads no own
    mask of the tie, the tie is a link of a chain (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean): it has the
    item; its messages read data and own masks only; its own masks lie at their places.
  `Spec.ldLkpMaskTie_mm`: so, under the same three premises: `Honest.MM` of Ior/Masked.lean for the
    whole tie, started with the tie's first claim.
  `Spec.ldLkpMaskTie_sound`: under the hypotheses of its statement: if C gives the joint before the
    tie (`mjClOf (D.jtAt .. 0)`), then what the honest run of the tie makes of C
    (`(D.mjTie ..).sp C`; `MJ.sp`: Cb/Ld/LdLkpMaskSp.lean) gives the joint after the tie (all masked
    claims that the tie leaves) (`mjClOf (D.jtAt .. (n + 1))`; `mjClOf`: Cb/Ld/LdLkpMaskKit.lean).

Notation: `Ex`: the external oracles (an `ExtSpec`, Iop/InteractiveOracleProof.lean); `Wp`: the type of the further
witness; `Kc`: the type of the core; `D.J`: the finite type that names the entries; `A0`: a joint
(`Rels Kc ..`), an argument of `D.jtAt`; `mjClOf A`: the claim on entries that a joint at the base
makes (Cb/Ld/LdLkpMaskKit.lean); `MJ.narrow`: the same record with the claim `Cl'` in the place of
its own (`{ D with Cl := Cl' }`; Cb/Ld/LdLkpMaskPsc.lean); `MJ.data`: the record of Ior/Masked.lean
(`MaskData`) (Cb/Ld/LdLkpMaskChain.lean).

Limits: this file does not say that the masks are uniform and unseen when the tie starts.
It says nothing on soundness: see Cb/Ld/LdLkpTie.lean. (`Spec.ldLkpMaskTie_sound` speaks of the
honest run.)

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskOur
import Cb.Ld.LdLkpTie

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

namespace TieP
variable {E : Type} [Field E] [Fintype E] (D : TieP E)

theorem toJ_bij : ∀ l, Function.Bijective (D.lv l).toJ
  | 0 => Function.bijective_id
  | _ + 1 => Function.bijective_id

/-- The entries of step l are the tie's entries. -/
def eJ (l : ℕ) : (D.lv l).T.J ≃ D.J := Equiv.ofBijective _ (D.toJ_bij l)

/-- The places of the own masks of step l. -/
def ownAt (l : ℕ) : D.J → Prop := fun j =>
  ∃ i, j = D.eJ l (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt i)

/-- The conditions on the places. -/
structure MaskOK (n : ℕ) (Dt : D.J → Prop) : Prop where
  inj  : ∀ l ≤ n, Function.Injective (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt)
  disj : ∀ l l', l < l' → l' ≤ n → ∀ j, D.ownAt l j → ¬ D.ownAt l' j
  rd   : ∀ st m m', (∀ j, Dt j → m j = m' j) →
    D.PK st m = D.PK st m' ∧ D.PT st m = D.PT st m' ∧ D.Q st m = D.Q st m'
  dt   : ∀ l ≤ n, ∀ j, Dt j → ¬ D.ownAt l j

/-- What the messages of step l read: the data, the own masks of the steps up to l. -/
def srAt (Dt : D.J → Prop) (l : ℕ) : D.J → Prop := fun j => Dt j ∨ ∃ l' ≤ l, D.ownAt l' j

/-- The `MJ` record of step l, with the step without rounds after it. -/
def mjAt (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ) :
    MJ E D.J (((D.lv l).T.par.psc Ex).post (fun o => some (D.nxt l o)) (ExtMap.id Ex)) :=
  ((D.lv l).T.mjJ Ex (D.eJ l) Rd).post (fun o => some (D.nxt l o)) (ExtMap.id Ex) (D.nxt l)

/-- The `MJ` record of the whole tie. -/
def mjTie (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (Rd : D.J → Prop) (n : ℕ) :
    MJ E D.J (D.tieA Ex Wp Kc msg n).R :=
  MJ.chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) (fun l => D.mjAt Ex Rd l) n

end TieP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The places, written out. -/
def ldLkpMaskTie_own : Prop :=
  ∀ (D : TieP E) (j : D.J),
    (D.ownAt 0 j ↔ (∃ i, j = D.wS i) ∨ ∃ b, j = D.cS b) ∧
    ∀ l, D.ownAt (l + 1) j ↔ (∃ i, j = D.wAt l i) ∨ ∃ b, j = D.cAt l b

/-- States: under the hypotheses below, the tie is a link of a chain of masked blocks. -/
def ldLkpMaskTie_link : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) (Dt Rd : D.J → Prop)
      (C : E × (D.lv 0).T.St → (D.J → E) → Prop),
    D.StepTo n → D.MaskOK n Dt → (∀ j, D.srAt Dt n j → Rd j) →
    (∀ x k, C x k → D.claim 0 x k) → (∀ l ≤ n, MjStab C (D.ownAt l)) →
    (D.mjTie Ex M Wp Kc msg Rd n).Link (D.tieA Ex Wp Kc msg n).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (fun j => ∃ l ≤ n, D.srAt Dt l j)
      (fun j => ∃ l ≤ n, D.ownAt l j) C

/-- States: under the hypotheses below, the tie has the item "masked messages". -/
def ldLkpMaskTie_mm : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) (Dt Rd : D.J → Prop),
    D.StepTo n → D.MaskOK n Dt → (∀ j, D.srAt Dt n j → Rd j) →
    (D.tieA Ex Wp Kc msg n).H.MM
      (((D.mjTie Ex M Wp Kc msg Rd n).narrow (D.claim 0)).data fun w => mjCut Rd (msg w.1))

/-- States: under the hypotheses below, what the honest run of the tie makes of a claim gives the
joint after the tie. -/
def ldLkpMaskTie_sound : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (Kc : Type) (A0 : Rels Kc D.St0 Ex ((D.J → E) × Unit)) (n : ℕ)
      (Dt Rd : D.J → Prop) (C : E × (D.lv 0).T.St → (D.J → E) → Prop),
    D.StepTo n → D.MaskOK n Dt → (∀ j, D.srAt Dt n j → Rd j) → (∀ x k, C x k → D.claim 0 x k) →
    (∀ x k, C x k → mjClOf (D.jtAt (fun m => m) A0 0) x k) → (∀ l ≤ n, MjStab C (D.ownAt l)) →
    ∀ x' k, (D.mjTie Ex (D.J → E) Unit Kc (fun m => m) Rd n).sp C x' k →
      mjClOf (D.jtAt (fun m => m) A0 (n + 1)) x' k

end
end Cb.Spec
