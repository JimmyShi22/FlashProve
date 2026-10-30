-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskAsm.lean: the lookup argument (every key is an entry of a table) as one chain of
reductions: under the hypotheses of its statements, the assembled lookup (`LkAsm`,
Cb/Ld/LdLkpAsm.lean; for `LkAsm2`, Cb/Ld/LdLkpAsm2.lean: Cb/Ld/LdLkpMaskAsm2.lean) has the item
"masked messages", as a whole (`Honest.MM`, Ior/Masked.lean).

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the conclusion of
`Spec.ldLkpMaskAsm_mm`; `GoodM` stands in no statement of this file. (In the first two sentences
`D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; below M is a tuple type, and
the statement has `((A.mjChain ..).narrow C).data ..` and `((A.mjBase ..).narrow C).data ..` for
that `D`.)

Definitions and statements (the statements in `Cb.Spec`). Proofs: Cb/Ld/LdLkpMaskAsmProofs.lean.
The lookup sends scalars only. All its masks are entries of oracle messages sent before it.
(Cb/Ld/LdLkpAsm.lean: `A : LkAsm E`; `A.chainA`: first challenge, tie, keys' tree, point of the
forest, forest, closing, bit test; `A.baseA`: with the read-out.)

The conditions on the places of the masks (`A.MaskOK Dt`). Dt: "the data": the entries that the keys
read, and the bits.
  `tie`: the conditions of the tie (Cb/Ld/LdLkpMaskTie.lean: own masks of a step, and of different
    steps, at different places; none in the data; the products read the data only).
  `keyT`: the conditions of the keys' tree (Cb/Ld/LdLkpMaskTree.lean); its incoming form reads masks
    of the tie only. So: no own mask of the keys' tree is a mask of the tie.
  `tab`: the conditions of the table's side (Cb/Ld/LdLkpMaskSegT.lean: forest, closing, bit test);
    its incoming forms read masks of the tie only.
  `kT`: no own mask of the keys' tree is an own mask of the table's side.
In all: the own masks of all sumchecks of the lookup lie at pairwise different places, outside the
data. That none of these entries blinds the answer to a sample comes in through Rd: the chain's
reading (`mjCut Rd`, Cb/Ld/LdLkpMaskOur.lean) forgets such entries if the caller leaves them out of
Rd (no statement here asks it), and Rd must hold data and own masks (Cb/Ld/LdPscZk.lean, Limits). Of
Rd the statements here ask only that it holds `A.srAll Dt`.

In the statements M is any tuple type, msg any reading of the entries, Mu any "the vector is the
multiplicities" with `A.H.MuOK`.

Main names:
  `A.swAll`, `A.srAll Dt`: where the own masks lie; what the messages read: the data and the own
    masks.
  `A.mjChain`: the `MJ` record (Cb/Ld/LdLkpMaskChain.lean) of the whole chain: own masks: those of
    all sumchecks; simulator: the sumchecks' simulators in a row, each at the explicit part that the
    earlier outputs fix (`sim : Xi → Rho R.shape → PMF (Plains R.shape)`; `MJ.seq`:
    `sim := fun x ρ => (D₁.sim x (Rho.fst ρ)).bind fun p₁ =>`
    `(D₂.sim (D₁.nxt x p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)`).
  `Spec.ldLkpMaskAsm_link`: under `A.H.lkb.Adm p` (conditions on numbers, as in Cb/Ld/LdLkpAsm.lean)
    with p the characteristic of E, `A.H.MuOK Mu`, `A.MaskOK Dt`, `A.srAll Dt` inside Rd, and
    `Nonempty Ex.Str`: started with any claim C that gives the lookup's exact claim (every key is in
    the table; the vector is the multiplicities) and reads no own mask, the chain is a link
    (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
  `Spec.ldLkpMaskAsm_mm`: under the same hypotheses, on C too: `Honest.MM` (Ior/Masked.lean) for
    `A.chainA` and for `A.baseA`.

Notation: `Ex`: the further oracles (an `ExtSpec`); `Wp`: the type of the further witness; `Kc`: the
type of the core; `A.St`: the kind of explicit part with which the chain starts
(`chainA : BkA Kc M A.St ..`, Cb/Ld/LdLkpAsm.lean; `BkA`: Cb/Ld/LdLkpTreeP.lean); `A.J`: the finite
type that names the entries; `MJ.narrow`: the same record with the claim `Cl'` in the place of its
own (`{ D with Cl := Cl' }`; Cb/Ld/LdLkpMaskPsc.lean); `MJ.data`: the record of Ior/Masked.lean
(`MaskData`) (Cb/Ld/LdLkpMaskChain.lean).

Limits: the further oracles have at least one value (`Nonempty Ex.Str`): the proof takes the claims
between the parts from the parts' completeness, which is stated "for every value of the oracles".
This file does not say that the masks are uniform and unseen when the lookup starts: the matter of
the block that sends them.
It says nothing on the lift over oracle messages: see Cb/Ld/LdLkpMaskLift2.lean (for `LkAsm2`).
It says nothing on how the conditions (`A.MaskOK Dt`) follow from plain conditions on the thirteen
families of places: see Cb/Ld/LdLkpMaskPlaces.lean, Cb/Ld/LdLkpMaskPlaces2.lean (for `LkAsm2`:
twelve families).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskSegT
import Cb.Ld.LdLkpAsm

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The places of the own masks: of the tie, of the keys' tree, of all. -/
def swTie : A.J → Prop := fun j => ∃ l ≤ A.n, A.H.tie.ownAt l j
def swK : A.J → Prop := fun j => ∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.ownAt l j
def swAll : A.J → Prop := fun j => A.swTie j ∨ A.swK j ∨ A.Q.swT j
/-- What the messages read. -/
def srAll (Dt : A.J → Prop) : A.J → Prop := fun j => Dt j ∨ A.swAll j

/-- The conditions on the places. -/
structure MaskOK (Dt : A.J → Prop) : Prop where
  tie  : A.H.tie.MaskOK A.n Dt
  keyT : (A.IK.setV (A.v' + 1)).DK.MaskOK A.v' Dt A.swTie
  tab  : A.Q.TabOK Dt A.swTie
  kT   : ∀ j, A.swK j → ¬ A.Q.swT j

/-- The `MJ` record of the whole chain. -/
def mjChain (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd : A.J → Prop) :
    MJ E A.J (A.chainA Ex M Wp Kc msg).R :=
  ((A.H.mjHead Ex M Wp Kc msg Rd).seq (mjSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)).seq
    (A.Q.mjSegT Ex Wp Kc msg Rd)

/-- The `MJ` record with the read-out. -/
def mjBase (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd : A.J → Prop) :
    MJ E A.J (A.baseA Ex M Wp Kc msg).R :=
  (A.mjChain Ex M Wp Kc msg Rd).post (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- States: under the hypotheses below, the assembled lookup is a link of a chain of masked blocks.
-/
def ldLkpMaskAsm_link : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E)
      (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop),
    A.H.lkb.Adm p → A.H.MuOK Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) →
    (∀ st k, C st k → A.lk.inP Mu st k) → MjStab C A.swAll →
    (A.mjChain Ex M Wp Kc msg Rd).Link (A.chainA Ex M Wp Kc msg).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (A.srAll Dt) A.swAll C

/-- States: under the hypotheses below, the assembled lookup has the item "masked messages". -/
def ldLkpMaskAsm_mm : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E)
      (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop),
    A.H.lkb.Adm p → A.H.MuOK Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) →
    (∀ st k, C st k → A.lk.inP Mu st k) → MjStab C A.swAll →
    (A.chainA Ex M Wp Kc msg).H.MM
      (((A.mjChain Ex M Wp Kc msg Rd).narrow C).data fun w => mjCut Rd (msg w.1)) ∧
    (A.baseA Ex M Wp Kc msg).H.MM
      (((A.mjBase Ex M Wp Kc msg Rd).narrow C).data fun w => mjCut Rd (msg w.1))

end
end Cb.Spec
