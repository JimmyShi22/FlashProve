-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskAsm2.lean: under the hypotheses of its statements, the assembled lookup, `LkAsm2`,
has the item "masked messages", as a whole.
This file is about the lookup argument (every key is an entry of a table), taken as one chain of
reductions.

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the conclusion of
`Spec.ldLkpMaskAsm2_mm`; `GoodM` stands in no statement of this file. (In the first two sentences
`D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; in this file's statements `M`
is a type, and `Spec.ldLkpMaskAsm2_mm` has `((A.mjChain ..).narrow C).data ..` and
`((A.mjBase ..).narrow C).data ..` for that `D`.)

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskAsm2Proofs.lean.
The statements are those for `LkAsm` (Cb/Ld/LdLkpMaskAsm.lean), word for word, at the data and the
chain of Cb/Ld/LdLkpAsm2.lean (first challenge, tie, the point for the table's products, keys' tree,
forest, the closing where no map is revealed (`A.En.par.core`: `PscPar.core`, Cb/Ld/LdPsc.lean), bit
test), with `H.MuOn` for `H.MuOK`. The lookup sends scalars only; all its masks are entries of
oracle messages sent before it.

The conditions on the places of the masks (`A.MaskOK Dt`). Dt: "the data": the entries that the keys
read, and the bits.
  `tie`: the conditions of the tie (Cb/Ld/LdLkpMaskTie.lean).
  `keyT`: the conditions of the keys' tree (Cb/Ld/LdLkpMaskTree.lean), its incoming form reading
    masks of the tie only.
  `lev`, `inc`: the same for the levels of the table's forest.
  `bits`: the bits are data.
  `injE`, `injB`; `dtE`, `dtB`, `inE`, `inB`, `fE`, `fB`, `eB`; `kT`: the closing's own masks (the
    coefficients of its hiding polynomial alone: there is no inner mask) and the bit test's lie at
    different places, outside the data, the tie's masks, the forest's masks, each other's, the keys'
    tree's.
In all: the own masks of all sumchecks of the lookup lie at pairwise different places, outside the
data.

Main names:
  `A.swAll`, `A.srAll Dt`: where the own masks lie; what the messages read: the data and the own
    masks.
  `A.mjChain .. Rd`: the `MJ` record (Cb/Ld/LdLkpMaskChain.lean) of the whole chain: own masks:
    those of all sumchecks; simulator: the sumchecks' simulators in a row, each at the explicit part
    that the earlier outputs fix (`sim : Xi → Rho R.shape → PMF (Plains R.shape)`; `MJ.seq`:
    `sim := fun x ρ => (D₁.sim x (Rho.fst ρ)).bind fun p₁ =>`
    `(D₂.sim (D₁.nxt x p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)`).
  `Spec.ldLkpMaskAsm2_link`: under `A.H.lkb.Adm p` with p the characteristic of E, `A.H.MuOn Mu`,
    `A.MaskOK Dt`, `A.srAll Dt` inside Rd, and `Nonempty Ex.Str`: started with any claim C that
    gives the lookup's exact claim and reads no own mask, the chain is a link
    (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
  `Spec.ldLkpMaskAsm2_mm`: under the same hypotheses, on C too: `Honest.MM` (Ior/Masked.lean) for
    `A.chainA` and for `A.baseA`.

What the closing means for the item. In `LkAsm` the verifier sees the round polynomial
of a further variable and one more scalar, the value of the bits' extension at the last point,
blinded by an inner mask. Here it sees the sum and the round polynomials alone, blinded by the
hiding polynomial; the simulator of that block is the one of the rounds of the variables
(Cb/Ld/LdPscZk.lean: `maskDataC`).

Notation:
  `Ex`: the further oracles (an `ExtSpec`);
  `M`: the type of the tuples of messages (a witness is in `M × Wp`: `BkA`);
  `msg : M → A.J → E`: the entries of a tuple;
  `Wp`: the type of the further witness;
  `Kc`: the type of the core;
  `A.St`: the kind of explicit part with which the chain starts (`chainA : BkA Kc M A.St ..`,
    Cb/Ld/LdLkpAsm2.lean; `BkA`: Cb/Ld/LdLkpTreeP.lean);
  `A.J`: the finite type that names the entries;
  `MJ.narrow`: the same record with the claim `Cl'` in the place of its own (`{ D with Cl := Cl' }`;
    Cb/Ld/LdLkpMaskPsc.lean);
  `MJ.data`: the record of Ior/Masked.lean (`MaskData`) (Cb/Ld/LdLkpMaskChain.lean).

Limits: the further oracles have at least one value (`Nonempty Ex.Str`): the proof takes the claims
after the head and after the keys' side from the parts' completeness.
This file does not say that the masks are uniform and unseen when the lookup starts.
It says nothing on the lift over oracle messages: see Cb/Ld/LdLkpMaskLift2.lean,
Cb/Ld/LdLkpAsm2GoodM.lean.
It says nothing on the conditions from four plain conditions on the eleven families of own masks'
places, and the number of own masks: see Cb/Ld/LdLkpMaskPlaces2.lean.
It does not say that the conditions can be met together: the guard Cb/Ld/LdLkpToyMask.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskSegT
import Cb.Ld.LdLkpMaskCore
import Cb.Ld.LdLkpAsm2

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- The places of the own masks: of the tie, of the keys' tree, of the forest's levels, of the
closing, of the bit test, of the table's side, of all. -/
def swTie : A.J → Prop := fun j => ∃ l ≤ A.n, A.H.tie.ownAt l j
def swK : A.J → Prop := fun j => ∃ l ≤ A.v', (A.IK.setV (A.v' + 1)).DK.ownAt l j
def ownF : A.J → Prop := fun j => ∃ l < A.d, A.D.ownAt l j
def ownE : A.J → Prop := fun j => ∃ i, j = A.wE i
def ownB : A.J → Prop := fun j => ∃ i, j = Sum.elim A.wB (fun _ : Unit => A.cB) i
def swT : A.J → Prop := fun j => A.ownF j ∨ A.ownE j ∨ A.ownB j
def swAll : A.J → Prop := fun j => A.swTie j ∨ A.swK j ∨ A.swT j
/-- What the messages read. -/
def srAll (Dt : A.J → Prop) : A.J → Prop := fun j => Dt j ∨ A.swAll j

/-- The conditions on the places. -/
structure MaskOK (Dt : A.J → Prop) : Prop where
  tie  : A.H.tie.MaskOK A.n Dt
  keyT : (A.IK.setV (A.v' + 1)).DK.MaskOK A.v' Dt A.swTie
  lev  : ∀ l < A.d, A.D.MaskOK l Dt A.swTie
  inc  : ∀ st ϱ j, ¬ A.swTie j → A.D.inc0 st ϱ j = 0
  bits : ∀ u j, Dt (A.bAt u j)
  injE : Function.Injective A.wE
  injB : Function.Injective (Sum.elim A.wB fun _ : Unit => A.cB)
  dtE  : ∀ j, Dt j → ¬ A.ownE j
  dtB  : ∀ j, Dt j → ¬ A.ownB j
  inE  : ∀ j, A.swTie j → ¬ A.ownE j
  inB  : ∀ j, A.swTie j → ¬ A.ownB j
  fE   : ∀ j, A.ownF j → ¬ A.ownE j
  fB   : ∀ j, A.ownF j → ¬ A.ownB j
  eB   : ∀ j, A.ownE j → ¬ A.ownB j
  kT   : ∀ j, A.swK j → ¬ A.swT j

section
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd : A.J → Prop)

/-- The `MJ` record of the keys' side with the step into the forest, and of the levels below l. -/
def mjForest : (l : ℕ) → MJ E A.J (A.forest Ex M Wp Kc msg l).R
  | 0 =>
    (mjSegK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Rd).post
      (fun x => some (A.enterT x)) (ExtMap.id Ex) A.enterT
  | l + 1 => (mjForest l).seq (A.D.mjLev Ex Rd l)

/-- The `MJ` record of the whole chain. -/
def mjChain : MJ E A.J (A.chainA Ex M Wp Kc msg).R :=
  ((((A.H.mjHead Ex M Wp Kc msg Rd).seq (A.R.toIn.mj Ex)).seq
        (A.mjForest Ex M Wp Kc msg Rd A.d)).seq
      (A.En.par.mjC Ex Rd)).seq
    ((A.Bt.zc.toIn.mj Ex).seq (A.Bt.zc.next.mjJ Ex (Equiv.refl _) Rd))

/-- The `MJ` record with the read-out. -/
def mjBase : MJ E A.J (A.baseA Ex M Wp Kc msg).R :=
  (A.mjChain Ex M Wp Kc msg Rd).post (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd

end
end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- States: under the hypotheses below, the assembled lookup is a link of a chain of masked blocks.
-/
def ldLkpMaskAsm2_link : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E)
      (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop),
    A.H.lkb.Adm p → A.H.MuOn Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) →
    (∀ st k, C st k → A.lk.inP Mu st k) → MjStab C A.swAll →
    (A.mjChain Ex M Wp Kc msg Rd).Link (A.chainA Ex M Wp Kc msg).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (A.srAll Dt) A.swAll C

/-- States: under the hypotheses below, the assembled lookup has the item "masked messages". -/
def ldLkpMaskAsm2_mm : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E)
      (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop),
    A.H.lkb.Adm p → A.H.MuOn Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) →
    (∀ st k, C st k → A.lk.inP Mu st k) → MjStab C A.swAll →
    (A.chainA Ex M Wp Kc msg).H.MM
      (((A.mjChain Ex M Wp Kc msg Rd).narrow C).data fun w => mjCut Rd (msg w.1)) ∧
    (A.baseA Ex M Wp Kc msg).H.MM
      (((A.mjBase Ex M Wp Kc msg Rd).narrow C).data fun w => mjCut Rd (msg w.1))

end
end Cb.Spec
