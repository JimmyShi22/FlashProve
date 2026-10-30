-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2GoodM.lean: under the hypotheses of its statements, the assembled lookup, `LkAsm2`
(Cb/Ld/LdLkpAsm2.lean), is a masked block, as a whole: completeness, knowledge soundness and its
zero-knowledge item "masked messages", in one bundle, in the forms that callers use.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpAsm2GoodMProofs.lean.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean).
Parts: Cb/Ld/LdLkpAsm2Pull*.lean (`GoodB`: `IOR.GoodT` without its clause on zero knowledge; rows
and mask form on the named entries), Cb/Ld/LdLkpMaskAsm2*.lean (the chain has the item),
Cb/Ld/LdLkpMaskLift2.lean (the item carried to these forms). Nothing is assumed about any block
beyond the hypotheses of the statements.

The bundle is `IOR.GoodM` of Ior/Masked.lean: `GoodB` (strings, local, complete, knowledge sound,
the two probabilities); the item `MM`: the lookup sends no oracle and withholds nothing; its plain
parts are a closed form in what is read of witness and explicit part; the claim does not read the
own masks (exactly: the field `stable`); at every verifier randomness, for every reading for which
the claim holds, the law of the plain parts over uniform own masks is the simulator's, exactly; and:
the exact relation gives the claim.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. `H.MM D` asks five things: the block
sends no oracle; `H.withheld w x` is always empty; the honest prover's plain parts are `D.msg` at
`D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and where `D.Cl xp k` holds,
`D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`. In `Spec.ldLkpAsm2M_subN`
and `Spec.ldLkpAsm2M_subIN` `GoodM` stands as the conclusion, and `MM` as a clause of it.

Main names:
  `A.ClaimReads Dt Mu`: the lookup's exact claim (every key in the table; Mu) reads the entries in
    Dt only. Dt: "the data": what the keys read, and the bits.
  The conditions, p being the characteristic of E: on numbers (`LkB.Adm`); `H.MuOn Mu`;
    `A.ClaimReads Dt Mu`; on places: `A.MaskOK Dt` (Cb/Ld/LdLkpMaskAsm2.lean: among them: the own
    masks of all sumchecks lie at pairwise different places, outside the data); ι injective with all
    places in its range; the reading Rd holds the data and the own masks (at entries outside Rd,
    pads say, the reading `mjCut Rd`, Cb/Ld/LdLkpMaskOur.lean, has 0); the further oracles have a
    value.
  `ldLkpAsm2M_subN` and `ldLkpAsm2M_subIN` have all of them; `ldLkpAsm2M_link` all but those on ι;
  `ldLkpAsm2M_dt` only `A.MaskOK Dt`.
  `ldLkpAsm2M_subN`: under the hypotheses of its statement, over a signature:
    `A.subN ι S E₀ Kc Wp msg` is `GoodM`, beside any riding joint, with the `MaskData` `A.dmN`
    (Cb/Ld/LdLkpMaskLift2.lean), which reads of a witness the entries in Rd of the messages, and no
    encoding randomness.
  `ldLkpAsm2M_subIN`: under the hypotheses of its statement, with an encoded index decoded by the
    statement: `A.subIN ι C S msg` is `GoodM`, with the `MaskData` `A.dmIN`
    (Cb/Ld/LdLkpMaskLift2.lean), which reads of a witness the entries in Rd of (the message of the
    prover encoded index, the messages).
  `ldLkpAsm2M_link`: under the hypotheses of its statement, at the base: the messages of `A.baseN ι`
    read the entries in `A.srAll Dt` (data and own masks) only; its own masks lie in `A.swAll`.
  `ldLkpAsm2M_dt`: under `A.MaskOK Dt`, the data holds no own mask.

Limits: this file says nothing on zero knowledge of a chain that holds the lookup: that the masks
are uniform and unseen when the lookup starts is the matter of the block that sends them and of the
blocks between. It does not say that the conditions can be met together: that is the matter of the
guard Cb/Ld/LdLkpToyMaskE.lean (`Spec.ldLkp_toyMaskE`: at one toy lookup; the two conditions on ι:
`Spec.ldLkp_toyE`, Cb/Ld/LdLkpToyE.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskLift2
import Cb.Ld.LdLkpMaskAsm2

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

/-- The lookup's exact claim reads the data only. -/
def LkAsm2.ClaimReads {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)
    (Dt : A.J → Prop) (Mu : A.St → (A.J → E) → Prop) : Prop :=
  ∀ st k k', (∀ j, Dt j → k j = k' j) → A.lk.inP Mu st k → A.lk.inP Mu st k'

end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpAsm2M_dt : Prop :=
  ∀ (A : LkAsm2 E) (Dt : A.J → Prop), A.MaskOK Dt → ∀ j, Dt j → ¬ A.swAll j

def ldLkpAsm2M_link : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E) (Dt Rd : A.J → Prop),
    A.H.lkb.Adm p → A.H.MuOn Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) → A.ClaimReads Dt Mu →
    (A.mjN ι (A.mjChain Ex M Wp Kc msg Rd)).Link (A.baseN ι Ex M Wp Kc msg).H
      (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1)) (A.srAll Dt) A.swAll (A.lk.inP Mu)

/-- Under the hypotheses below, the assembled lookup is a masked block, over a signature. -/
def ldLkpAsm2M_subN : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E) (Dt Rd : A.J → Prop),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) → A.ClaimReads Dt Mu →
    GoodM (A.subN ι S E₀ Kc Wp msg).R (A.subN ι S E₀ Kc Wp msg).H
      (S.over (cj R0 msg id (A.lk.inP Mu) A.lk.inR))
      (S.over (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι))))
      (A.subN ι S E₀ Kc Wp msg).ext (A.subN ι S E₀ Kc Wp msg).P
      (A.dmN ι S (A.mjChain E₀ S.Msg Wp Kc msg Rd) (A.lk.inP Mu) fun w => mjCut Rd (msg w.1))

/-- Under the hypotheses below, the assembled lookup is a masked block, with an encoded index
decoded by the statement. -/
def ldLkpAsm2M_subIN : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (C : ConfigurationWithOutOfDomainSample) [Nonempty C.E0.Str] (S : Sig E)
      (rc : A.St → C.Rec) (R0 : Rels Unit A.St C.E0 ((C.Msg × S.Msg) × Unit))
      (msg : C.Msg × S.Msg → A.J → E) (Dt Rd : A.J → Prop),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) → A.ClaimReads Dt Mu →
    GoodM (A.subIN ι C S msg).R (A.subIN ι C S msg).H
      (S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR)))
      (S.over (idxAt C (fun x => rc x.1)
          (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι)))))
      (A.subIN ι C S msg).ext (A.subIN ι C S msg).P
      (A.dmIN ι C S (A.mjChain C.E0 (C.Msg × S.Msg) Unit Unit msg Rd)
        (A.lk.inP Mu) fun w => mjCut Rd (msg w.1))

end
end Cb.Spec
