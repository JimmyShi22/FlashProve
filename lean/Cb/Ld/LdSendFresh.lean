-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFresh.lean: under the hypotheses of its statements, after a sending, the masks of a
coming block are still uniform, given all that the sending shows, in this sense:
`(ldSendFamHon ..).Fresh Ri (fun _ T => N.budT t ..) .. Mb put` (`Spec.ldSendFam_fresh`;
`Honest.Fresh`: Ior/KnowCollRulesMask.lean); and so "a sending, then a masked block" is
honest-verifier zero knowledge.

Definitions and statements (Cb.Spec.*); the proofs are in Cb/Ld/LdSendFreshProofs.lean.

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is the conclusion of
`Spec.ldSendFam_fresh`.
`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. Here it is
a premise of `Spec.ldSendFam_fresh` (`D.Nn.Hides (N.budT t)`: the encoding is `D.Nn`, N the family;
`Sig.budT`: Cb/Ld/LdSendFam.lean).
What `GoodT` bundles: the head of Cb/Ld/LdSend.lean.

Why: a block may hide what it sends in the clear by mask entries that stand in an oracle message
sent earlier (Ior/Masked.lean: the item "masked messages"). The rule for chains with such blocks
(Ior/KnowCollRulesMask.lean: `goodT_seq_masked`) asks of the rounds before the block the property
`Honest.Fresh`: given all that these rounds show, the block's own masks are uniform and independent
of the rest of what the block reads. The sending (Cb/Ld/LdSendFam.lean, Cb/Ld/LdSigSum.lean) shows
two things that depend on the masks: symbols of the words, and the answers to the samples. Here:
under the hypotheses below, it is Fresh all the same.

The coins of the sender that go into the messages are split (`Sender.Own Mb`, data): ((own masks of
the coming block, Mb) × (all other such coins, M0: other blocks' masks, free room)) × (the pads,
Pd). M0 and Pd are finite and not empty.
`U.Laws Sd rd put`, the conditions. rd: what the coming block reads of (messages sent, further
witness); put M k: k with the own masks overwritten.
  over: to overwrite twice is to overwrite once.
  lay: what the block reads of the messages sent is put (own masks) (a body), and the body reads the
  witness and the other coins: not the own masks, not the pads. (So no own mask is a pad, and the
  block reads no pad.)
  pad: at every joint seed the law of all answers, over the pads alone, is the same for every
  witness and every fixing of all else. (Uniform answers are a case: `Spec.own_pad_of_uniform`. This
  is what a pad under the sample gives: an entry that is used for nothing else, with a factor that
  is not 0.)
With "the encoding hides `t a` long positions of each member a" these give all
(`Spec.ldSendFam_fresh`, `Spec.ldSendSig_fresh`). In the sending, encoding randomness is read by
nothing but the words; it stands in the witness handed on, and the reading forgets the encoding
randomness of the whole family (rd : N.Msg → W' → Kc).

Main names, each under the hypotheses of its statement:
  `Spec.own_blind`: the conditions give the hypothesis "Blind" of the sending's own zero knowledge.
  `Spec.ldSendFam_fresh`: the sending of a family, from any joint, is Fresh for the own masks, at
    the budget of its own zero knowledge.
  `Spec.ldSendSig_fresh`: the same for the sending to a statement that has oracle messages already.
  `Spec.sigChain_send_masked`: a sending, then a masked block on claims about all messages
    (`GoodAt`, the item, "the relation gives the claim"): the bundle `GoodT`, with exact
    honest-verifier zero knowledge. Errors in a row; no new error; the budget is the composed one
    (`Nums.seq`, Ior/Chain.lean) of the sending's and `P`'s.
  `Spec.send_psc_goodT`: the case of the sumcheck for a polynomial summand (Cb/Ld/LdPsc.lean),
    abstract inner masks; `Spec.send_psc_our_goodT`: the instance with the dummy last variable.

Limits: this file says nothing on masks of several coming blocks: each block has its own split (its
masks are "other coins" for the others), and between the sending and a block every link must not
look at that block's masks (`Honest.Blind`; for the sumcheck: Cb/Ld/LdPscGood.lean,
`psc_blind_sig`). A proximity test on a word before the block that uses its masks is excluded by the
rule itself. This file says nothing on statistical errors of encodings: all are 0 here.
The lemma behind this file follows this protocol's technical report (lean/CREDITS.md), which follows
the paper that this protocol builds on.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigChain
import Cb.Ld.LdPscGood
import Ior.KnowCollRulesMask

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type}

/-- The coins that go into the messages, split: own masks of the coming block, other coins, pads.
Data. -/
structure Sig.Sender.Own (D : N.Sender W W') (Mb : Type) where
  M0 : Type
  [finM0 : Fintype M0]
  [neM0 : Nonempty M0]
  Pd : Type
  [finPd : Fintype Pd]
  [nePd : Nonempty Pd]
  κ : D.Mk ≃ (Mb × M0) × Pd

attribute [instance] Sig.Sender.Own.finM0 Sig.Sender.Own.neM0
  Sig.Sender.Own.finPd Sig.Sender.Own.nePd

variable {D : N.Sender W W'} {Mb : Type}

/-- the coins, from their parts -/
def Sig.Sender.Own.mk' (U : D.Own Mb) (M : Mb) (k₀ : U.M0) (η : U.Pd) : D.Mk :=
  U.κ.symm ((M, k₀), η)

open Classical in
/-- The conditions. -/
structure Sig.Sender.Own.Laws
    (U : D.Own Mb) (Sd : N.Seeds) {Kc : Type} (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc) :
    Prop where
  over : ∀ M M' k, put M (put M' k) = put M k
  lay  : ∃ body : W → U.M0 → Kc,
    ∀ w M k₀ η, rd (D.upM (D.put w (U.mk' M k₀ η))) (D.rest w) = put M (body w k₀)
  pad  : ∀ s w w' M M' k₀ k₀', (unif U.Pd).map (fun η => D.ans Sd s w (U.mk' M k₀ η)) =
    (unif U.Pd).map fun η => D.ans Sd s w' (U.mk' M' k₀' η)

end

namespace Spec
open IOR

section
variable (E : Type) [Field E]

open Classical in
/-- Uniform answers over the pads, for every fixing of all else, are a case of "pad". -/
def own_pad_of_uniform [Fintype E] : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type) (U : D.Own Mb) (Sd : N.Seeds),
    (∀ s w M k₀, (unif U.Pd).map (fun η => D.ans Sd s w (U.mk' M k₀ η)) = unif N.Answ) →
    ∀ s w w' M M' k₀ k₀', (unif U.Pd).map (fun η => D.ans Sd s w (U.mk' M k₀ η)) =
      (unif U.Pd).map fun η => D.ans Sd s w' (U.mk' M' k₀' η)

/-- The conditions give the hypothesis "Blind" of the sending's own zero knowledge. -/
def own_blind : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type) [Fintype Mb] [Nonempty Mb]
      (U : D.Own Mb) (Sd : N.Seeds) (Kc : Type) (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → D.Blind Sd

/-- Under the hypotheses below, the sending of a family is fresh for the own masks of a coming
block, within the budget `N.budT t`. -/
def ldSendFam_fresh : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec) (D : N.Sender W W') (t : N.O → ℕ)
      (Ri : X → E₀.Str → W → Prop) (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : D.Own Mb) (Kc : Type)
      (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → D.Nn.Hides (N.budT t) →
    (ldSendFamHon Sd X E₀ D).Fresh
      Ri (fun _ T => N.budT t (ldSendFamSet N Sd T)) (fun v => rd (N.msgs v.1) v.2) Mb put

/-- The same for the sending to a statement over S. rd reads all messages, old and new, and the
further witness. -/
def ldSendSig_fresh : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (St Wp Wp' : Type) (E₀ : ExtSpec)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (t : N.O → ℕ)
      (Ri : St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : D.Own Mb) (Kc : Type) (rd : (S.sum N).Msg × Wp' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd (fun m w' => rd (S.join N (T := OMsg.Msg) (S.msgs w'.1) m, w'.2)) put →
    D.Nn.Hides (N.budT t) →
    (ldSendSigHon Sd St E₀ D).Fresh Ri (ldSendSigNums S N Sd St E₀ Unit (fun _ => 0) t).bud
      (fun v => rd ((S.sum N).msgs v.1, v.2)) Mb put

/-- A sending, then a masked block on claims about all messages: honest-verifier zero knowledge, and
all the rest. (not all hypotheses are named here: see the statement below) -/
def sigChain_send_masked : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (Kc St St' Wp Wp' Wp'' : Type) (E₀ E₀' : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ) (R : IOR St E₀ St' E₀')
      (H : R.Honest ((S.sum N).Msg × Wp') ((S.sum N).Msg × Wp''))
      (B : Rels Kc St' E₀' ((S.sum N).Msg × Wp''))
      (ext : (S.sum N).Msg → St × E₀.Str → Tr R.shape → Wp'' → Wp') (P : Nums Kc R) (d : S.Wit × Wp)
      (Dm : MaskData R ((S.sum N).Msg × Wp')) (U : D.Own Dm.Mk),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Nn.Hides (N.budT t) →
    U.Laws Sd (fun m w' => Dm.kc (S.join N (T := OMsg.Msg) (S.msgs w'.1) m, w'.2)) Dm.put →
    GoodAt R H (S.grow N A bk) B ext P → H.MM Dm →
    (∀ x y w, (S.grow N A bk).rel x y w → Dm.Cl (Dm.pub x) (Dm.kc w)) →
    GoodT ((ldSendSig S N Sd St E₀).seq (R.keep (S.sum N).Smp (S.sum N).ext))
      ((ldSendSigHon Sd St E₀ D).seq ((S.sum N).liftH H)) (S.over A).cf ((S.sum N).over B).cf
      (IOR.extSeq _ _
        (fun _ _ w =>
          (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
        (fun a τ w => (w.1, ext ((S.sum N).msgs w.1) (a.1.1, a.2.1) τ w.2)) d)
      ((ldSendSigNums S N Sd St E₀ Kc L t).seq (P.keep (S.sum N).Smp (S.sum N).ext))

end

section
variable (E : Type) [Field E] [Fintype E]

/-- A sending, then the sumcheck for a polynomial summand whose masks were sent in it. Before the
sending the sum claim is on entries read (msg₀) off the old messages and the further witness, a part
of which is about to be sent; after it, on entries read (msg) off all messages. Asked: the two
readings give the same claim. (not all hypotheses are named here: see the statement below) A0 rides
along. -/
def send_psc_goodT : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (Y : PscPar E) (Kc Wp Wp' : Type) (E₀ : ExtSpec)
      (A0 : Rels Kc Y.St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp) (msg₀ : S.Msg × Wp → Y.J → E)
      (msg : (S.sum N).Msg → Y.J → E) (O : Y.Own) (D : N.Sender (S.Wit × Wp) (S.Wit × Wp'))
      (L t : N.O → ℕ) (d : S.Wit × Wp) (U : D.Own O.Mk),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Nn.Hides (N.budT t) → Y.VarsOK → Y.DegOK → Y.ValInj → Y.OwnOK O →
    U.Laws Sd (fun m w' => O.cut (msg (S.join N (T := OMsg.Msg) (S.msgs w'.1) m))) O.put →
    (∀ x (m : (S.sum N).Msg) wp',
      Y.SumHolds x (msg₀ (S.left N (T := OMsg.Msg) m, bk (S.right N (T := OMsg.Msg) m) wp')) ↔
      Y.SumHolds x (msg m)) →
    GoodT ((ldSendSig S N Sd (E × Y.St) E₀).seq ((Y.psc E₀).keep (S.sum N).Smp (S.sum N).ext))
      ((ldSendSigHon Sd (E × Y.St) E₀ D).seq ((S.sum N).liftH (Y.hon E₀ fun w => msg w.1)))
      (S.over (Y.baseIn A0 msg₀)).cf
      ((S.sum N).over (Y.baseOut (S.grow N A0 bk) fun w => msg w.1)).cf
      (IOR.extSeq _ _
        (fun _ _ w =>
          (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
        (fun _ _ w => w) d)
      ((ldSendSigNums S N Sd (E × Y.St) E₀ Kc L t).seq
        ((Y.nums E₀ Kc).keep (S.sum N).Smp (S.sum N).ext))

/-- The instance with the dummy last variable. -/
def send_psc_our_goodT : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (T : PscOur E) (Kc Wp Wp' : Type) (E₀ : ExtSpec)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp) (msg₀ : S.Msg × Wp → T.J → E)
      (msg : (S.sum N).Msg → T.J → E) (Rd : T.J → Prop) (D : N.Sender (S.Wit × Wp) (S.Wit × Wp'))
      (L t : N.O → ℕ) (d : S.Wit × Wp) (U : D.Own (T.own Rd).Mk),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) →
    (∀ a, (N.om a).Evades) → D.Laws (S.backN N bk) → D.Nn.Hides (N.budT t) → T.VarsOK →
    T.DegX → T.DegY → T.ValInj → T.OwnOur Rd →
    U.Laws Sd (fun m w' => (T.own Rd).cut (msg (S.join N (T := OMsg.Msg) (S.msgs w'.1) m)))
      (T.own Rd).put →
    (∀ x (m : (S.sum N).Msg) wp',
      T.SumHolds x (msg₀ (S.left N (T := OMsg.Msg) m, bk (S.right N (T := OMsg.Msg) m) wp')) ↔
      T.SumHolds x (msg m)) →
    GoodT ((ldSendSig S N Sd (E × T.St) E₀).seq ((T.par.psc E₀).keep (S.sum N).Smp (S.sum N).ext))
      ((ldSendSigHon Sd (E × T.St) E₀ D).seq ((S.sum N).liftH (T.par.hon E₀ fun w => msg w.1)))
      (S.over (T.par.baseIn A0 msg₀)).cf
      ((S.sum N).over (T.par.baseOut (S.grow N A0 bk) fun w => msg w.1)).cf
      (IOR.extSeq _ _
        (fun _ _ w =>
          (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
        (fun _ _ w => w) d)
      ((ldSendSigNums S N Sd (E × T.St) E₀ Kc L t).seq
        ((T.par.nums E₀ Kc).keep (S.sum N).Smp (S.sum N).ext))

end
end Spec
end Cb
