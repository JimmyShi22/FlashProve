-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshVis.lean: under the hypotheses of its statements, after a sending the masks of a
coming block are fresh within the budget `N.budT t`, also for a reading that sees the encoding
randomness and the pads of the other oracle messages of the same prover message.

This file defines conditions (`Own.LawsV`) on a split of those coins of an honest prover that go
into its messages, and states two implications from them to `Honest.Fresh`
(Ior/KnowCollRulesMask.lean), one to them (`Spec.lawsV_of_laws`), and two on a sender that is made
from members' senders (`Spec.ofMem_hid`, `Spec.ofMem_pad`).

Definitions and statements (Cb.Spec.*); the proofs are in Cb/Ld/LdSendFreshVisProofs.lean.

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is the conclusion of
`Spec.ldSendFam_freshV`.

Why: Cb/Ld/LdSendFresh.lean states (proved in Cb/Ld/LdSendFreshProofs.lean), under the hypotheses of
its statements, `Honest.Fresh` of a sending for readings that forget the encoding randomness of
every oracle message of the family sent, and with all pads in one block (`Own.Pd`). That is more
than has to be forgotten: what must stay out of view is the pad and the encoding randomness of the
oracle message o that holds the masks.
It matters: an oracle message with masks may go in one prover message with others that are tested
(folded) long before these masks are used. The prover of such a test reads the encoding randomness
of the messages that it tests; it "does not look at the masks" (`Honest.Blind`,
Ior/KnowCollRulesMask.lean) only for a reading that holds what it reads.

Main names, each under the hypotheses of its statement:
1. In general. vis: any function of the new encoding randomness: the part that may be seen. The
   reading: rd (new messages) (vis (new randomness)) (the further witness handed on).
  `U.LawsV Sd vis bud rd put`, for a split U of the sender's coins (Cb/Ld/LdSendFresh.lean:
    ((own masks × other coins) × Pd)):
    over: to overwrite twice is to overwrite once.
    lay: what is read of the messages sent = own masks laid over a body that reads the witness, the
    other coins and vis: not the own masks, not Pd.
    pad: the weak form: for one witness and one fixing of the other coins, the law of all answers
    over Pd alone does not depend on the own masks. (So Pd may be the pad of o alone: the other
    messages' pads are "other coins", and may be seen.)
    hid: between two messages that differ in own masks and Pd only: a change of the encoding
    randomness that keeps all symbols read within the budget and keeps vis
    (exactly: ∀ T, bud T → ∀ w M M' k₀ η η', ∃ e : D.Nn.Rnd ≃ D.Nn.Rnd, ∀ r,
      (∀ p ∈ T, D.Nn.enc (D.put w (U.mk' M k₀ η)) r p.1 p.2 =
        D.Nn.enc (D.put w (U.mk' M' k₀ η')) (e r) p.1 p.2) ∧ vis (D.upR (e r)) = vis (D.upR r)).
  `Spec.ldSendFam_freshV`: then the sending of a family is Fresh for the own masks, at that budget,
    for that reading. `Spec.ldSendSig_freshV`: the same for the sending to a statement over S.
  `Spec.lawsV_of_laws`: the conditions of Cb/Ld/LdSendFresh.lean with Hides give the case "nothing
    is seen".
2. A sender made from senders of the members, with independent coins (Cb/Ld/LdSendMem.lean:
   `Sig.Sender.ofMem`). o: the member that holds the masks. A split of its coins:
   κo : (mem o).Mk ≃ (Mb × Mo) × Pd.
  `ofMemOwn mem rest w0 o κo`: the split of the family's coins: the other coins are Mo and all coins
    of the other members.
  `visBut o`: the encoding randomness of all members but o.
  `Spec.ofMem_hid`, `Spec.ofMem_pad`: "hid" with vis := visBut o follows from o's own hiding; "pad"
    from the same condition on o's own answers. Nothing is asked of the other members.

Limits: this file says nothing on masks of one block in several oracle messages. It says nothing on
the sending's own zero knowledge (its hypothesis Blind (`Sig.Sender.Blind`, Cb/Ld/LdSendFam.lean) is
not implied by the weak form of "pad").
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFresh
import Cb.Ld.LdSendMem

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type} {D : N.Sender W W'} {Mb : Type}

open Classical in
/-- The conditions, with a part of the new encoding randomness in view. -/
structure Sig.Sender.Own.LawsV (U : D.Own Mb) (Sd : N.Seeds) {Rv Kc : Type}
    (vis : (∀ a, (N.om a).Rnd) → Rv) (bud : Finset (Σ a, (N.om a).C.NP) → Prop)
    (rd : N.Msg → Rv → W' → Kc) (put : Mb → Kc → Kc) : Prop where
  over : ∀ M M' k, put M (put M' k) = put M k
  lay  : ∃ body : W → U.M0 → Rv → Kc,
    ∀ w M k₀ η v, rd (D.upM (D.put w (U.mk' M k₀ η))) v (D.rest w) = put M (body w k₀ v)
  pad  : ∀ s w M M' k₀, (unif U.Pd).map (fun η => D.ans Sd s w (U.mk' M k₀ η)) =
    (unif U.Pd).map fun η => D.ans Sd s w (U.mk' M' k₀ η)
  hid  : ∀ T, bud T →
    ∀ w M M' k₀ η η', ∃ e : D.Nn.Rnd ≃ D.Nn.Rnd, ∀ r,
      (∀ p ∈ T, D.Nn.enc (D.put w (U.mk' M k₀ η)) r p.1 p.2 =
        D.Nn.enc (D.put w (U.mk' M' k₀ η')) (e r) p.1 p.2) ∧
      vis (D.upR (e r)) = vis (D.upR r)

end

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type}

/-- the encoding randomness of all members but o -/
def Sig.visBut (N : Sig E) (o : N.O) (r : ∀ a, (N.om a).Rnd) : ∀ a : {a // a ≠ o}, (N.om a).Rnd :=
  fun a => r a

/-- The split of the family's coins, from a split of the coins of the member o. -/
def Sig.Sender.ofMemOwn (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W') (w0 : W)
    (o : N.O) {Mb Mo Pd : Type} [Fintype Mo] [Nonempty Mo] [Fintype Pd]
    [Nonempty Pd] (κo : (mem o).Mk ≃ (Mb × Mo) × Pd) :
    (Sig.Sender.ofMem mem rest w0).Own Mb where
  M0 := Mo × ∀ a : {a // a ≠ o}, (mem a).Mk
  Pd := Pd
  κ := (Equiv.piSplitAt o fun a => (mem a).Mk).trans
    { toFun := fun x => (((κo x.1).1.1, ((κo x.1).1.2, x.2)), (κo x.1).2)
      invFun := fun y => (κo.symm ((y.1.1, y.1.2.1), y.2), y.1.2.2)
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

end

namespace Spec
open IOR
variable (E : Type) [Field E]

/-- Under the hypotheses below, the sending of a family is fresh, with a part of the new encoding
randomness in view. -/
def ldSendFam_freshV : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec) (D : N.Sender W W')
      (t : N.O → ℕ) (Ri : X → E₀.Str → W → Prop) (Mb : Type) [Fintype Mb] [Nonempty Mb]
      (U : D.Own Mb) (Rv Kc : Type) (vis : (∀ a, (N.om a).Rnd) → Rv)
      (rd : N.Msg → Rv → W' → Kc) (put : Mb → Kc → Kc),
    U.LawsV Sd vis (N.budT t) rd put →
    (ldSendFamHon Sd X E₀ D).Fresh Ri (fun _ T => N.budT t (ldSendFamSet N Sd T))
      (fun v => rd (N.msgs v.1) (vis fun a => (v.1 a).2) v.2) Mb put

/-- The same for the sending to a statement over S. -/
def ldSendSig_freshV : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (St Wp Wp' : Type) (E₀ : ExtSpec)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (t : N.O → ℕ)
      (Ri : St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : D.Own Mb) (Rv Kc : Type) (vis : (∀ a, (N.om a).Rnd) → Rv)
      (rd : N.Msg → Rv → S.Wit × Wp' → Kc) (put : Mb → Kc → Kc),
    U.LawsV Sd vis (N.budT t) rd put →
    (ldSendSigHon Sd St E₀ D).Fresh Ri (ldSendSigNums S N Sd St E₀ Unit (fun _ => 0) t).bud
      (fun v =>
        rd (N.msgs (S.right N (T := OMsg.Wit) v.1))
          (vis fun a => (S.right N (T := OMsg.Wit) v.1 a).2) (S.left N (T := OMsg.Wit) v.1, v.2))
      Mb put

/-- The conditions of Cb/Ld/LdSendFresh.lean, with `D.Nn.Hides (N.budT t)`, give the conditions
here in the case in which nothing of the new randomness is seen. -/
def lawsV_of_laws : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type) (U : D.Own Mb) (Sd : N.Seeds)
      (t : N.O → ℕ) (Kc : Type) (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → D.Nn.Hides (N.budT t) →
    U.LawsV Sd (fun _ => ()) (N.budT t) (fun m _ w' => rd m w') put

/-- A sender from members with independent coins: "hid", from the hiding of the one member that
holds the masks. -/
def ofMem_hid : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W') (w0 : W) (o : N.O)
      (Mb Mo Pd : Type) [Fintype Mo] [Nonempty Mo] [Fintype Pd] [Nonempty Pd]
      (κo : (mem o).Mk ≃ (Mb × Mo) × Pd) (t : N.O → ℕ),
    (mem o).N.Hides ((N.om o).C.budT (t o)) →
    ∀ T, N.budT t T →
      ∀ w M M' k₀ η η',
        ∃ e : (Sig.Sender.ofMem mem rest w0).Nn.Rnd ≃ (Sig.Sender.ofMem mem rest w0).Nn.Rnd, ∀ r,
          (∀ p ∈ T, (Sig.Sender.ofMem mem rest w0).Nn.enc
              ((Sig.Sender.ofMem mem rest w0).put
                w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η))
              r p.1 p.2 =
            (Sig.Sender.ofMem mem rest w0).Nn.enc
              ((Sig.Sender.ofMem mem rest w0).put
                w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M' k₀ η'))
              (e r) p.1 p.2) ∧
          N.visBut o ((Sig.Sender.ofMem mem rest w0).upR (e r)) =
            N.visBut o ((Sig.Sender.ofMem mem rest w0).upR r)

open Classical in
/-- "pad", from the same condition on the answers of that member alone. -/
def ofMem_pad : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W') (w0 : W) (o : N.O)
      (Mb Mo Pd : Type) [Fintype Mo] [Nonempty Mo] [Fintype Pd] [Nonempty Pd]
      (κo : (mem o).Mk ≃ (Mb × Mo) × Pd) (Sd : N.Seeds),
    (∀ ρ w M M' k, (unif Pd).map (fun η => (mem o).ans ρ w (κo.symm ((M, k), η))) =
      (unif Pd).map fun η => (mem o).ans ρ w (κo.symm ((M', k), η))) →
    ∀ s w M M' k₀,
      (unif Pd).map (fun η =>
          (Sig.Sender.ofMem mem rest w0).ans
            Sd s w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η)) =
        (unif Pd).map fun η =>
          (Sig.Sender.ofMem mem rest w0).ans
            Sd s w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M' k₀ η)

end Spec
end Cb
