-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegSendFresh.lean: under the hypotheses of its statement, a sending of a preamble is fresh
for the masks that it sends, in the form of the wide fact; meant: only the holder's pad and encoding
randomness are forgotten.

Definitions and statements (Cb.Spec.segSend_*); the proofs are in
Cb/Req1/LdSegSendFreshProofs.lean.
It builds on Cb/Req1/LdSegKit.lean, Cb/Req1/LdSegCarry.lean (`segCarry_send_new` takes "the
sending's honest side is Fresh" as a hypothesis) and
Cb/Ld/LdSendFreshVis.lean (Fresh at the sender for a reading that sees a part of the new encoding
randomness).
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) In `Spec.segSend_fresh` it is the conclusion (of `d.link.H`).

What is stated: d (`d : LdSendD a`, Cb/Req1/LdSegKit.lean) sends the family d.N to a statement over
a.S. A coming masked block has its own masks at entries "own" of the new messages. After the sending
the wide fact (`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean) holds:
  Read: of the old messages the entries in RdOld, of the old encoding randomness that at the names
    in RrOld: both arbitrary; of the new messages the entries in RdNew, of the new encoding
    randomness that at the names in RrNew; the whole further witness.
  Own: the entries "own" of the new messages, with the values val M (M in Mb, a finite non-empty
    type).
  Meant: RdNew = all entries but the pad of the oracle message o that holds the masks; RrNew = all
    names of the new family but o. So a later test on a companion of o, whose prover reads that
    companion's encoding randomness, still carries the fact, under the hypotheses of `segWide_fold`
    (Cb/Req1/LdSegCarry.lean).
Asked, of a split U of the sender's coins (Cb/Ld/LdSendFresh.lean:
((own masks × other coins) × Pd)):
  sub: the own entries are read (own ⊆ RdNew).
  own: the entry at an own place is the mask's value there.
  off: an entry in RdNew that is not own reads neither the own masks nor Pd.
  pad: for one witness and one fixing of the other coins, the law of all answers over Pd alone does
    not depend on the own masks.
  hid: between two messages that differ in own masks and Pd only: a change of the encoding
    randomness that keeps all symbols read within the budget, and keeps the randomness at the names
    in RrNew.

Main names:
  `N.visAt Rr`: the encoding randomness at the names in Rr (nothing at the others).
  `Spec.segSend_fresh`, `Spec.segSend_after` are under the five conditions sub, own, off, pad, hid.
  `Spec.segSend_fresh`: d.link.H.Fresh .. for the wide fact: the hypothesis of
    Cb/Req1/LdSegCarry.lean's `segCarry_send_new`.
  `Spec.segSend_after`: so the wide fact is among the facts that are fresh after the move
    (Cb/Req1/LdReq.lean: `(LdMv.send a d).After base`), whatever was fresh before.
  `Spec.segSend_hid_but`: "hid" from the form of Cb/Ld/LdSendFreshVis.lean ("keeps the randomness of
    all members but o": for a sender made from members with independent coins that follows from o's
    own hiding: `ofMem_hid`), if RrNew does not name o.

Limits: this file says nothing on masks of one block in several oracle messages, and nothing on the
sending's own zero knowledge.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry
import Cb.Ld.LdSendFreshVis
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

open Classical in
/-- the encoding randomness at the names in Rr -/
def Sig.visAt {E : Type} (N : Sig E) (Rr : N.O → Prop) (r : ∀ a, (N.om a).Rnd) :
    ∀ o, Option (N.om o).Rnd :=
  fun o => if Rr o then some (r o) else none

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

open Classical in
/-- Under the hypotheses below, the sending is fresh for the wide fact. -/
def segSend_fresh : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : d.D.Own Mb)
      (RdOld : a.S.Ent → Prop) (RdNew : d.N.Ent → Prop) (RrOld : a.S.O → Prop)
      (RrNew : d.N.O → Prop) (own : d.N.Ent → Prop) (val : Mb → d.N.Ent → E),
    (∀ n, own n → RdNew n) →
    (∀ w M k₀ η (n : d.N.Ent), own n → d.D.upM (d.D.put w (U.mk' M k₀ η)) n.1 n.2 = val M n) →
    (∀ w M M' k₀ η η' (n : d.N.Ent), RdNew n → ¬ own n →
      d.D.upM (d.D.put w (U.mk' M k₀ η)) n.1 n.2 = d.D.upM (d.D.put w (U.mk' M' k₀ η')) n.1 n.2) →
    (∀ s w M M' k₀, (unif U.Pd).map (fun η => d.D.ans d.Sd s w (U.mk' M k₀ η)) =
      (unif U.Pd).map fun η => d.D.ans d.Sd s w (U.mk' M' k₀ η)) →
    (∀ T, d.N.budT d.t T →
      ∀ w M M' k₀ η η', ∃ e : d.D.Nn.Rnd ≃ d.D.Nn.Rnd, ∀ r,
        (∀ p ∈ T, d.D.Nn.enc (d.D.put w (U.mk' M k₀ η)) r p.1 p.2 =
          d.D.Nn.enc (d.D.put w (U.mk' M' k₀ η')) (e r) p.1 p.2) ∧
        d.N.visAt RrNew (d.D.upR (e r)) = d.N.visAt RrNew (d.D.upR r)) →
    d.link.H.Fresh a.J.rels.rel d.link.P.bud
      (d.tgt.wideFact (a.S.sumP d.N RdOld RdNew) (a.S.sumO d.N RrOld RrNew)
        (a.S.sumP d.N (fun _ => False) own) Mb fun M => a.S.sumV d.N (fun _ => 0) (val M)).kc
      Mb (d.tgt.wideFact (a.S.sumP d.N RdOld RdNew) (a.S.sumO d.N RrOld RrNew)
        (a.S.sumP d.N (fun _ => False) own) Mb fun M => a.S.sumV d.N (fun _ => 0) (val M)).put

open Classical in
/-- Under the hypotheses below, the wide fact is fresh after the move in this sense: it is in
`(LdMv.send a d).After base`, whatever `base` is. -/
def segSend_after : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (base : MaskFact a.J.W → Prop) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : d.D.Own Mb) (RdOld : a.S.Ent → Prop) (RdNew : d.N.Ent → Prop)
      (RrOld : a.S.O → Prop) (RrNew : d.N.O → Prop) (own : d.N.Ent → Prop) (val : Mb → d.N.Ent → E),
    (∀ n, own n → RdNew n) →
    (∀ w M k₀ η (n : d.N.Ent), own n → d.D.upM (d.D.put w (U.mk' M k₀ η)) n.1 n.2 = val M n) →
    (∀ w M M' k₀ η η' (n : d.N.Ent), RdNew n → ¬ own n →
      d.D.upM (d.D.put w (U.mk' M k₀ η)) n.1 n.2 = d.D.upM (d.D.put w (U.mk' M' k₀ η')) n.1 n.2) →
    (∀ s w M M' k₀, (unif U.Pd).map (fun η => d.D.ans d.Sd s w (U.mk' M k₀ η)) =
      (unif U.Pd).map fun η => d.D.ans d.Sd s w (U.mk' M' k₀ η)) →
    (∀ T, d.N.budT d.t T →
      ∀ w M M' k₀ η η', ∃ e : d.D.Nn.Rnd ≃ d.D.Nn.Rnd, ∀ r,
        (∀ p ∈ T, d.D.Nn.enc (d.D.put w (U.mk' M k₀ η)) r p.1 p.2 =
          d.D.Nn.enc (d.D.put w (U.mk' M' k₀ η')) (e r) p.1 p.2) ∧
        d.N.visAt RrNew (d.D.upR (e r)) = d.N.visAt RrNew (d.D.upR r)) →
    (LdMv.send a d).After base
      (d.tgt.wideFact (a.S.sumP d.N RdOld RdNew) (a.S.sumO d.N RrOld RrNew)
        (a.S.sumP d.N (fun _ => False) own) Mb fun M => a.S.sumV d.N (fun _ => 0) (val M))

end

/-- What keeps the randomness of all members but o keeps the randomness at the names in Rr, if Rr
does not name o. -/
def segSend_hid_but : Prop :=
  ∀ (E : Type) (N : Sig E) (o : N.O) (Rr : N.O → Prop) (r r' : ∀ a, (N.om a).Rnd),
    ¬ Rr o → N.visBut o r' = N.visBut o r → N.visAt Rr r' = N.visAt Rr r

end Spec
end Cb
