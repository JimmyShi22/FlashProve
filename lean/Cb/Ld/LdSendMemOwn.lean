-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendMemOwn.lean: under the hypotheses of its statements, a sender made from senders of the
members, with independent coins: masks of a coming block that stand in several members are fresh
after the sending, in the letters of the wide fact.

This file is on those coins of an honest prover that go into its messages (`Sig.Sender.Mk`). The
data of the honest prover (`Sig.Sender`, Cb/Ld/LdSendFam.lean) of a reduction that sends several
words in one prover message are built (`Sig.Sender.ofMem`, Cb/Ld/LdSendMem.lean) from the data of
the honest prover for each word; the masks that one later reduction of a chain will use may be
spread over several of the words' messages.

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is the conclusion of
`Spec.memOwn_fresh`.

Definitions, statements (Cb.Spec.memOwn_*) and proofs.

Why: the one sending of a closing sends the closing's new messages and the first oracle messages of
the next segment, which hold the own masks of that segment's blocks (Cb/Ld/LdGroupNewRide.lean:
riders). The masks of one block may be spread over many members. Cb/Ld/LdSendStdOwn.lean has this
for the standard sender of a layout; here for any members' senders, so that a family put together
from two makes of senders is covered.

The data (`X : MemSplit mem`). For each member a: its coins as (free coins Fr a, pad coins Pd a).
Every Pd a is finite and not empty.
  `X.Unif`: for every fixing of the free coins, every member's answers are uniform over its pad
    coins, at every seed and witness.
  `X.own ε rest w0`: the split of the family's coins for a block, from a split ε of all free coins
    into (own masks, the others); the pads: all pad coins.

Main names, each under the hypotheses of its statement:
  `Spec.memOwn_pad`: `X.Unif` ⇒ for one witness and one fixing of the other free coins the law of
    all answers over the pads does not depend on the own masks, however seeds are shared.
  `Spec.memOwn_hid`: every member's encoder hides `t a` long positions ⇒ between any two messages a
    change of the encoding randomness keeps all symbols read within the budget (`Sig.budT`,
    Cb/Ld/LdSendFam.lean)
    (in this sense: ∀ T, N.budT t T → ∀ m m' : (Sig.Sender.ofMem mem rest w0).Nn.Msg,
      ∃ e : (Sig.Sender.ofMem mem rest w0).Nn.Rnd ≃ (Sig.Sender.ofMem mem rest w0).Nn.Rnd, ∀ r,
      (∀ p ∈ T, (Sig.Sender.ofMem mem rest w0).Nn.enc m r p.1 p.2 =
        (Sig.Sender.ofMem mem rest w0).Nn.enc m' (e r) p.1 p.2) ∧
      N.visAt (fun _ => False) ((Sig.Sender.ofMem mem rest w0).upR (e r)) =
        N.visAt (fun _ => False) ((Sig.Sender.ofMem mem rest w0).upR r)).
  `Spec.memOwn_fresh`: so the sending is Fresh (`Honest.Fresh`, Ior/KnowCollRulesMask.lean) for the
    wide fact (`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean; its reading: `Sig.wide`) that shows:
      of the old messages and randomness anything;
      of the new messages the entries in RdNew;
      no new encoding randomness;
    from:
      `X.Unif`;
      every member's encoder hides `t o` long positions (o: the member);
      own ⊆ RdNew;
      an own entry holds the mask's value;
      an entry in RdNew that is not own reads neither the own masks nor a pad coin.

Limits: the reading forgets all new encoding randomness: such a fact serves the blocks that follow;
it does not cross a closing whose group holds a member of the same sending (for that:
Cb/Ld/LdSendFreshVis.lean, Cb/Ld/LdSendStdVis.lean: masks in one member).
This file does not say that a given family has such a split (for standard riders:
Cb/Ld/LdGroupRideStdFresh.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- The coins of each member as (free coins, pad coins). -/
structure MemSplit {E : Type} [Field E] {N : Sig E} {W : Type}
    (mem : ∀ a, (N.om a).Sender W Unit) where
  Fr : N.O → Type
  Pd : N.O → Type
  [finPd : ∀ a, Fintype (Pd a)]
  [nePd : ∀ a, Nonempty (Pd a)]
  κ : ∀ a, (mem a).Mk ≃ Fr a × Pd a

attribute [instance] MemSplit.finPd MemSplit.nePd

namespace MemSplit
variable {E : Type} [Field E] {N : Sig E} {W W' : Type}
  {mem : ∀ a, (N.om a).Sender W Unit} (X : MemSplit mem)

/-- the member a with its free coins fixed -/
@[reducible] def fix (x : ∀ a, X.Fr a) : ∀ a, (N.om a).Sender W Unit := fun a =>
  { N := (mem a).N
    upM := (mem a).upM
    upR := (mem a).upR
    Mk := X.Pd a
    put := fun w η => (mem a).put w ((X.κ a).symm (x a, η))
    rest := fun _ => ()
    w0 := (mem a).w0 }

/-- over its pad coins alone every member's answers are uniform -/
def Unif [Fintype E] : Prop := ∀ x a, (X.fix x a).Uniform

open Classical in
/-- The split of the family's coins for a block. -/
def own {Mb M0 : Type} [Fintype M0] [Nonempty M0] (ε : (∀ a, X.Fr a) ≃ Mb × M0)
    (rest : W → W') (w0 : W) :
    (Sig.Sender.ofMem mem rest w0).Own Mb where
  M0 := M0
  Pd := ∀ a, X.Pd a
  κ := { toFun := fun k => (ε fun a => (X.κ a (k a)).1, fun a => (X.κ a (k a)).2)
         invFun := fun y a => (X.κ a).symm (ε.symm y.1 a, y.2 a)
         left_inv := fun k => funext fun a => by simp
         right_inv := fun y => by simp }

end MemSplit

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

open Classical in
def memOwn_pad : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (X : MemSplit mem)
      (Mb M0 : Type) [Fintype M0] [Nonempty M0] (ε : (∀ a, X.Fr a) ≃ Mb × M0) (rest : W → W')
      (w0 : W) (Sd : N.Seeds),
    X.Unif →
    ∀ s w M M' k₀,
      (unif (X.own ε rest w0).Pd).map
          (fun η => (Sig.Sender.ofMem mem rest w0).ans Sd s w ((X.own ε rest w0).mk' M k₀ η)) =
        (unif (X.own ε rest w0).Pd).map fun η =>
          (Sig.Sender.ofMem mem rest w0).ans Sd s w ((X.own ε rest w0).mk' M' k₀ η)

def memOwn_hid : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit)
      (rest : W → W') (w0 : W) (t : N.O → ℕ),
    (∀ a, (mem a).N.Hides ((N.om a).C.budT (t a))) →
    ∀ T, N.budT t T →
      ∀ m m' : (Sig.Sender.ofMem mem rest w0).Nn.Msg,
        ∃ e : (Sig.Sender.ofMem mem rest w0).Nn.Rnd ≃ (Sig.Sender.ofMem mem rest w0).Nn.Rnd, ∀ r,
          (∀ p ∈ T, (Sig.Sender.ofMem mem rest w0).Nn.enc m r p.1 p.2 =
            (Sig.Sender.ofMem mem rest w0).Nn.enc m' (e r) p.1 p.2) ∧
          N.visAt (fun _ => False) ((Sig.Sender.ofMem mem rest w0).upR (e r)) =
            N.visAt (fun _ => False) ((Sig.Sender.ofMem mem rest w0).upR r)

variable (Kc : Type)

/-- Under the hypotheses below, the sending is fresh for the wide fact. -/
def memOwn_fresh : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (bk : N.Msg → Wp' → a.Wp)
      (L t : N.O → ℕ) (mem : ∀ o, (N.om o).Sender (a.S.Wit × a.Wp) Unit)
      (rest : a.S.Wit × a.Wp → a.S.Wit × Wp') (w0 : a.S.Wit × a.Wp) (X : MemSplit mem)
      (Mb M0 : Type) [Fintype Mb] [Nonempty Mb] [Fintype M0] [Nonempty M0]
      (ε : (∀ o, X.Fr o) ≃ Mb × M0) (RdOld : a.S.Ent → Prop) (RdNew : N.Ent → Prop)
      (RrOld : a.S.O → Prop) (own : N.Ent → Prop) (val : Mb → N.Ent → E),
    X.Unif → (∀ o, (mem o).N.Hides ((N.om o).C.budT (t o))) → (∀ n, own n → RdNew n) →
    (∀ w M k₀ (η : ∀ o, X.Pd o) (n : N.Ent), own n →
      (mem n.1).upM ((mem n.1).put w ((X.κ n.1).symm (ε.symm (M, k₀) n.1, η n.1))) n.2 = val M n) →
    (∀ w M M' k₀ (η η' : ∀ o, X.Pd o) (n : N.Ent), RdNew n → ¬ own n →
      (mem n.1).upM ((mem n.1).put w ((X.κ n.1).symm (ε.symm (M, k₀) n.1, η n.1))) n.2 =
        (mem n.1).upM ((mem n.1).put w ((X.κ n.1).symm (ε.symm (M', k₀) n.1, η' n.1))) n.2) →
    (⟨N, Sd, Wp', bk, Sig.Sender.ofMem mem rest w0, L, t⟩ : LdSendD a).link.H.Fresh a.J.rels.rel
      (⟨N, Sd, Wp', bk, Sig.Sender.ofMem mem rest w0, L, t⟩ : LdSendD a).link.P.bud
      ((⟨N, Sd, Wp', bk, Sig.Sender.ofMem mem rest w0, L, t⟩ : LdSendD a).tgt.wideFact
        (a.S.sumP N RdOld RdNew) (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) own)
        Mb fun M => a.S.sumV N (fun _ => 0) (val M)).kc
      Mb ((⟨N, Sd, Wp', bk, Sig.Sender.ofMem mem rest w0, L, t⟩ : LdSendD a).tgt.wideFact
        (a.S.sumP N RdOld RdNew) (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) own)
        Mb fun M => a.S.sumV N (fun _ => 0) (val M)).put

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem memOwn_pad : Spec.memOwn_pad E := by
  classical
  intro N W W' mem X Mb M0 _ _ ε rest w0 Sd hU s w M M' k₀
  have h1 := ldSendMem_uniform E N W W' (X.fix (ε.symm (M, k₀))) rest w0 Sd (hU _) s w
  have h2 := ldSendMem_uniform E N W W' (X.fix (ε.symm (M', k₀))) rest w0 Sd (hU _) s w
  exact h1.trans h2.symm

omit [Field E] [Fintype E] in
theorem memOwn_hid : Spec.memOwn_hid E := by
  intro N W W' mem rest w0 t h T hT m m'
  obtain ⟨e, he⟩ := (hides_iff_equiv _ (Sig.Sender.ofMem mem rest w0).Nn (N.budT t)).1
    (ldSendMem_hides E N W W' mem rest w0 t h) T hT m m'
  exact ⟨e, fun r =>
      ⟨fun p hp => eq_of_heq (Sigma.mk.inj (he r p hp)).2,
        funext fun _ => (if_neg fun h : False => h).trans (if_neg fun h : False => h).symm⟩⟩

theorem memOwn_fresh {Kc : Type} : Spec.memOwn_fresh E Kc := by
  intro a N Sd Wp' bk L t mem rest w0 X Mb M0 _ _ _ _ ε RdOld RdNew RrOld own val hU hH hs ho hf
  exact segSend_fresh E Kc a ⟨N, Sd, Wp', bk, Sig.Sender.ofMem mem rest w0, L, t⟩ Mb
    (X.own ε rest w0) RdOld RdNew RrOld (fun _ => False) own val hs
    (fun w M k₀ η n hn => ho w M k₀ η n hn)
    (fun w M M' k₀ η η' n h1 h2 => hf w M M' k₀ η η' n h1 h2)
    (memOwn_pad N _ _ mem X Mb M0 ε rest w0 Sd hU)
    (fun T hT w M M' k₀ η η' => memOwn_hid N _ _ mem rest w0 t hH T hT _ _)

end
end Cb
