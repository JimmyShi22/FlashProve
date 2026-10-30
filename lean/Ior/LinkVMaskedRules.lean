-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMaskedRules.lean: how two hypotheses of the rule for masked links of a batch, `FreshV`
and `MMV`, are had.

In standard terms: rules for interactive oracle reductions that run on a batch of instances: for
their sequential composition, for a reduction for one instance that is run on the batch, and a
weakening rule.

Definitions and statements; the proofs are in Ior/LinkVMaskedRulesProofs.lean (`blindV_local`,
`mmV_local`, `mmV_shared`, `freshV_conseq`), Ior/LinkVMaskedRulesSeq.lean (`freshV_seq`,
`freshV_snd`), Ior/LinkVMaskedRulesLocal.lean (`freshV_local`), Ior/LinkVMaskedRulesShared.lean
(`freshV_shared`, `blindV_shared`). No protocol, no code occurs here. `Spec.freshV_snd`,
`Spec.freshV_seq`, `Spec.freshV_conseq` are the analogues for batches of `Spec.fresh_snd`,
`Spec.fresh_seq`, `Spec.fresh_conseq` (Ior/KnowCollRulesMask.lean).

A block is an IOR R (Ior/Ior.lean) with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken
as a part of a chain. A batch link is an IOR with an annotation of its shape (`RoundSplits`,
Iop/Batch.lean) and an honest side (`IOR.HonestV`, Ior/LinkV.lean). A slot is one of the N places
of a batch; the statements here speak of a set J of slots, each with one instance.

What `FreshV` and `MMV` (the item "masked messages") say: their rows in the head of
Ior/LinkVMasked.lean. `H.Bad`, `H.Hid`: fields of `IOR.Honest`, Ior/Honest.lean.

The rule is in Ior/LinkVMasked.lean (`Spec.exactV_seq_masked`): under the hypotheses of its
statement: a prefix that is honest-verifier zero knowledge for sets of slots and FreshV, then a
link with the item MMV, is honest-verifier zero knowledge for sets of slots. (The notion:
`HonestV.ExactVWith`, Ior/LinkV.lean.)
Here, each rule under the hypotheses of its statement:

How `FreshV` is had (the types M0, Mj are non-empty):
  `Spec.freshV_snd`: the part that sends the masks comes last: if the second link is FreshV on all
    its inputs, so is "the first, then the second", whatever the first link is (it has to be
    complete).
  `H.BlindV`: a link that does not look at these masks: if what is read of two shared witnesses
    differs by an overwriting of the shared masks, and what is read of two witnesses of a slot by
    an overwriting of that slot's masks, then, with the same explicit part, coins and verifier
    messages:
      the slot's local transcript is the same,
      the slot ends with the same explicit part,
      and what is read of the witnesses handed on (the shared one, the slot's) differs by the same
        overwritings.
    For the shared witness the first condition alone is asked (field `shared`: from
    `k0 v0 = put0 M (k0 w0)`).
  `Spec.freshV_seq`: FreshV is carried through a link that is BlindV.
  `Spec.freshV_conseq`: a smaller relation, a smaller budget, coarser readings.
  `Spec.freshV_local`: an IOR in every slot (`H.localV`) that is Fresh for one instance
    (Ior/KnowCollRulesMask.lean) is FreshV for the slots' masks: the slots are independent. No
    shared mask; the shared witness is handed on.
  `Spec.freshV_shared`: a sending run by the shared part alone (`H.sharedV s0`) that is Fresh for
    one instance is FreshV for shared masks, at the union of the slots' further positions. After
    such a link the messages just sent stand in the shared witness and, as a copy, in each slot's
    witness (the slot recomputes its result). Asked beside `∀ w x, H.Hid w x = ∅` and RiV → Ri:
      the one-instance prover's transcript is s0's;
      what the masked link will read of the shared witness (k0) is the one-instance reading (kc)
        of a slot's result;
      what a slot hands on (its explicit part, and kj of its witness) is a function G of its own
        data, the plain parts shown, the verifier messages and that reading, and G is blind to the
        masks: a slot may keep and later read the other messages of the sending, not the masks;
      and, for an empty set of slots or verifier messages that are withheld: the reading of s0's
        result alone has a law that the overwriting does not change (asked at every w0 and ρ).
  `Spec.blindV_local`: an IOR in every slot that is Blind for one instance is BlindV, for the
    slots' masks and for any shared masks (it does not see the shared witness).
  `Spec.blindV_shared`: an IOR run by the shared part alone is BlindV if s0 does not look at the
    shared masks (same transcript; the reading of its result differs by the overwriting) and the
    one-instance prover, from which a slot recomputes its result, is Blind for the slots' masks.
How `MMV` is had:
  `D.localV W0 N`, `Spec.mmV_local`: a masked block for one instance (Ior/Masked.lean: `H.MM D`),
    run in every slot: masks in the slots' witnesses; the simulator is the block's, in each slot
    of J independently.
  `D.sharedV k N`, `Spec.mmV_shared`: a masked block run by the shared part alone
    (`H.sharedV s0`): masks in the shared witness, read through k; all slots see one transcript;
    the simulator is the block's, once, shown to every slot of J. Asked beside `H.Bad = ∅`:
      s0's plain parts are the block's closed form on what is read of the shared witness, at the
        public part that the claim ties to it;
      the claim determines the public part from what is read (the shared witness holds the shared
        explicit part).

Limits: this file says nothing on soundness, nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVMasked
import Ior.LinkVRules
import Ior.KnowCollRulesMask
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal

namespace IOR
variable {X X' : Type} {Ei Eo : ExtSpec}

/-- A link that does not look at the masks. -/
structure HonestV.BlindV {R : IOR X Ei X' Eo} {A : RoundSplits R.shape} {W0 Wj W0' Wj' : Type}
    (H : R.HonestV A W0 Wj W0' Wj') {K0 Kj K0' Kj' : Type} (k0 : W0 → K0) (kj : Wj → Kj)
    (k0' : W0' → K0') (kj' : Wj' → Kj') (M0 Mj : Type) (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj)
    (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj') : Prop where
  shared : ∀ (w0 v0 : W0) (M : M0) (c0 : H.Coin0) (σ : RhoSh R.shape A),
    k0 v0 = put0 M (k0 w0) → k0' ((H.strat0 v0 c0).res σ) = put0' M (k0' ((H.strat0 w0 c0).res σ))
  slot   : ∀ (w0 v0 : W0) (wj vj : Wj) (M : M0) (Ms : Mj) (x : X)
        (c : H.Coin0 × H.Coin) (ρ : Rho R.shape),
      k0 v0 = put0 M (k0 w0) → kj vj = putj Ms (kj wj) →
      ((H.one v0 x vj c).run ρ).1 = ((H.one w0 x wj c).run ρ).1 ∧
      ((H.one v0 x vj c).run ρ).2.2.1 = ((H.one w0 x wj c).run ρ).2.2.1 ∧
      kj' ((H.one v0 x vj c).run ρ).2.2.2 = putj' Ms (kj' ((H.one w0 x wj c).run ρ).2.2.2)

/-- A masked block for one instance, run in every slot: the parameters. -/
def MaskData.localV
    {R : IOR X Ei X' Eo} {Wi : Type} (D : MaskData R Wi) (W0 : Type) (N : ℕ) :
    MaskDataV R W0 Wi N where
  K0 := Unit
  k0 := fun _ => ()
  Kj := D.Kc
  kj := D.kc
  Xp := D.Xp
  pub := D.pub
  M0 := Unit
  put0 := fun _ k => k
  Mj := D.Mk
  putj := D.put
  Cl := fun xp _ κ => D.Cl xp κ
  msg := fun _ κ xp ρ => D.msg κ xp ρ
  sim := fun J xps ρs => pis fun j : J => D.sim (xps j) (ρs j)

open Classical in
/-- A masked block run by the shared part alone: the parameters. k: what the block's messages
read, now of the shared witness. -/
def MaskData.sharedV
    {R : IOR X Ei X' Eo} {Wi W0 : Type} (D : MaskData R Wi) (k : W0 → D.Kc) (N : ℕ) :
    MaskDataV R W0 Wi N where
  K0 := D.Kc
  k0 := k
  Kj := Unit
  kj := fun _ => ()
  Xp := D.Xp
  pub := D.pub
  M0 := D.Mk
  put0 := D.put
  Mj := Unit
  putj := fun _ κ => κ
  Cl := fun xp k _ => D.Cl xp k
  msg := fun k _ xp ρ => D.msg k xp ρ
  sim := fun J xps ρs =>
    if h : Nonempty J then
      (D.sim (xps (Classical.choice h)) (ρs (Classical.choice h))).map fun pl _ =>
        pl else PMF.pure fun j => (h ⟨j⟩).elim

end IOR

namespace Spec
open IOR

/-- The part that sends the masks comes last. In words: the row of `Spec.freshV_snd` in the head. -/
def freshV_snd : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')
      (Ra : X → Ei.Str → W0 × Wj → Prop) (Rb : X' → Eo.Str → W0' × Wj' → Prop) (N : ℕ)
      (b₁ : BudB R₁.shape N) (b₂ : BudB R₂.shape N) (K0 Kj : Type) (k0 : W0'' → K0) (kj : Wj'' → Kj)
      (M0 : Type) [Fintype M0] [Nonempty M0] (put0 : M0 → K0 → K0) (Mj : Type) [Fintype Mj]
      [Nonempty Mj] (putj : Mj → Kj → Kj),
    H₁.AccV Ra Rb → H₂.FreshV N Rb b₂ k0 kj M0 put0 Mj putj →
    (H₁.seqV H₂).FreshV N Ra (budSeqV R₁ R₂ b₁ b₂) k0 kj M0 put0 Mj putj

/-- States: FreshV is carried through a link that does not look at the masks. -/
def freshV_seq : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')
      (Ra : X → Ei.Str → W0 × Wj → Prop) (N : ℕ) (b₁ : BudB R₁.shape N) (b₂ : BudB R₂.shape N)
      (K0 Kj K0' Kj' : Type) (k0 : W0' → K0) (kj : Wj' → Kj) (k0' : W0'' → K0') (kj' : Wj'' → Kj')
      (M0 : Type) [Fintype M0] [Nonempty M0] (Mj : Type) [Fintype Mj] [Nonempty Mj]
      (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj) (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
    H₁.FreshV N Ra b₁ k0 kj M0 put0 Mj putj → H₂.BlindV k0 kj k0' kj' M0 Mj put0 putj put0' putj' →
    (H₁.seqV H₂).FreshV N Ra (budSeqV R₁ R₂ b₁ b₂) k0' kj' M0 put0' Mj putj'

/-- A smaller relation, a smaller budget, coarser readings (g0, gj, which commute with the
overwritings). -/
def freshV_conseq : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (W0 Wj W0' Wj' : Type)
      (H : R.HonestV A W0 Wj W0' Wj') (Ri Ri' : X → Ei.Str → W0 × Wj → Prop) (N : ℕ)
      (bud bud' : BudB R.shape N) (K0 Kj K0' Kj' : Type) (k0 : W0' → K0) (kj : Wj' → Kj)
      (g0 : K0 → K0') (gj : Kj → Kj') (M0 : Type) [Fintype M0] [Nonempty M0] (Mj : Type)
      [Fintype Mj] [Nonempty Mj] (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj)
      (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
    (∀ x y w, Ri' x y w → Ri x y w) → (∀ J ρs Ts, bud' J ρs Ts → bud J ρs Ts) →
    (∀ M k, g0 (put0 M k) = put0' M (g0 k)) → (∀ M k, gj (putj M k) = putj' M (gj k)) →
    H.FreshV N Ri bud k0 kj M0 put0 Mj putj →
    H.FreshV N Ri' bud' (fun w => g0 (k0 w)) (fun w => gj (kj w)) M0 put0' Mj putj'

/-- States, under the hypotheses below: an IOR in every slot that is Fresh for one instance is
FreshV for the slots' masks. -/
def freshV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (Ri : X → Ei.Str → Wi → Prop) (RiV : X → Ei.Str → W0 × Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (N : ℕ) (K0 Kc : Type) (k0 : W0 → K0)
      (kc : Wo → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    H.Fresh Ri bud kc Mk put → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (H.localV W0).FreshV N RiV (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j))
      k0 kc Unit (fun _ k => k) Mk put

open Classical in
/-- States, under the hypotheses below: a sending run by the shared part alone that is Fresh for
one instance is FreshV for shared masks, at the union of the slots' further positions. -/
def freshV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (Ri : X → Ei.Str → Wi → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (N : ℕ)
      (Kc Kj : Type) (kc : Wo → Kc) (k0 : W0' → Kc) (kj : Wo → Kj) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (put : Mk → Kc → Kc) (G : X → Wi → Plains R.shape → Rho R.shape → Kc → X' × Kj),
    H.Fresh Ri bud kc Mk put → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ((H.strat w.2 x c).run ρ).1 = ((s0 w.1 c).run ρ).1) →
    (∀ x y w c ρ, RiV x y w → kc ((H.strat w.2 x c).run ρ).2.2 = k0 ((s0 w.1 c).run ρ).2) →
    (∀ x y w c ρ, RiV x y w →
      (((H.strat w.2 x c).run ρ).2.1, kj ((H.strat w.2 x c).run ρ).2.2) =
        G x w.2 ((H.strat w.2 x c).run ρ).1.plains ρ (kc ((H.strat w.2 x c).run ρ).2.2)) →
    (∀ x wi pl ρ k M, G x wi pl ρ (put M k) = G x wi pl ρ k) →
    (∀ w0 ρ, (unif (H.Coin × Mk)).map (fun a => put a.2 (k0 ((s0 w0 a.1).run ρ).2)) =
      (unif H.Coin).map fun c => k0 ((s0 w0 c).run ρ).2) →
    (H.sharedV s0).FreshV N RiV (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts))
      k0 kj Mk put Unit (fun _ k => k)

/-- States: an IOR in every slot that is Blind for one instance is BlindV; it does not see the
shared witness, which it hands on. -/
def blindV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (K0 Ki Ko : Type) (k0 : W0 → K0) (kci : Wi → Ki) (kco : Wo → Ko) (M0 Mk : Type)
      (put0 : M0 → K0 → K0) (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    H.Blind kci kco Mk puti puto → (H.localV W0).BlindV k0 kci k0 kco M0 Mk put0 puti put0 puto

/-- An IOR run by the shared part alone that does not look at the masks. In words: the row of
`Spec.blindV_shared` in the head. -/
def blindV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (K0 K0' Ki Ko : Type) (k0 : W0 → K0) (k0' : W0' → K0')
      (kci : Wi → Ki) (kco : Wo → Ko) (M0 Mk : Type) (put0 : M0 → K0 → K0) (put0' : M0 → K0' → K0')
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ (w0 v0 : W0) (M : M0) (c : H.Coin) (ρ : Rho R.shape), k0 v0 = put0 M (k0 w0) →
      ((s0 v0 c).run ρ).1 = ((s0 w0 c).run ρ).1 ∧
      k0' ((s0 v0 c).run ρ).2 = put0' M (k0' ((s0 w0 c).run ρ).2)) →
    H.Blind kci kco Mk puti puto → (H.sharedV s0).BlindV k0 kci k0' kco M0 Mk put0 puti put0' puto

/-- A masked block for one instance, run in every slot. In words: the row of `Spec.mmV_local` in
the head. -/
def mmV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (N : ℕ),
    H.MM D → H.Bad = ∅ → (H.localV W0).MMV (D.localV W0 N)

/-- A masked block run by the shared part alone. In words: the row of `Spec.mmV_shared` in the
head. -/
def mmV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (D : MaskData R Wi) (k : W0 → D.Kc) (N : ℕ),
    H.MM D → H.Bad = ∅ →
    (∀ w0 c ρ xp, D.Cl xp (k w0) → ((s0 w0 c).run ρ).1.plains = D.msg (k w0) xp ρ) →
    (∀ xp xp' κ, D.Cl xp κ → D.Cl xp' κ → xp = xp') → (H.sharedV s0).MMV (D.sharedV k N)

end Spec
end Iop
