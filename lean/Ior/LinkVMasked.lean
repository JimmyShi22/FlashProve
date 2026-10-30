-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVMasked.lean: honest-verifier zero knowledge for sets of slots of a chain of batch links
whose masks are sent in advance (`HonestV.ExactVWith`, Ior/LinkV.lean).

In standard terms: the file is about a sequential composition of interactive oracle reductions
that run on a batch of instances.

Definitions and statements; the proofs are in Ior/LinkVMaskedProofs.lean. No protocol, no code
occurs here. The analogue for batches (Ior/LinkV.lean) of Ior/Masked.lean and
Ior/KnowCollRulesMask.lean.

A batch link is an IOR with an annotation of its shape (`RoundSplits`, Iop/Batch.lean) and an honest side
(`IOR.HonestV`, Ior/LinkV.lean). A slot is one of the N places of a batch; the statements here
speak of a set J of slots, each with one instance.

Why: a link of a batch IOP may hide what it sends in the clear by mask entries that stand in an
oracle sent earlier in the chain: by the shared part (the masks then stand in the shared witness)
or by a slot (they stand in that slot's witness). Such a link is not zero knowledge by itself
(Ior/Masked.lean: `masked_not_exact`, in this sense: `¬ H.Exact Ri bud`, for one instance, under
its hypotheses; for a link of a batch [no theorem here]), so "a link, then a link"
(Ior/LinkVSeq.lean) does not take it.

Main names:
  `MaskDataV R W0 Wj N`: the parameters of the item.
      `k0 w0`, `kj wj`: what the link's messages read of the shared witness, of a slot's witness;
        `pub x`: of a slot's explicit part. (The reading meant; by type any maps `W0 → K0`,
        `Wj → Kj`, `X → Xp`.)
      `M0`, `put0`; `Mj`, `putj`: the values of the link's own mask entries in the shared witness,
        in a slot's witness, and how they are written into what is read. (The reading meant; by
        type any maps `M0 → K0 → K0`, `Mj → Kj → Kj`.) (A link with shared masks only has Mj =
        Unit; one with slots' masks only has M0 = Unit.)
      `Cl xp k κ`: the claim with which a slot starts. (The reading meant; by type any predicate
        `Xp → K0 → Kj → Prop`.) `msg k κ xp ρ`: all plain parts of a slot's local transcript, in
        closed form.
      `sim J xps ρs`: the simulator, for a set J of slots: it reads pub of the slots' explicit
        parts and their verifier messages, by type nothing else.
  `H.MMV D`, the item "masked messages": the link sends no oracle and withholds nothing; where the
    claim holds the plain parts of a slot's local transcript are msg (k0 w0) (kj wj) (pub x) ρ
    (only there: the shared part does not see a slot's explicit part; the claim ties the two); the
    claim does not read the own masks (exactly:
    `∀ xp k κ M Mj, D.Cl xp k κ → D.Cl xp (D.put0 M k) (D.putj Mj κ)`); and, at every ρ of the
    whole batch, for every set J, every k and every family (κ_j, xp_j) for which the claims hold,
    the law of the family ( msg (put0 M k) (putj M_j κ_j) xp_j ρ_j )_{j in J} over uniform (M,
    (M_j)) is sim J xp ρ. Jointly over the slots of J: a shared mask is one value for all.
  `H.FreshV N Ri bud k0 kj M0 put0 Mj putj`: a property of the honest side of the prefix: for
    non-empty `M0` and `Mj`: for every shared witness, every set J, every family in Ri, at every ρ
    and all further positions within the budget, the tuple ( for each slot of J: the notice, or
    (what the run shows, the explicit part handed on, kj of the slot's witness handed on); k0 of
    the shared witness handed on ) has the same law, over the prefix's coins, as the tuple in
    which the own mask entries are overwritten by fresh uniform ones. In words: given all that the
    prefix shows to the slots of J together, the link's masks are still uniform and independent of
    the rest of what the link reads.
  `Spec.exactV_seq_masked`, under the hypotheses of its statement: a prefix that is
    honest-verifier zero knowledge for sets of slots (`HonestV.ExactVWith`, Ior/LinkV.lean) and
    FreshV, then a link with the item MMV: the whole is honest-verifier zero knowledge for sets of
    slots, exact form, no new error. The simulator is named: that of "a link, then a link"
    (`LinkVSeq.sim`) on the prefix's simulator and the link's (`D.simOwnV`). The budget: `budSeqV`
    with nothing asked for the link, which has no oracle.

Limits: this file does not say how FreshV and MMV are had. Rules for the part that sends the
masks, for links that do not look at them, for an IOR in every slot and for an IOR run by the
shared part are stated in Ior/LinkVMaskedRules.lean, each under the hypotheses of its statement.
This file says nothing on soundness, nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVSeq
import Ior.Masked
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec}

/-- The parameters of the item "masked messages", for a link of a batch. -/
structure MaskDataV (R : IOR X Ei X' Eo) (W0 Wj : Type) (N : ℕ) where
  K0  : Type
  k0  : W0 → K0
  Kj  : Type
  kj  : Wj → Kj
  Xp  : Type
  pub : X → Xp
  M0  : Type
  [finM0 : Fintype M0]
  [neM0  : Nonempty M0]
  put0 : M0 → K0 → K0
  Mj  : Type
  [finMj : Fintype Mj]
  [neMj  : Nonempty Mj]
  putj : Mj → Kj → Kj
  Cl  : Xp → K0 → Kj → Prop
  msg : K0 → Kj → Xp → Rho R.shape → Plains R.shape
  sim : (J : Finset (Fin N)) → (J → Xp) → (J → Rho R.shape) → PMF (J → Plains R.shape)

attribute [instance] MaskDataV.finM0 MaskDataV.neM0 MaskDataV.finMj MaskDataV.neMj

/-- The item "masked messages", for sets of slots. -/
structure HonestV.MMV {R : IOR X Ei X' Eo} {A : RoundSplits R.shape} {W0 Wj W0' Wj' : Type}
    (H : R.HonestV A W0 Wj W0' Wj') {N : ℕ} (D : MaskDataV R W0 Wj N) : Prop where
  noOrc : IsEmpty (OPos R.shape)
  free  : H.withheld = ∅
  run   : ∀ w0 x wj c ρ, D.Cl (D.pub x) (D.k0 w0) (D.kj wj) →
    ((H.one w0 x wj c).run ρ).1.plains = D.msg (D.k0 w0) (D.kj wj) (D.pub x) ρ
  stable : ∀ xp k κ M Mj, D.Cl xp k κ → D.Cl xp (D.put0 M k) (D.putj Mj κ)
  law   : ∀ (J : Finset (Fin N)) (k : D.K0) (κ : J → D.Kj) (xp : J → D.Xp) (ρ : BRho N R.shape A),
    (∀ j, D.Cl (xp j) k (κ j)) →
    (unif (D.M0 × (Fin N → D.Mj))).map
        (fun M => fun j : J => D.msg (D.put0 M.1 k) (D.putj (M.2 j.1) (κ j)) (xp j) (ρ.slot j.1)) =
      D.sim J xp fun j => ρ.slot j.1

/-- the simulator of a masked link -/
def MaskDataV.simOwnV {R : IOR X Ei X' Eo} {W0 Wj : Type} {N : ℕ}
    (D : MaskDataV R W0 Wj N) (h : IsEmpty (OPos R.shape)) : R.SimV N :=
  fun J xs ρs _ _ => (D.sim J (fun j => D.pub (xs j)) ρs).map fun pl j => some (bareView h (pl j))

namespace HonestV
variable {R : IOR X Ei X' Eo} {A : RoundSplits R.shape} {W0 Wj W0' Wj' : Type}

open Classical in
/-- What the slots of J are shown and what a coming link reads: for each slot the notice, or (the
view at the further positions, the explicit part handed on, kj of the slot's witness handed on);
and k0 of the shared witness handed on. -/
def seenV (H : R.HonestV A W0 Wj W0' Wj') {N : ℕ} {K0 Kj : Type} (k0 : W0' → K0)
    (kj : Wj' → Kj) (w0 : W0) (J : Finset (Fin N)) (as : J → X × Wj) (ρ : BRho N R.shape A)
    (Ts : J → Finset (OPos R.shape)) (c : H.Coin0 × (Fin N → H.Coin)) :
    (J → Option (View R × X' × Kj)) × K0 :=
  (fun j =>
      if ρ.slot j.1 ∈ H.withheld then none
      else
        some (R.view (Ts j) ((H.one w0 (as j).1 (as j).2 (c.1, c.2 j.1)).run (ρ.slot j.1)).1,
            ((H.one w0 (as j).1 (as j).2 (c.1, c.2 j.1)).run (ρ.slot j.1)).2.2.1,
            kj ((H.one w0 (as j).1 (as j).2 (c.1, c.2 j.1)).run (ρ.slot j.1)).2.2.2),
    k0 ((H.strat0 w0 c.1).res (BRho.shared ρ)))

/-- the own mask entries overwritten -/
def overV {N : ℕ} {J : Finset (Fin N)} {V K0 Kj M0 Mj : Type} (put0 : M0 → K0 → K0)
    (putj : Mj → Kj → Kj) (M : M0 × (Fin N → Mj)) (z : (J → Option (V × X' × Kj)) × K0) :
    (J → Option (V × X' × Kj)) × K0 :=
  (fun j => (z.1 j).map fun t => (t.1, t.2.1, putj (M.2 j.1) t.2.2), put0 M.1 z.2)

/-- For non-empty `M0` and `Mj`: for every shared witness, every set J, every family in Ri, at
every ρ and all further positions within the budget, the tuple ( for each slot of J: the notice,
or (what the run shows, the explicit part handed on, kj of the slot's witness handed on); k0 of
the shared witness handed on ) has the same law, over the prefix's coins, as the tuple in which
the own mask entries are overwritten by fresh uniform ones. -/
def FreshV (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ) (Ri : X → Ei.Str → W0 × Wj → Prop)
    (bud : BudB R.shape N) {K0 Kj : Type} (k0 : W0' → K0) (kj : Wj' → Kj) (M0 : Type)
    [Fintype M0] [Nonempty M0] (put0 : M0 → K0 → K0) (Mj : Type) [Fintype Mj]
    [Nonempty Mj] (putj : Mj → Kj → Kj) : Prop :=
  ∀ (w0 : W0) (J : Finset (Fin N)) (as : J → X × Ei.Str × Wj),
    (∀ j, Ri (as j).1 (as j).2.1 (w0, (as j).2.2)) →
    ∀ (ρ : BRho N R.shape A) (Ts : J → Finset (OPos R.shape)), bud J (fun j => ρ.slot j.1) Ts →
      (unif ((H.Coin0 × (Fin N → H.Coin)) × (M0 × (Fin N → Mj)))).map (fun a =>
          overV put0 putj a.2 (H.seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts a.1)) =
        (unif (H.Coin0 × (Fin N → H.Coin))).map
          (H.seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts)

end HonestV
end IOR

namespace Spec
open IOR

/-- A prefix that is honest-verifier zero knowledge for sets of slots and fresh, then a masked
link: honest-verifier zero knowledge for sets of slots, with the simulator named. (not all
hypotheses are named here: see the statement below) -/
def exactV_seq_masked : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')
      (Ra : X → Ei.Str → W0 × Wj → Prop) (Rb : X' → Eo.Str → W0' × Wj' → Prop) (N : ℕ)
      (b₁ : BudB R₁.shape N) (S₁ : R₁.SimV N) (D : MaskDataV R₂ W0' Wj' N) (m : H₂.MMV D),
    R₁.IsLocal → H₁.AccV Ra Rb → H₁.ExactVWith N Ra b₁ S₁ →
    H₁.FreshV N Ra b₁ D.k0 D.kj D.M0 D.put0 D.Mj D.putj →
    (∀ x y w, Rb x y w → D.Cl (D.pub x) (D.k0 w.1) (D.kj w.2)) →
    (H₁.seqV H₂).ExactVWith N Ra (budSeqV R₁ R₂ b₁ fun _ _ _ => True)
      (LinkVSeq.sim R₁ R₂ H₁.withheld S₁ (D.simOwnV m.noOrc))

end Spec
end Iop
