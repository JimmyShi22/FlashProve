-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Masked.lean: blocks whose masks were sent in advance: the item "masked messages" (`Honest.MM`),
the bundle of such a block, and the same block with the masks as its coins.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean): what is
asked of one reduction of a composition and of its honest prover.
Definitions, statements and proofs. No protocol, no code occurs here.
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain.

Why: a block may hide what it sends in the clear by mask entries that the prover has sent earlier,
inside an oracle that holds much else. For such a block the masks stand in the input witness, and
its honest prover has no coins that matter.
The honest-verifier zero-knowledge field of the bundles (Ior/Chain.lean: `Good`;
Ior/KnowCollGood.lean: `GoodT`), `exact`, speaks of every witness of the relation and of the law
over the block's own coins. A block of this kind does not have it: its first message is a function
of the witness's mask entries, and the simulator is given nothing that depends on them (what it is
given: `Honest.ExactWith`, Ior/Honest.lean; that nothing of it depends on them: the premises of
`Spec.masked_not_exact`). [An argument in words; `Spec.masked_not_exact` makes it a statement. Its
premise, two witnesses of one explicit part, each with some oracles that the verifier does not
read, with different plain parts at some ρ with `bud ρ ∅`, is met although the explicit part holds
answers that read the masks: an entry that is used for nothing else absorbs the difference in the
answer (no theorem here).] What such a block has is an item of its own; zero knowledge is then a
property of a whole chain that also holds the round in which the masks are sent.

Main names:
 1. `GoodB R H A B ext P`: `GoodT` without the field `exact`, field for field: strings (`point`),
    local, complete, conditions handed on, cores, the two probabilities, knowledge soundness.
    `Spec.goodB_seq_ext`, `Spec.goodB_seq`: the rule for chains. `Spec.goodB_conseq` to
    `Spec.goodB_cf_out`: the other rules of Ior/KnowCollGood.lean, but for the two on `Good`. So
    all of the bundle `GoodT` but the clause on zero knowledge goes through a chain as before,
    whatever the kinds of its blocks.
 2. `MaskData R Wi`: the parameters of the item.
      `kc w`: what the block's messages read of a witness (messages and mask entries; not encoding
        randomness). (The reading meant; by type any map `Wi → Kc`.)
      `pub x`: what the block's messages and its simulator read of the explicit part (state and
        targets; not what earlier rounds have shown of the oracles that hold the masks). (The
        reading meant; by type any map `Xi → Xp`.)
      `Mk`, `put`: the values of the block's own mask entries; put M k: k with these entries
        overwritten by M. All else in k is fixed, the mask entries of other blocks too. (The
        reading meant; of the fields of `Honest.MM` only `stable` and `law` name `put`.)
      `Cl xp k`: the claim with which the block starts. It does not read the own entries (field
        `stable`) (exactly: `∀ xp k M, D.Cl xp k → D.Cl xp (D.put M k)`); so it is the predicate on
        messages without whatever earlier rounds have asked of the oracle that holds the masks.
        (The reading meant; by type any predicate `Xp → Kc → Prop`; of the fields of `Honest.MM`
        only `stable` and `law` name `Cl`.)
      `msg`: all plain parts of the honest prover, in closed form. `sim`: the simulator: it reads
        pub x and the verifier's messages, by type nothing else.
    `H.MM D`, the item: the block sends no oracle and withholds nothing; its plain parts are msg
    (kc w) (pub x) ρ; the claim does not read the own masks (exactly:
    `∀ xp k M, D.Cl xp k → D.Cl xp (D.put M k)`); and, at every ρ, for every k for which the claim
    holds, the law of msg (put M k) xp ρ over uniform M is sim xp ρ. Exact: no error term. (At
    every ρ: a challenge that must not be 0 has a challenge set without 0.)
    Narrower than need be, on purpose: "no oracle", "nothing withheld", and that the honest
    messages read a witness through kc and the explicit part through pub.
 3. `GoodM R H A B ext P D`: the bundle of a masked block: `GoodB`, the item, and "the relation
    implies the claim".
 4. The same block with the masks as its coins (`H.own Mk putW`): the honest prover first draws M,
    overwrites the own entries of its witness, and goes on as H. (The reading meant; this file asks
    nothing of `putW` but the premise of `Spec.exact_own`.) `Spec.exact_own`, under the hypotheses
    of its statement: it is honest-verifier zero knowledge in our exact form
    (`Honest.ExactWith`, Ior/Honest.lean), for every witness for which the claim holds, at every
    budget, without error, with the simulator "sim, and no oracle".
    This is the block of an analysis in which each masked block draws its masks, keeps them in its
    witness, and the oracle that holds them is sent late. It is not the block that first sends its
    masks in a fresh oracle of their own (that one has a bound on queries and the error of the
    encoding [no theorem here]). Nothing is said here on relations for which `H.own` is complete.

Limits: this file does not say that a chain of masked blocks, of the rounds that send their masks
and of blocks with the field `exact` is zero knowledge: that is a lemma of its own, with conditions
on who reads which entry when. It says nothing on running times.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollGood
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- All of `GoodT` but zero knowledge. -/
structure GoodB (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  acc     : H.Acc A.rel B.rel
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  keeps   : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w
  prBad   : prRho H.Bad ≤ P.pBad
  cover   : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)
  prCov   : ∀ k, prRho (P.cov k) ≤ P.pHid
  know    : R.red.Know A.on A.relR B.relR ext P.err

/-- The parameters of the item "masked messages". -/
structure MaskData (R : IOR Xi Ei Xo Eo) (Wi : Type) where
  /-- what the block's messages read of a witness -/
  Kc  : Type
  kc  : Wi → Kc
  /-- what the block's messages and the simulator read of the explicit part -/
  Xp  : Type
  pub : Xi → Xp
  /-- the values of the block's own mask entries, and how they are written into what is read of a
  witness (by type any map `Mk → Kc → Kc`) -/
  Mk  : Type
  [finMk : Fintype Mk]
  [neMk  : Nonempty Mk]
  put : Mk → Kc → Kc
  /-- the claim with which the block starts -/
  Cl  : Xp → Kc → Prop
  /-- the honest prover's plain parts, in closed form -/
  msg : Kc → Xp → Rho R.shape → Plains R.shape
  /-- the simulator -/
  sim : Xp → Rho R.shape → PMF (Plains R.shape)

attribute [instance] MaskData.finMk MaskData.neMk

/-- The item "masked messages". -/
structure Honest.MM {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (D : MaskData R Wi) : Prop where
  /-- the block sends no oracle -/
  noOrc : IsEmpty (OPos R.shape)
  /-- nothing is withheld -/
  free  : ∀ w x, H.withheld w x = ∅
  /-- the plain parts are the closed form -/
  run   : ∀ w x c ρ, ((H.strat w x c).run ρ).1.plains = D.msg (D.kc w) (D.pub x) ρ
  /-- the claim does not read the own masks
  (exactly: `∀ xp k M, D.Cl xp k → D.Cl xp (D.put M k)`) -/
  stable : ∀ xp k M, D.Cl xp k → D.Cl xp (D.put M k)
  /-- under `D.Cl xp k`: over the own masks, all else fixed, the plain parts have the law of the
  simulator -/
  law   : ∀ k xp ρ, D.Cl xp k → (unif D.Mk).map (fun M => D.msg (D.put M k) xp ρ) = D.sim xp ρ

/-- The bundle of a masked block. -/
structure GoodM (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (P : Nums K R) (D : MaskData R Wi) : Prop where
  base  : GoodB R H A B ext P
  mm    : H.MM D
  claim : ∀ x y w, A.rel x y w → D.Cl (D.pub x) (D.kc w)

/-- The same block with the masks as its coins. -/
def Honest.own {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (putW : Mk → Wi → Wi) : R.Honest Wi Wo where
  Coin  := Mk × H.Coin
  strat := fun w x c => H.strat (putW c.1 w) x c.2
  Bad   := H.Bad
  Hid   := fun w x => {ρ | ∃ M, ρ ∈ H.Hid (putW M w) x}

/-- what a run without oracles shows -/
def bareView {R : IOR Xi Ei Xo Eo} (h : IsEmpty (OPos R.shape)) (pl : Plains R.shape) : View R :=
  ⟨pl, fun p => (h.false p).elim⟩

/-- the simulator of the block with the masks as its coins -/
def MaskData.simOwn
    {R : IOR Xi Ei Xo Eo} (D : MaskData R Wi) (h : IsEmpty (OPos R.shape)) : Honest.Sim R :=
  fun x ρ _ _ => (D.sim (D.pub x) ρ).map fun pl => some (bareView h pl)

end IOR

namespace Spec
open IOR

/-- States: `GoodT` is equivalent to `GoodB` and the field `exact`. -/
def goodT_iff : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodT R H A B ext P ↔ GoodB R H A B ext P ∧ H.Exact A.rel P.bud

/-- The rule for chains, general form. -/
def goodB_seq_ext : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ext : X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    GoodB R₁ H₁ A B e₁ P₁ → GoodB R₂ H₂ B C e₂ P₂ →
    (∀ a (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) b w,
      R₁.red.out a τ₁ = some b → ext a (Tr.app τ₁ τ₂) w = e₁ a τ₁ (e₂ b τ₂ w)) →
    GoodB (R₁.seq R₂) (H₁.seq H₂) A C ext (P₁.seq P₂)

/-- The rule for chains, without its clause on zero knowledge. -/
def goodB_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    GoodB R₁ H₁ A B e₁ P₁ → GoodB R₂ H₂ B C e₂ P₂ →
    GoodB (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂)

/-- Consequence, with the premises of `Spec.goodT_conseq` (Ior/KnowCollGood.lean). -/
def goodB_conseq : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A A' : Rels K Xi Ei Wi) (B B' : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P P' : Nums K R),
    GoodB R H A B ext P → (∀ x y w, A'.rel x y w → A.rel x y w) →
    (∀ x y w, B.rel x y w → B'.rel x y w) → (∀ a, A'.on a → A.on a) → (∀ b, B.on b → B'.on b) →
    (∀ a w, A'.on a → A.relR a w → A'.relR a w) → (∀ b w, B'.relR b w → B.relR b w) →
    (∀ w, A'.core w = A.core w) → (∀ w, B'.core w = B.core w) → P.Le P' → GoodB R H A' B' ext P'

def goodB_ext_congr : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext ext' : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    (∀ a τ b w, A.on a → R.red.out a τ = some b → B.relR b w → ext' a τ w = ext a τ w) →
    GoodB R H A B ext P → GoodB R H A B ext' P

def goodB_of_det : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (d : Xi × Ei.Str → Wi),
    (∀ a w, A.on a → A.relR a w → w = d a) →
    GoodB R H A B ext P → GoodB R H A B (fun a _ _ => d a) P

def goodB_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B ext P → GoodB R H A.cf B.cf ext P

def goodB_cf_in : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B.cf ext P ↔ GoodB R H A.cf B.cf ext P

def goodB_cf_out : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    (∀ a τ b, A.on a → R.red.out a τ = some b → B.on b) →
    GoodB R H A.cf B ext P → GoodB R H A B ext P

/-- States: a masked block carries the conditions of its joints. -/
def goodM_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (D : MaskData R Wi),
    GoodM R H A B ext P D → GoodM R H A.cf B.cf ext P D

/-- States, under the hypotheses below: the block with the masks as its coins is honest-verifier
zero knowledge in the exact form: for every witness for which the claim holds, at every ρ, at every
budget. -/
def exact_own : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (putW : D.Mk → Wi → Wi)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (m : H.MM D),
    (∀ M w, D.kc (putW M w) = D.put M (D.kc w)) →
    (H.own D.Mk putW).ExactWith (fun x _ w => D.Cl (D.pub x) (D.kc w)) bud (D.simOwn m.noOrc)

/-- States: a masked block does not have the field `exact`, as soon as two witnesses of one
explicit part, each with some oracles that the verifier does not read, make the prover send
different plain parts at some ρ with `bud ρ ∅`. -/
def masked_not_exact : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop),
    H.MM D → (∀ ρ, R.extReads ρ = ∅) →
    ∀ x y y' w w' ρ, Ri x y w → Ri x y' w' → bud ρ ∅ →
      D.msg (D.kc w) (D.pub x) ρ ≠ D.msg (D.kc w') (D.pub x) ρ → ¬ H.Exact Ri bud

end Spec

open IOR ChainKit

theorem goodT_iff : Spec.goodT_iff := fun _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun g =>
      ⟨⟨g.point, g.isLocal, g.acc, g.onOut, g.keeps, g.prBad, g.cover, g.prCov, g.know⟩, g.exact⟩,
    fun g =>
      ⟨g.1.point, g.1.isLocal, g.1.acc, g.1.onOut, g.1.keeps, g.1.prBad, g.1.cover,
        g.1.prCov, g.1.know, g.2⟩⟩

theorem goodB_seq_ext : Spec.goodB_seq_ext := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ ext P₁ P₂ g₁ g₂ he
  exact
    { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
      isLocal := g₁.isLocal.seq g₂.isLocal
      acc := g₁.acc.seq g₂.acc
      onOut := by
        intro a τ c ha hc
        obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
        exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
      keeps := by
        intro w x c ρ
        rw [Honest.run_seq]
        exact (g₂.keeps _ _ _ _).trans (g₁.keeps _ _ _ _)
      prBad := le_trans (prRho_cyl_union_le H₁.Bad H₂.Bad) (add_le_add g₁.prBad g₂.prBad)
      cover := by
        rintro w x ρ (hρ | ⟨_, c, hc⟩)
        · exact Or.inl (g₁.cover w x hρ)
        · have h := g₂.cover _ _ hc
          rw [g₁.keeps] at h
          exact Or.inr h
      prCov := fun k =>
        le_trans (prRho_cyl_union_le (P₁.cov k) (P₂.cov k)) (add_le_add (g₁.prCov k) (g₂.prCov k))
      know := by
        intro a ha
        refine Doomed.mono _ _ ?_ (Reduction.Know.seq_ext g₁.know g₂.know g₁.onOut ext he a ha)
        intro τ h b w hb hw
        exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw }

theorem goodB_seq : Spec.goodB_seq := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ g₁ g₂
  refine goodB_seq_ext K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂
    (IOR.extSeq R₁ R₂ e₁ e₂ d) P₁ P₂ g₁ g₂ ?_
  intro a τ₁ τ₂ b w hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact IOR.extSeq_app R₁ R₂ e₁ e₂ d a τ₁ τ₂ xo w hx

theorem goodB_conseq : Spec.goodB_conseq := by
  intro K Xi Xo Ei Eo R Wi Wo H A A' B B' ext P P' g hA hB hoA hoB hrA hrB hcA hcB hP
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := fun x y w c ρ hR hρ =>
        ⟨(g.acc x y w c ρ (hA x y w hR) hρ).1, hB _ _ _ (g.acc x y w c ρ (hA x y w hR) hρ).2⟩
      onOut := fun a τ b ha hb => hoB b (g.onOut a τ b (hoA a ha) hb)
      keeps := fun w x c ρ => by rw [hcA, hcB]; exact g.keeps w x c ρ
      prBad := le_trans g.prBad hP.pBad
      cover := fun w x => by rw [hP.cov, hcA]; exact g.cover w x
      prCov := fun k => by rw [hP.cov]; exact le_trans (g.prCov k) hP.pHid
      know := (g.know.conseq hoA hrA hrB).mono_err hP.err }

theorem goodB_ext_congr : Spec.goodB_ext_congr := fun _ _ _ _ _ R _ _ _ A B ext ext' P he g =>
  { g with know := know_ext_congr _ _ _ _ R.red A.on A.relR B.relR ext ext' P.err he g.know }

theorem goodB_of_det : Spec.goodB_of_det := fun _ _ _ _ _ R _ _ _ A B ext P d hd g =>
  { g with know := know_of_det _ _ _ _ R.red A.on A.relR B.relR ext P.err d hd g.know }

theorem goodB_cf_in : Spec.goodB_cf_in := fun _ _ _ _ _ R _ _ _ A B ext P =>
  ⟨fun g =>
      { g with
        onOut := fun _ _ _ _ _ => trivial,
        know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.cf.relR ext P.err).1 g.know },
    fun g =>
      { g with
        onOut := fun _ _ _ _ _ => trivial,
        know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.cf.relR ext P.err).2 g.know }⟩

theorem goodB_cf : Spec.goodB_cf := fun K Xi Xo Ei Eo R Wi Wo H A B ext P g =>
  (goodB_cf_in K Xi Xo Ei Eo R Wi Wo H A B ext P).1
    { g with
      onOut := fun _ _ _ _ _ => trivial,
      know := knowInto_of_carry _ _ _ _ R.red A.on B.on A.relR B.relR ext P.err
          (fun a τ b hb ha => g.onOut a τ b ha hb) g.know }

theorem goodB_cf_out : Spec.goodB_cf_out := fun _ _ _ _ _ R _ _ _ A B ext P ho g =>
  { g with
    onOut := ho, know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.relR ext P.err).2 g.know }

theorem goodM_cf : Spec.goodM_cf := fun K Xi Xo Ei Eo R Wi Wo H A B ext P _ g =>
  ⟨goodB_cf K Xi Xo Ei Eo R Wi Wo H A B ext P g.base, g.mm, g.claim⟩

/-- a run without oracles shows its plain parts -/
theorem IOR.view_eq_bare {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (h : IsEmpty (OPos R.shape)) (T : Finset (OPos R.shape)) (τ : Tr R.shape) :
    R.view T τ = bareView h τ.plains := by
  unfold IOR.view bareView
  congr 1
  funext p
  exact (h.false p).elim

theorem exact_own : Spec.exact_own := by
  intro Xi Xo Ei Eo R Wi Wo H D putW bud m hput x y w hw ρ _ T _
  have hfree : ρ ∉ (H.own D.Mk putW).withheld w x := by
    rintro (hb | ⟨M, hM⟩)
    · have : ρ ∈ H.withheld w x := Or.inl hb
      rw [m.free] at this
      exact this
    · have : ρ ∈ H.withheld (putW M w) x := Or.inr hM
      rw [m.free] at this
      exact this
  unfold IOR.Honest.output
  rw [if_neg hfree]
  have e : (fun c : (H.own D.Mk putW).Coin =>
        some (R.view T (((H.own D.Mk putW).strat w x c).run ρ).1)) =
      (fun pl => some (bareView m.noOrc pl)) ∘ (fun M => D.msg (D.put M (D.kc w)) (D.pub x) ρ) ∘
        (Prod.fst : D.Mk × H.Coin → D.Mk) := by
    funext c
    show some (R.view T ((H.strat (putW c.1 w) x c.2).run ρ).1) =
      some (bareView m.noOrc (D.msg (D.put c.1 (D.kc w)) (D.pub x) ρ))
    rw [IOR.view_eq_bare R m.noOrc, m.run, hput]
  show (unif (D.Mk × H.Coin)).map _ = (D.sim (D.pub x) ρ).map _
  rw [e, ← PMF.map_comp, ← PMF.map_comp, map_fst_unif, m.law _ _ _ hw]

theorem masked_not_exact : Spec.masked_not_exact := by
  intro Xi Xo Ei Eo R Wi Wo H D Ri bud m hr x y y' w w' ρ hw hw' hb hne ⟨S, hS⟩
  have hg : R.given ρ ∅ = ∅ := by
    unfold IOR.given
    rw [hr]
    haveI := m.noOrc
    simp [Finset.eq_empty_of_isEmpty]
  have hans : Ei.ans (R.given ρ ∅) y = Ei.ans (R.given ρ ∅) y' := by
    rw [hg]
    funext p
    simp [ExtSpec.ans]
  have out : ∀ w₀,
      H.output w₀ x ρ ∅ = PMF.pure (some (bareView m.noOrc (D.msg (D.kc w₀) (D.pub x) ρ))) := by
    intro w₀
    unfold IOR.Honest.output
    rw [if_neg (by rw [m.free]; exact fun h => h)]
    have e : (fun c : H.Coin => some (R.view ∅ ((H.strat w₀ x c).run ρ).1)) =
        fun _ => some (bareView m.noOrc (D.msg (D.kc w₀) (D.pub x) ρ)) := by
      funext c
      rw [IOR.view_eq_bare R m.noOrc, m.run]
    rw [e]
    exact PMF.map_const _ _
  have hid : ∀ w₀, ρ ∉ H.Hid w₀ x := fun w₀ h => by
    have : ρ ∈ H.withheld w₀ x := Or.inr h
    rw [m.free] at this
    exact this
  have h1 := hS x y w hw ρ (hid w) ∅ hb
  have h2 := hS x y' w' hw' ρ (hid w') ∅ hb
  rw [out, hans] at h1
  rw [out] at h2
  have h3 := h1.trans h2.symm
  have h4 : some (bareView m.noOrc (D.msg (D.kc w) (D.pub x) ρ)) =
      some (bareView m.noOrc (D.msg (D.kc w') (D.pub x) ρ)) := by
    have : some (bareView m.noOrc (D.msg (D.kc w') (D.pub x) ρ)) ∈
        (PMF.pure (some (bareView m.noOrc (D.msg (D.kc w) (D.pub x) ρ)))).support := by
      rw [h3]
      exact (PMF.mem_support_pure_iff _ _).2 rfl
    exact ((PMF.mem_support_pure_iff _ _).1 this).symm
  exact hne (congrArg View.plains (Option.some.inj h4))

end Iop
