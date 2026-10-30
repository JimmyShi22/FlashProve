-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesMaskSeq.lean: two masked blocks in a row are a masked block, under the laws
`L.OK H₁`; under the hypotheses of `Spec.mm_public`, a block whose plain parts are public is a
masked block without masks.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean): two
reductions in a row, neither of which sends an oracle.
Definitions, statements and proofs. No protocol, no code occurs here.
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain. A masked block is a block with the item "masked messages" (`Honest.MM`, over parameters
`MaskData`: Ior/Masked.lean). The plain part of a prover message is the part that is not an oracle
(`Round.Plain`, Iop/Shape.lean).

Why: a sub-protocol may be a chain of masked blocks (Ior/Masked.lean) and of blocks without a
prover message, none of which sends an oracle, while all its masks stand in its input: no part of
it sends them. Its zero-knowledge item is then again "masked messages" (for two in a row, under the
laws `L.OK H₁`: `Spec.mm_seq`; a block without prover message: under the hypotheses of
`Spec.mm_silent`), and the rule for prefixes (Ior/KnowCollRulesMask.lean) takes the whole
sub-protocol as one masked block.

Main names:
  `MaskLink D₁ D₂`: how the first block hands on to the second, in closed form. The reading `D₁.Kc`
    of the first block is taken so wide that it also holds what the second will read.
      `nk k xp ρ`: what the second block reads of the witness that the first hands on.
      `np xp pl ρ`: the public part of the explicit part that the first hands on: a function of the
        first's public part, its plain parts pl and its verifier messages.
      `put₂ M k`: the second block's own masks, overwritten where they stand in the first block's
        reading. (The reading meant; of the laws of `MaskLink.OK` only `blind`, `pass` and `stable`
        name `put₂`.)
  `L.OK H₁`: the laws: the two closed forms are right; the first block's messages and claim do not
    read the second's masks (exactly: `blind`:
    `∀ M k xp ρ, D₁.msg (L.put₂ M k) xp ρ = D₁.msg k xp ρ`; `stable`:
    `∀ xp k M, D₁.Cl xp k → D₁.Cl xp (L.put₂ M k)`); these masks are handed on as they are (nk
    commutes with the overwriting); the first's claim gives the second's claim, at the public part
    that the first's messages fix.
  `D₁.seq D₂ L`: the parameters of the whole: reading, public part and claim of the first; own
    masks: the pair; plain parts: the first's, then the second's; the simulator: the first's, then
    the second's at the public part that the first's output fixes.
  `Spec.mm_seq`: `H₁.MM D₁`, `H₂.MM D₂`, `L.OK H₁` give `(H₁.seq H₂).MM (D₁.seq D₂ L)`.
  `Spec.goodM_seq`: the same for the bundles: `GoodM`, then `GoodM`, is `GoodM`, again under
    `L.OK H₁`.
  `MaskData.pubMsg`, `Spec.mm_public`: a block without oracles that withholds nothing and whose
    plain parts are a function f of the public part and the verifier's messages: the item holds
    with no masks (Mk = Unit) and the simulator f.
  `Spec.mm_silent`: in particular a block without prover message (its plain parts have one value).

Why (the proof of `mm_seq`): the order of the two averages matters. The second block's claim may
read the first block's masks (what the first leaves open holds them). So the second's masks are
averaged first, for every fixing of the first's; beyond `L.OK H₁` nothing is asked about how nk
depends on the first's masks.

Limits: this file says nothing on blocks that send oracles. It says nothing on running times.
The statement was asked for on a reading of this protocol's technical report (lean/CREDITS.md),
which gives such a sub-protocol this item.
Terms: lean/GLOSSARY.md.
-/
import Ior.Masked
import Ior.ExactSeq
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo : ExtSpec} {W₁ W₂ W₃ Wi Wo : Type}

/-- How a masked block hands on to the next, in closed form. -/
structure MaskLink {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    (D₁ : MaskData R₁ W₁) (D₂ : MaskData R₂ W₂) where
  nk   : D₁.Kc → D₁.Xp → Rho R₁.shape → D₂.Kc
  np   : D₁.Xp → Plains R₁.shape → Rho R₁.shape → D₂.Xp
  put₂ : D₂.Mk → D₁.Kc → D₁.Kc

/-- Its laws. -/
structure MaskLink.OK {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {D₁ : MaskData R₁ W₁}
    {D₂ : MaskData R₂ W₂} (L : MaskLink D₁ D₂) (H₁ : R₁.Honest W₁ W₂) : Prop where
  handK  : ∀ w x c ρ, D₂.kc ((H₁.strat w x c).run ρ).2.2 = L.nk (D₁.kc w) (D₁.pub x) ρ
  handP  : ∀ w x c ρ,
    D₂.pub ((H₁.strat w x c).run ρ).2.1 = L.np (D₁.pub x) (D₁.msg (D₁.kc w) (D₁.pub x) ρ) ρ
  blind  : ∀ M k xp ρ, D₁.msg (L.put₂ M k) xp ρ = D₁.msg k xp ρ
  pass   : ∀ M k xp ρ, L.nk (L.put₂ M k) xp ρ = D₂.put M (L.nk k xp ρ)
  stable : ∀ xp k M, D₁.Cl xp k → D₁.Cl xp (L.put₂ M k)
  claim  : ∀ k xp ρ, D₁.Cl xp k → D₂.Cl (L.np xp (D₁.msg k xp ρ) ρ) (L.nk k xp ρ)

/-- The parameters of two masked blocks in a row. -/
def MaskData.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} (D₁ : MaskData R₁ W₁)
    (D₂ : MaskData R₂ W₂) (L : MaskLink D₁ D₂) : MaskData (R₁.seq R₂) W₁ where
  Kc  := D₁.Kc
  kc  := D₁.kc
  Xp  := D₁.Xp
  pub := D₁.pub
  Mk  := D₁.Mk × D₂.Mk
  put := fun M k => L.put₂ M.2 (D₁.put M.1 k)
  Cl  := D₁.Cl
  msg := fun k xp ρ =>
    Plains.app (D₁.msg k xp (Rho.fst ρ))
      (D₂.msg (L.nk k xp (Rho.fst ρ))
        (L.np xp (D₁.msg k xp (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ))
  sim := fun xp ρ =>
    (D₁.sim xp (Rho.fst ρ)).bind fun p₁ =>
      (D₂.sim (L.np xp p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)

/-- The parameters of a block whose plain parts are public: no masks. -/
def MaskData.pubMsg (R : IOR Xi Ei Xo Eo) {Kc Xp : Type} (kc : Wi → Kc)
    (pub : Xi → Xp) (Cl : Xp → Kc → Prop) (f : Xp → Rho R.shape → Plains R.shape) :
    MaskData R Wi where
  Kc  := Kc
  kc  := kc
  Xp  := Xp
  pub := pub
  Mk  := Unit
  put := fun _ k => k
  Cl  := Cl
  msg := fun _ xp ρ => f xp ρ
  sim := fun xp ρ => PMF.pure (f xp ρ)

end IOR

namespace Spec
open IOR

/-- States, under `L.OK H₁`: two masked blocks in a row are a masked block. -/
def mm_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (D₁ : MaskData R₁ W₁)
      (D₂ : MaskData R₂ W₂) (L : MaskLink D₁ D₂),
    H₁.MM D₁ → H₂.MM D₂ → L.OK H₁ → (H₁.seq H₂).MM (D₁.seq D₂ L)

def goodM_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (D₁ : MaskData R₁ W₁) (D₂ : MaskData R₂ W₂) (L : MaskLink D₁ D₂),
    GoodM R₁ H₁ A B e₁ P₁ D₁ → GoodM R₂ H₂ B C e₂ P₂ D₂ → L.OK H₁ →
    GoodM (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) (D₁.seq D₂ L)

/-- States, under the hypotheses below: a block whose plain parts are public is a masked block
without masks. -/
def mm_public : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Kc Xp : Type) (kc : Wi → Kc) (pub : Xi → Xp) (Cl : Xp → Kc → Prop)
      (f : Xp → Rho R.shape → Plains R.shape),
    IsEmpty (OPos R.shape) → (∀ w x, H.withheld w x = ∅) →
    (∀ w x c ρ, ((H.strat w x c).run ρ).1.plains = f (pub x) ρ) →
    H.MM (MaskData.pubMsg R kc pub Cl f)

/-- In particular a block without prover message. (not all hypotheses are named here: see the
statement below) -/
def mm_silent : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Kc Xp : Type) (kc : Wi → Kc) (pub : Xi → Xp) (Cl : Xp → Kc → Prop) (p₀ : Plains R.shape),
    IsEmpty (OPos R.shape) → Subsingleton (Plains R.shape) → (∀ w x, H.withheld w x = ∅) →
    H.MM (MaskData.pubMsg R kc pub Cl fun _ _ => p₀)

end Spec

open IOR

theorem mm_seq : Spec.mm_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ D₁ D₂ L m₁ m₂ hL
  refine ⟨⟨fun p => ?_⟩, fun w x => ?_, fun w x c ρ => ?_,
    fun xp k M h => hL.stable xp _ M.2 (m₁.stable xp k M.1 h), fun k xp ρ h => ?_⟩
  · rcases left_or_right (s := R₁.shape) (t := R₂.shape) p with ⟨q, -⟩ | ⟨q, -⟩
    · exact m₁.noOrc.false q
    · exact m₂.noOrc.false q
  · refine Set.eq_empty_iff_forall_notMem.2 fun ρ =>
      (Honest.not_mem_withheld_seq H₁ H₂ w x ρ).2 ⟨?_, fun c => ?_⟩
    · rw [m₁.free]
      exact fun h => h
    · rw [m₂.free]
      exact fun h => h
  · rw [Honest.run_seq]
    show (Tr.app _ _).plains = Plains.app _ _
    rw [Tr.plains_app, m₁.run, m₂.run, hL.handK, hL.handP]
    rfl
  · show (unif (D₁.Mk × D₂.Mk)).map (fun M =>
        Plains.app (D₁.msg (L.put₂ M.2 (D₁.put M.1 k)) xp (Rho.fst ρ))
          (D₂.msg (L.nk (L.put₂ M.2 (D₁.put M.1 k)) xp (Rho.fst ρ))
            (L.np xp (D₁.msg (L.put₂ M.2 (D₁.put M.1 k)) xp (Rho.fst ρ)) (Rho.fst ρ))
            (Rho.snd (s := R₁.shape) ρ))) =
      (D₁.sim xp (Rho.fst ρ)).bind fun p₁ =>
        (D₂.sim (L.np xp p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)
    rw [← m₁.law k xp (Rho.fst ρ) h]
    refine map_unif_bind_factor _ (fun M₁ => D₁.msg (D₁.put M₁ k) xp (Rho.fst ρ)) _ fun M₁ => ?_
    rw [← m₂.law _ _ _ (hL.claim (D₁.put M₁ k) xp (Rho.fst ρ) (m₁.stable xp k M₁ h)), PMF.map_comp]
    refine congrArg (fun f => PMF.map f (unif D₂.Mk)) (funext fun M₂ => ?_)
    show Plains.app (D₁.msg (L.put₂ M₂ (D₁.put M₁ k)) xp (Rho.fst ρ)) _ =
      Plains.app (D₁.msg (D₁.put M₁ k) xp (Rho.fst ρ)) _
    rw [hL.blind, hL.pass]

theorem goodM_seq :
    Spec.goodM_seq := fun K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ D₁ D₂ L g₁ g₂ hL =>
  ⟨goodB_seq K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ g₁.base g₂.base,
    mm_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ D₁ D₂ L g₁.mm g₂.mm hL,
    g₁.claim⟩

theorem mm_public : Spec.mm_public := fun _ _ _ _ _ _ _ _ _ _ _ _ _ f h0 hf hr =>
  ⟨h0, hf, hr, fun _ _ _ h => h, fun _ xp ρ _ => PMF.map_const (unif Unit) (f xp ρ)⟩

theorem mm_silent : Spec.mm_silent := fun Xi Xo Ei Eo R Wi Wo H Kc Xp kc pub Cl p₀ h0 hs hf =>
  mm_public Xi Xo Ei Eo R Wi Wo H Kc Xp kc pub Cl (fun _ _ => p₀) h0 hf fun _ _ _ _ => hs.elim _ _

end Iop
