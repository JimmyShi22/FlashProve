-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskChain.lean: under `Blind` and `Step`, a chain of masked blocks over one tuple of
entries, of any length, is a masked block.
This file is about the sequential composition of interactive oracle reductions that send no oracle.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskChainProofs.lean. No
protocol of its own, no code occurs here.
A claim is a predicate on an explicit part and the entries.

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the field `mm` of
`MJ.Fits`: `Fits` is a premise and the conclusion of `Spec.mj_seq` and `Spec.mj_chain`, and the
conclusion of `Spec.mj_draw`; `GoodM` stands in no statement of this file. (In the first two
sentences `D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; below `D` is an `MJ`
record, and `Fits` has `D.data rdi` for that `D`.)

Why: a sub-protocol like the lookup is a long chain of sumchecks whose masks were sent in advance
and of steps in which only the verifier speaks. None of them sends an oracle; the witness is handed
on unchanged; all read the same entries m : J → E of the messages; the kind of the explicit part
changes from joint to joint.
Its zero-knowledge item is "masked messages" (Ior/Masked.lean) for the whole. The rule for two
blocks is `mm_seq` (Ior/KnowCollRulesMaskSeq.lean). Here it is put in a form that iterates.

Main names:
  `MJ E J R`: the record of the item for a block R of this kind: own masks `Mk` with `put` (how they
    are written into the entries), the claim `Cl`, the honest plain parts `msg` in closed form, the
    simulator `sim`, and `nxt`: the explicit part that is handed on, as a function of the explicit
    part, the plain parts and the verifier's messages: so it is public.
  `D.data rd`: the record of Ior/Masked.lean (`MaskData`): what is read of a witness is
    `rd w : J → E`; the public part is the whole explicit part.
  `D.Fits H rdi rdo`: H has the item with this record; the entries are handed on unchanged; the
    honest prover ends with `nxt`.
  `D₁.Blind D₂`: the earlier block does not look at the later block's masks: neither its messages
    nor its claim (exactly: `msg : ∀ M k x ρ, D₁.msg (D₂.put M k) x ρ = D₁.msg k x ρ`;
    `cl : ∀ x k M, D₁.Cl x k → D₁.Cl x (D₂.put M k)`).
  `D₁.Step D₂`: the earlier block's claim gives the later block's claim, at the explicit part that
    the earlier block's messages fix.
  `D₁.seq D₂`: two in a row: own masks: the pair; the simulator: the first's, then the second's at
    what the first's output fixes.
  `Spec.mj_seq`: `Fits`, `Fits`, `Blind`, `Step` give `Fits` of the two in a row.
  `Spec.mj_blind_seq`, `mj_step_seq`: how `Blind` and `Step` of a composition follow from those of
    the parts.
  `Spec.mj_chain`: if every block `Fits`, every earlier block is `Blind` to every later one, and
    each Steps to the next, the whole chain `Fits`: so it has the item "masked messages".
  `MJ.silent`, `Spec.mj_draw`: a step in which the verifier draws a value (Ior/Draw.lean): no masks;
    it `Fits`.

Limits: the order matters, as in the rule for two: a later claim may read an earlier block's masks
(what a sumcheck leaves open holds its inner masks); nothing is asked in that direction.
This file does not say that the masks are uniform and unseen when the chain starts: that is the
matter of the block that sends them. It says nothing on blocks that send oracles.

Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMaskSeq
import Ior.MaskedDraw
import Cb.Ld.LdLkpTreeP
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Prob

/-- The record of the item for a block over entries that stay. -/
structure MJ (E J : Type) {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) where
  Mk  : Type
  [finMk : Fintype Mk]
  [neMk  : Nonempty Mk]
  put : Mk → (J → E) → J → E
  Cl  : Xi → (J → E) → Prop
  msg : (J → E) → Xi → Rho R.shape → Plains R.shape
  /-- The explicit part that is handed on: public. -/
  nxt : Xi → Plains R.shape → Rho R.shape → Xo
  sim : Xi → Rho R.shape → PMF (Plains R.shape)

attribute [instance] MJ.finMk MJ.neMk

namespace MJ
variable {E J : Type} {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo : ExtSpec} {W₁ W₂ W₃ Wi Wo : Type}

/-- The record of Ior/Masked.lean (`MaskData`). -/
@[reducible] def data {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (rd : Wi → J → E) : MaskData R Wi :=
  { Kc := J → E, kc := rd, Xp := Xi, pub := fun x => x, Mk := D.Mk, put := D.put, Cl := D.Cl,
    msg := D.msg, sim := D.sim }

/-- The honest side has the item with this record, keeps the entries, and ends with `nxt`. -/
structure Fits {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (H : R.Honest Wi Wo)
    (rdi : Wi → J → E) (rdo : Wo → J → E) : Prop where
  mm   : H.MM (D.data rdi)
  same : ∀ w x c ρ, rdo ((H.strat w x c).run ρ).2.2 = rdi w
  hand : ∀ w x c ρ, ((H.strat w x c).run ρ).2.1 = D.nxt x (D.msg (rdi w) x ρ) ρ

/-- The earlier block does not look at the later block's masks. Exactly: the two fields below. -/
structure Blind {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR Xi Ei Xo Eo} (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) :
    Prop where
  msg : ∀ M k x ρ, D₁.msg (D₂.put M k) x ρ = D₁.msg k x ρ
  cl  : ∀ x k M, D₁.Cl x k → D₁.Cl x (D₂.put M k)

/-- The earlier claim gives the later claim. -/
def Step {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) : Prop :=
  ∀ k x ρ, D₁.Cl x k → D₂.Cl (D₁.nxt x (D₁.msg k x ρ) ρ) k

/-- Two in a row. -/
def seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) : MJ E J (R₁.seq R₂) where
  Mk  := D₁.Mk × D₂.Mk
  put := fun M k => D₂.put M.2 (D₁.put M.1 k)
  Cl  := D₁.Cl
  msg := fun k x ρ =>
    Plains.app (D₁.msg k x (Rho.fst ρ))
      (D₂.msg k (D₁.nxt x (D₁.msg k x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ))
  nxt := fun x pl ρ =>
    D₂.nxt (D₁.nxt x (Plains.fst pl) (Rho.fst ρ))
      (Plains.snd (s := R₁.shape) pl) (Rho.snd (s := R₁.shape) ρ)
  sim := fun x ρ =>
    (D₁.sim x (Rho.fst ρ)).bind fun p₁ =>
      (D₂.sim (D₁.nxt x p₁ (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)).map (Plains.app p₁)

/-- How the first hands on to the second, in the record of the rule for two (`MaskLink`). -/
def link {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} (D₁ : MJ E J R₁) (D₂ : MJ E J R₂)
    (rd₁ : W₁ → J → E) (rd₂ : W₂ → J → E) :
    MaskLink (D₁.data rd₁) (D₂.data rd₂) :=
  ⟨fun k _ _ => k, D₁.nxt, D₂.put⟩

/-- A step in which only the verifier speaks: no masks. -/
def silent {X X' : Type} (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
    (Ex : ExtSpec) (Cl : X → (J → E) → Prop) : MJ E J (IOR.draw Dd nx Ex) where
  Mk  := Unit
  put := fun _ k => k
  Cl  := Cl
  msg := fun _ _ _ => ((), ())
  nxt := fun x _ ρ => nx x ρ.1
  sim := fun _ _ => PMF.pure ((), ())

end MJ

/-- The record of the blocks b 0, .., b n in a row (`BkA.chain`, Cb/Ld/LdLkpTreeP.lean). -/
def MJ.chain {E J K M : Type} {Ex : ExtSpec} {Wp : Type} (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R) :
    ∀ n, MJ E J (BkA.chain X b n).R
  | 0 => D 0
  | n + 1 => (MJ.chain X b D n).seq (D (n + 1))

namespace Spec

/-- Two masked blocks over the same entries, in a row. -/
def mj_seq : Prop :=
  ∀ (E J X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (D₁ : MJ E J R₁)
      (D₂ : MJ E J R₂) (rd₁ : W₁ → J → E) (rd₂ : W₂ → J → E) (rd₃ : W₃ → J → E),
    D₁.Fits H₁ rd₁ rd₂ → D₂.Fits H₂ rd₂ rd₃ → D₁.Blind D₂ →
    D₁.Step D₂ → (D₁.seq D₂).Fits (H₁.seq H₂) rd₁ rd₃

/-- A composition is blind to a later block if both parts are. -/
def mj_blind_seq : Prop :=
  ∀ (E J X₁ X₂ X₃ Xi Xo : Type) (E₁ E₂ E₃ Ei Eo : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (R₃ : IOR Xi Ei Xo Eo) (D₁ : MJ E J R₁)
      (D₂ : MJ E J R₂) (D₃ : MJ E J R₃),
    D₁.Blind D₃ → D₂.Blind D₃ → (D₁.seq D₂).Blind D₃

/-- A composition steps to a later block if the first steps to the second and the
second to the later one. -/
def mj_step_seq : Prop :=
  ∀ (E J X₁ X₂ X₃ X₄ : Type) (E₁ E₂ E₃ E₄ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (R₃ : IOR X₃ E₃ X₄ E₄) (D₁ : MJ E J R₁) (D₂ : MJ E J R₂) (D₃ : MJ E J R₃),
    D₁.Step D₂ → D₂.Step D₃ → (D₁.seq D₂).Step D₃

/-- A chain of any length. -/
def mj_chain : Prop :=
  ∀ (E J K M : Type) (Ex : ExtSpec) (Wp : Type) (X : ℕ → Type)
      (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R)
      (rd : M × Wp → J → E) (n : ℕ),
    (∀ l ≤ n, (D l).Fits (b l).H rd rd) → (∀ l l', l < l' → l' ≤ n → (D l).Blind (D l')) →
    (∀ l < n, (D l).Step (D (l + 1))) → (MJ.chain X b D n).Fits (BkA.chain X b n).H rd rd

/-- What the whole chain's claim is: the first block's. -/
def mj_chain_cl : Prop :=
  ∀ (E J K M : Type) (Ex : ExtSpec) (Wp : Type) (X : ℕ → Type)
      (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R) (n : ℕ),
    (MJ.chain X b D n).Cl = (D 0).Cl

/-- A draw fits, whatever the claim. -/
def mj_draw : Prop :=
  ∀ (E J X X' : Type) (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X') (Ex : ExtSpec)
      (W : Type) (Cl : X → (J → E) → Prop) (rd : W → J → E),
    (MJ.silent Dd nx Ex Cl).Fits (Honest.draw Dd nx Ex W) rd rd

end Spec
end Cb
