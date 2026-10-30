-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FreshJoin.lean: masks of one block that were sent at different steps: a prefix that is Fresh
for two sets of masks at one reading is Fresh for the pair (not all hypotheses are named here: see
`Spec.fresh_join`).

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean): a rule
that joins two instances of one property of an honest prover.
Statements (`Iop.Spec.fresh_join`, `Iop.Spec.fresh_join_seq`); the proofs are in
Ior/FreshJoinProofs.lean. No protocol, no code occurs here.
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain. Prefix, link: see the head of Ior/KnowCollRulesMask.lean.
It uses Ior/KnowCollRulesMask.lean:
  `H.Fresh Ri bud kc Mk put`: given all that the prefix H shows, the masks Mk are still uniform,
    and independent of the rest of what kc reads of the witness handed on. Exactly, of `H.Fresh`,
    for a non-empty `Mk`: on every triple of Ri, at every ρ that is not withheld, for every set T
    of further positions within the budget, the triple (what the run shows at T, the explicit part
    handed on, kc of the witness handed on) has the same law, over the prefix's coins, as the
    triple in which the own mask entries are overwritten by fresh uniform ones (`Honest.Fresh`,
    Ior/KnowCollRulesMask.lean).
  `H.Blind`: a link that does not look.
  `Spec.fresh_snd`, `Spec.fresh_seq` (their theorems are used in Ior/FreshJoinProofs.lean).
`H.Acc Ri Ro` (Ior/Honest.lean): pointwise completeness from the relation Ri to the relation Ro.
Reading: the argument `kc` of `H.Fresh`: see its row in the head of Ior/KnowCollRulesMask.lean.

Why: a masked block may have own masks in several oracle messages that were sent at different steps
(say: hiding coefficients in a message sent just before the block's segment, inner masks in a
message sent with the first prover message). The rules so far (`fresh_snd`, `fresh_seq`) make a
fact "fresh" at the one link that sends the masks and carry it through links that do not look. A
link is not Fresh for masks that stand in its input; so no link is Fresh for such a block's masks
as a whole, and the block's fact could not be had [no theorem here; not so at an overwriting that
does nothing: `fresh_idle`, Ior/MaskControls.lean].

Main names:
  `Spec.fresh_join`: one prefix H, one relation Ri, one budget bud, one reading kc, non-empty M₁
    and M₂. H is Fresh for (M₁, put₁) and Fresh for (M₂, put₂) ⇒ H is Fresh for the pair (M₁ × M₂,
    first put₂, then put₁).
    Nothing is asked of the two overwritings (not that they commute, not that their places differ).
    Why: "Fresh" says that overwriting by fresh uniform masks does not change the law of (what is
    shown, explicit part, reading); overwrite by M₂: the law is the old one; overwrite that by M₁:
    again.
    What a user must still see: that the masked block's own overwriting of the pair is "put₁ after
    put₂" (at different places the order does not matter).
    What makes the hypotheses strong enough: the reading is one. Fresh for M₁ at kc says that M₁ is
    independent of all that kc reads beside it: M₂'s entries among it; and the other way round.
    With two different readings nothing follows (`fresh1`, `fresh2`, `pair_not_fresh`,
    Ior/MaskControls.lean).
  `Spec.fresh_join_seq`, under the hypotheses of its statement (`H₁.Acc Ra Rb` among them): a
    prefix H₁ that is Fresh for M₁; then a link H₂ that does not look at M₁ and is Fresh for M₂,
    both at the reading kc₃ of what it hands on ⇒ the whole is Fresh for the pair at kc₃.

Limits: this file says nothing on chains as lists of links (Cb/Req1/LdSegFreshS.lean). It says
nothing on batches.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMask

set_option autoImplicit false

namespace Iop
namespace Spec
open IOR Prob

/-- States, under the hypotheses below: a prefix that is Fresh for two sets of masks at one reading
is Fresh for the pair. -/
def fresh_join : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (Kc : Type)
      (kc : Wo → Kc) (M₁ M₂ : Type) [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂]
      (put₁ : M₁ → Kc → Kc) (put₂ : M₂ → Kc → Kc),
    H.Fresh Ri bud kc M₁ put₁ → H.Fresh Ri bud kc M₂ put₂ →
    H.Fresh Ri bud kc (M₁ × M₂) fun M k => put₁ M.1 (put₂ M.2 k)

/-- Masks sent earlier, and masks that the last link sends. -/
def fresh_join_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (Rb : X₂ → E₂.Str → W₂ → Prop) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (K₂ K₃ : Type) (kc₂ : W₂ → K₂)
      (kc₃ : W₃ → K₃) (M₁ M₂ : Type) [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂]
      (put₁' : M₁ → K₂ → K₂) (put₁ : M₁ → K₃ → K₃) (put₂ : M₂ → K₃ → K₃),
    H₁.Acc Ra Rb → H₁.Fresh Ra b₁ kc₂ M₁ put₁' → H₂.Blind kc₂ kc₃ M₁ put₁' put₁ →
    H₂.Fresh Rb b₂ kc₃ M₂ put₂ →
    (H₁.seq H₂).Fresh Ra (budSeq R₁ R₂ b₁ b₂) kc₃ (M₁ × M₂) fun M k => put₁ M.1 (put₂ M.2 k)

end Spec
end Iop
