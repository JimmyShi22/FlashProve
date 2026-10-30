-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/LinkOf.lean: the link of a sub-proof as a whole (`sub_link`, Cb/Pv/Att/Link.lean), with
the premises on what stands in front of the first sending replaced by their one consequence.

One statement and its proof. `sub_link` takes the chain's conditions, the lookup's `KnowAt`, the
bound on the ledger and the two premises on the chain's end, and uses of them only `subR_knowAt`:
`KnowAt` of the front block from the joint at the door to `virtJ` (Cb/Sub/LateJoin.lean). Here that
is the premise. So whoever proves it otherwise has the whole.

Main names:
  `sub_link_of`: for any block R₀ that ends at a statement with a ledger beside it: from `KnowAt R₀
    A (virtJ B₀ a msg₁ n) idW ε₀` and the premises of `sub_link` on what follows: `KnowInto` of the
    whole.

Limits: those of Cb/Pv/Att/Link.lean.
-/
import Cb.Pv.Att.Link

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Hiop Cb IOR TWhole Reduction Cb.Sub

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {X₀ Xe : Type}
  {Ex : ExtSpec}

/-- The link of a sub-proof as a whole, from the front block's `KnowAt`. -/
theorem sub_link_of {K Y₂ X₃ Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (Sd₁ : N₁.Seeds)
    (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp)
    (bk₂ : N₂.Msg → Wp₂ → Wp₁) {R₀ : IOR X₀ Ex (Xe × Ledger E (J₁ ⊕ J₂)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (a : Xe → J₂ → Aff E J₁)
    (msg₁ : S₁.Msg → J₁ → E) (ent : N₁.Msg → J₂ → E) (n : ℕ) (B₀ : Rels K Xe Ex (S₁.Msg × Wp))
    (h₀ : KnowAt R₀ A (virtJ B₀ a msg₁ n) idW ε₀)
    {T₁ : IOR (Xe × Ledger E (J₁ ⊕ J₂)) Ex Y₂ Ex} {T₂ : IOR Y₂ Ex X₃ Ex}
    {Rl₁ : Rels K (Xe × Ledger E (J₁ ⊕ J₂)) Ex ((S₁.sum N₁).Msg × Wp₁)}
    {C₁ : Rels K Y₂ Ex ((S₁.sum N₁).Msg × Wp₁)}
    {Rl₂ : Rels K Y₂ Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)}
    {C₂ : Rels K X₃ Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)} {η₁ : Err T₁.shape} {η₂ : Err T₂.shape}
    (hRng : KnowAt T₁ Rl₁ C₁ idW η₁) (hDig : KnowAt T₂ Rl₂ C₂ idW η₂)
    (ho₁ : ∀ b, (virtJ B₀ a msg₁ n).on b → Rl₁.on b)
    (hs₁ : ∀ b m w', Rl₁.relR b (m, w') →
      B₀.relR (b.1.1, b.2) (S₁.left N₁ (T := OMsg.Msg) m, bk₁ (S₁.right N₁ (T := OMsg.Msg) m) w') ∧
        Agree (a b.1.1) (msg₁ (S₁.left N₁ (T := OMsg.Msg) m))
          (ent (S₁.right N₁ (T := OMsg.Msg) m)) ∧
        Ledger.Holds b.1.2 (Sum.elim (msg₁ (S₁.left N₁ (T := OMsg.Msg) m))
          (ent (S₁.right N₁ (T := OMsg.Msg) m))))
    (ho₂ : ∀ b, C₁.on b → Rl₂.on b)
    (hs₂ : ∀ b m w', Rl₂.relR b (m, w') →
      C₁.relR b ((S₁.sum N₁).left N₂ (T := OMsg.Msg) m,
        bk₂ ((S₁.sum N₁).right N₂ (T := OMsg.Msg) m) w'))
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ T₁ T₂).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over C₂).on (S₁.over A).relR (((S₁.sum N₁).sum N₂).over C₂).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ bk₂ R₀ T₁ T₂ d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ T₁ T₂ ε₀ η₁ η₂) :=
  frame2 d d' h₀ hRng hDig ho₁
    (fun b m w' hw => by
      obtain ⟨g1, g2, g3⟩ := hs₁ b m w' hw
      exact ⟨g1, (late_holds (a b.1.1) b.1.2 _ _ g2).1 g3⟩)
    ho₂ hs₂ hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end Cb.Pv.Att
