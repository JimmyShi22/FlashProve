-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/SumOrder.lean: a chain with messages that are sent in its middle, in the true order, AT ONE
SIGNATURE: the form in which the library's own blocks can follow.

Definitions, statements and their proofs.
Cb/Sub/TrueOrder.lean ends a chain at a nested joint (`N.over (over2 S₁ C)`), at which no block of
the library starts. The library's own sending in the middle of a chain is `ldSendSig S N Sd`
(Cb/Ld/LdSigSum.lean): the sending of the family N, then a renaming without rounds, to the ONE
signature `S.sum N`. Here the same chains are laid with it. A block behind the sending has
`TWhole.KnowAt` at the tuples of `S.sum N`, and is passed to oracle messages by one call of
`sigLift_know`. The chain ends at `(S.sum N).over C`: a joint of the library's kind.

Main names:
  `sendSig_into`: `ldSendSig`'s knowledge soundness alone: from `S.over A` into
    `(S.sum N).over (S.grow N A bk)`, with the sending's error; no honest side is asked. From
    `ldSendFam_into` (Cb/Ld/LdSendFam.lean) and the renaming's clause `know` (`sigSum_step`).
  `sum_step`: ONE SENDING IN THE MIDDLE: whatever stands in front (K₀, ending at `S.over A₂`), the
    sending, a block T with `KnowAt` at the tuples of `S.sum N`. The seam: what T starts from, at
    (m, w'), gives A₂ at (the old messages of m, `bk` (the new messages of m) w'). ITS CONCLUSION
    HAS THE FORM OF ITS FIRST PREMISE, at the signature `S.sum N`: so it is used again as it stands.
  `sum_order`: R over S₁, the sending of N, T over `S₁.sum N`.
  `realS`, `late_sum_order`: the same for a ledger on early and late entries
    (Cb/Sub/LateJoin.lean's `virtJ`, `realJ`).

Limits: those of Cb/Sub/TrueOrder.lean, but (vii). On `bk`: the head of Cb/Sub/SendBack.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.TrueOrder
import Cb.Ld.LdSigSumProofs

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR Reduction

variable {E : Type} [Field E]

/-- The library's sending to one signature: knowledge soundness alone. -/
theorem sendSig_into {K St Wp Wp' : Type} {E₀ : ExtSpec} (S N : Sig E) (Sd : N.Seeds)
    (A : Rels K St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp) (Ln : N.O → ℕ) (hF : Sd.Fair)
    (hL : ∀ a, (N.om a).ListLE (Ln a)) (hE : ∀ a, (N.om a).Evades) :
    (ldSendSig S N Sd St E₀).red.KnowInto (S.over A).on ((S.sum N).over (S.grow N A bk)).on
      (S.over A).relR ((S.sum N).over (S.grow N A bk)).relR
      (fun _ _ w =>
        (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
      (ldSendFamErr N Sd Ln, (0, ())) := by
  intro a ha
  refine Doomed.mono _ _ ?_
    (ldSendFam_into E N Sd K (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext) (S.over A)
      (S.backN N bk) Ln hF hL hE a ha)
  intro τ hτ b' w' hb' hw'
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb'
  have h1' : ((ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).out a.1 a.2 τ).bind (S.mergeX N St) =
      some b'.1 := h1
  obtain ⟨x, hx, hf⟩ := Option.bind_eq_some_iff.1 h1'
  have hb : (ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).red.out a τ =
      some (x, (ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).imp a.2 τ) :=
    red_out_eq_some.2 ⟨hx, rfl⟩
  have e : b' = (b'.1,
      (S.mergeE N E₀).map ((ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).imp a.2 τ)) :=
    Prod.ext rfl h2
  have hw : ((S.sum N).over (S.grow N A bk)).cf.relR (b'.1,
      (S.mergeE N E₀).map ((ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).imp a.2 τ)) w' := by
    rw [← e]
    exact hw'
  exact hτ _ (S.splitW N Wp' w') hb
    ((sigSum_step E S N K St Wp Wp' E₀ A bk).know x _ b'.1 w' trivial hf hw)

/-- ONE SENDING IN THE MIDDLE OF A CHAIN, AT ONE SIGNATURE. -/
theorem sum_step {K P WP Y X₂ Wp Wp' : Type} {E₂ E₃ : ExtSpec} (S N : Sig E) (Sd : N.Seeds)
    (Ln : N.O → ℕ) (bk : N.Msg → Wp' → Wp) {K₀ : Reduction P ((Y × S.Smp) × (E₂.prod S.ext).Str)}
    {onP : P → Prop} {RP : P → WP → Prop} {e₀ : P → Tr K₀.shape → S.Wit × Wp → WP}
    {ε₀ : Err K₀.shape} {A₂ : Rels K Y E₂ (S.Msg × Wp)} {T : IOR Y E₂ X₂ E₃}
    {Rl : Rels K Y E₂ ((S.sum N).Msg × Wp')} {C : Rels K X₂ E₃ ((S.sum N).Msg × Wp')}
    {ε₂ : Err T.shape} (dP : WP) (d₂ : S.Wit × Wp)
    (k₀ : K₀.KnowInto onP (S.over A₂).on RP (S.over A₂).relR e₀ ε₀) (h : KnowAt T Rl C idW ε₂)
    (hon : ∀ b, A₂.on b → Rl.on b)
    (hseam : ∀ b m w', Rl.relR b (m, w') →
      A₂.relR b (S.left N (T := OMsg.Msg) m, bk (S.right N (T := OMsg.Msg) m) w'))
    (hF : Sd.Fair) (hL : ∀ a, (N.om a).ListLE (Ln a)) (hE : ∀ a, (N.om a).Evades) :
    (K₀.seq ((ldSendSig S N Sd Y E₂).red.seq
        (T.keep (S.sum N).Smp (S.sum N).ext).red)).KnowInto
      onP ((S.sum N).over C).on RP ((S.sum N).over C).relR
      (Reduction.extSeq _ _ e₀
        (Reduction.extSeq _ _
          (fun _ _ w =>
            (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
          (fun _ _ w => w) d₂) dP)
      (Err.app ε₀ (Err.app (s := (ldSendSig S N Sd Y E₂).shape) (ldSendFamErr N Sd Ln, (0, ())) ε₂))
    := by
  have k₂ := sendSig_into S N Sd A₂ bk Ln hF hL hE
  have k₃ : (T.keep (S.sum N).Smp (S.sum N).ext).red.KnowInto
      ((S.sum N).over (S.grow N A₂ bk)).on ((S.sum N).over C).on
      ((S.sum N).over (S.grow N A₂ bk)).relR ((S.sum N).over C).relR (fun _ _ w => w) ε₂ :=
    Know.conseq (lift_into (S.sum N) h) (fun _ ha => ⟨ha.1, hon _ ha.2⟩)
      (fun _ _ _ hw => ⟨hw.1, hseam _ _ _ hw.2⟩) fun _ _ h => h
  exact knowInto_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dP k₀
    (knowInto_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d₂ k₂ k₃)

/-- R over the early signature, the sending, T over both as one. -/
theorem sum_order {K X Y X₂ Wp Wp' : Type} {E₁ E₂ E₃ : ExtSpec} (S₁ N : Sig E) (Sd : N.Seeds)
    (Ln : N.O → ℕ) (bk : N.Msg → Wp' → Wp) {R : IOR X E₁ Y E₂} {T : IOR Y E₂ X₂ E₃}
    {A : Rels K X E₁ (S₁.Msg × Wp)} {V : Rels K Y E₂ (S₁.Msg × Wp)}
    {Rl : Rels K Y E₂ ((S₁.sum N).Msg × Wp')} {C : Rels K X₂ E₃ ((S₁.sum N).Msg × Wp')}
    {ε₁ : Err R.shape} {ε₂ : Err T.shape} (d : S₁.Wit × Wp) (h₁ : KnowAt R A V idW ε₁)
    (h₂ : KnowAt T Rl C idW ε₂) (hon : ∀ b, V.on b → Rl.on b)
    (hseam : ∀ b m w', Rl.relR b (m, w') →
      V.relR b (S₁.left N (T := OMsg.Msg) m, bk (S₁.right N (T := OMsg.Msg) m) w'))
    (hF : Sd.Fair) (hL : ∀ a, (N.om a).ListLE (Ln a)) (hE : ∀ a, (N.om a).Evades) :
    ((R.keep S₁.Smp S₁.ext).red.seq ((ldSendSig S₁ N Sd Y E₂).red.seq
        (T.keep (S₁.sum N).Smp (S₁.sum N).ext).red)).KnowInto
      (S₁.over A).on ((S₁.sum N).over C).on (S₁.over A).relR ((S₁.sum N).over C).relR
      (Reduction.extSeq _ _ (fun _ _ w => w)
        (Reduction.extSeq _ _
          (fun _ _ w =>
            (S₁.left N (T := OMsg.Wit) w.1, bk (N.msgs (S₁.right N (T := OMsg.Wit) w.1)) w.2))
          (fun _ _ w => w) d) d)
      (Err.app ε₁
        (Err.app (s := (ldSendSig S₁ N Sd Y E₂).shape) (ldSendFamErr N Sd Ln, (0, ())) ε₂)) :=
  sum_step S₁ N Sd Ln bk d d (lift_into S₁ h₁) h₂ hon hseam hF hL hE

section Late
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

/-- `realJ` (Cb/Sub/LateJoin.lean) at the tuples of the one signature. -/
def realS {K X Wp : Type} {Ex : ExtSpec} (S₁ N : Sig E) (B₀ : Rels K X Ex (S₁.Msg × Wp))
    (a : X → J₂ → Aff E J₁) (msg₁ : S₁.Msg → J₁ → E) (ent : N.Msg → J₂ → E) (n : ℕ) :
    Rels K (X × Ledger E (J₁ ⊕ J₂)) Ex ((S₁.sum N).Msg × Wp) :=
  comapM (fun m => (S₁.left N (T := OMsg.Msg) m, S₁.right N (T := OMsg.Msg) m))
    (realJ B₀ a msg₁ ent n)

/-- The same for a ledger on early and late entries. -/
theorem late_sum_order {K X X' X₂ Wp : Type} {E₁ E₂ E₃ : ExtSpec} (S₁ N : Sig E) (Sd : N.Seeds)
    (Ln : N.O → ℕ) {R : IOR X E₁ (X' × Ledger E (J₁ ⊕ J₂)) E₂}
    {T : IOR (X' × Ledger E (J₁ ⊕ J₂)) E₂ X₂ E₃} {A : Rels K X E₁ (S₁.Msg × Wp)}
    {B₀ : Rels K X' E₂ (S₁.Msg × Wp)} {C : Rels K X₂ E₃ ((S₁.sum N).Msg × Wp)} {ε₁ : Err R.shape}
    {ε₂ : Err T.shape} (d : S₁.Wit × Wp) (a : X' → J₂ → Aff E J₁) (msg₁ : S₁.Msg → J₁ → E)
    (ent : N.Msg → J₂ → E) (n : ℕ) (h₁ : KnowAt R A (virtJ B₀ a msg₁ n) idW ε₁)
    (h₂ : KnowAt T (realS S₁ N B₀ a msg₁ ent n) C idW ε₂) (hF : Sd.Fair)
    (hL : ∀ i, (N.om i).ListLE (Ln i)) (hE : ∀ i, (N.om i).Evades) :
    ((R.keep S₁.Smp S₁.ext).red.seq
        ((ldSendSig S₁ N Sd (X' × Ledger E (J₁ ⊕ J₂)) E₂).red.seq
          (T.keep (S₁.sum N).Smp (S₁.sum N).ext).red)).KnowInto
      (S₁.over A).on ((S₁.sum N).over C).on (S₁.over A).relR ((S₁.sum N).over C).relR
      (Reduction.extSeq _ _ (fun _ _ w => w)
        (Reduction.extSeq _ _ (fun _ _ w => (S₁.left N (T := OMsg.Wit) w.1, w.2))
          (fun _ _ w => w) d) d)
      (Err.app ε₁
        (Err.app (s := (ldSendSig S₁ N Sd (X' × Ledger E (J₁ ⊕ J₂)) E₂).shape)
          (ldSendFamErr N Sd Ln, (0, ())) ε₂)) :=
  sum_order S₁ N Sd Ln (fun _ w => w) d h₁ h₂ (fun _ h => h)
    (fun b m wp (hw : B₀.relR (b.1.1, b.2) (S₁.left N (T := OMsg.Msg) m, wp) ∧
        Agree (a b.1.1) (msg₁ (S₁.left N (T := OMsg.Msg) m)) (ent (S₁.right N (T := OMsg.Msg) m)) ∧
        Ledger.Holds b.1.2
          (Sum.elim (msg₁ (S₁.left N (T := OMsg.Msg) m)) (ent (S₁.right N (T := OMsg.Msg) m)))) =>
      (⟨hw.1, (late_holds (a b.1.1) b.1.2 _ _ hw.2.1).1 hw.2.2⟩ :
        B₀.relR (b.1.1, b.2) (S₁.left N (T := OMsg.Msg) m, wp) ∧
          Ledger.Holds (pullL (a b.1.1) b.1.2) (msg₁ (S₁.left N (T := OMsg.Msg) m))))
    hF hL hE

end Late
end Cb.Sub
