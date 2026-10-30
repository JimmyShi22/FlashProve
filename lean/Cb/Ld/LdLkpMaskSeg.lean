-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskSeg.lean: the head and the keys' side of the assembled lookup as links of a chain of
masked blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean; `MJ`, Cb/Ld/LdLkpMaskChain.lean).

Definitions, statements and proofs. Glue between Cb/Ld/LdLkpMaskTie.lean, Cb/Ld/LdLkpMaskTree.lean
and Cb/Ld/LdLkpMaskAsm.lean.
The identity: after the first challenge λ the lookup claims ∏ (λ - key) = ∏_j PT_j ^ (2 ^ j), PT_j
the table's product at bit position j (`LkHead.tie`, Cb/Ld/LdLkpHead.lean). The tie (`TieP`,
Cb/Ld/LdLkpTie.lean) is the chain of sumchecks that ties its two sides; the keys' tree (`LkInst.DK`,
Cb/Ld/LdLkpInst.lean) is the product tree with the factors λ - key.
A claim `C x k` is a predicate on an explicit part x and the entries k : J → E of the messages.
`MjStab`, `MJ.sp`: Cb/Ld/LdLkpMaskSp.lean. `hM` is `MaskOK` (Cb/Ld/LdLkpMaskTie.lean,
Cb/Ld/LdLkpMaskTree.lean).

Main names:
  `mjst_map`: a claim carried along a map of explicit parts.
  `LkHead.mjHead`, `mjl_head`: the head (Cb/Ld/LdLkpHead.lean): the first challenge, then the tie.
    (hypotheses: its doc comment)
  `mjSegK`, `mjl_segK`: the keys' side (Cb/Ld/LdLkpSegK.lean): the step into level 0, then the keys'
    tree. (hypotheses: its doc comment)

Notation:
  `D.Link H rdi rdo Sr Sw C` (Cb/Ld/LdLkpMaskSp.lean): three fields:
    `fits : (D.narrow C).Fits H rdi rdo`, `reads : D.MReads Sr`, `writes : D.Writes Sw`;
  `MjStab C S`: `∀ x k k', (∀ j, ¬ S j → k j = k' j) → C x k → C x k'` (the same file);
  `D.sp C`: `fun x' k => ∃ x ρ, C x k ∧ x' = D.nxt x (D.msg k x ρ) ρ` (the same file);
  `mjCut Rd m`: `fun j => if Rd j then m j else 0` (Cb/Ld/LdLkpMaskOur.lean);
  `Ex`: the external oracles (an `ExtSpec`, Iop/InteractiveOracleProof.lean);
  `M`: the type of the tuples of messages (a witness is in `M × Wp`: `BkA`, Cb/Ld/LdLkpTreeP.lean);
  `msg : M → H.J → E` (`H : LkHead E`; in `mjl_segK`: `M → I.J → E`): the entries of a tuple;
  `Dt`, `Rd`: predicates on `H.J` (in `mjl_segK`: `Dt`, `In`, `Rd`, on `I.J`);
  `hRd`: `∀ j, H.tie.srAt Dt H.n j → Rd j` (in `mjl_segK`:
    `∀ j, (I.setV (v' + 1)).DK.srAt Dt In v' j → Rd j`).

Limits: what the heads of Cb/Ld/LdLkpMaskTie.lean and Cb/Ld/LdLkpMaskTree.lean list as not said is
not said here either.
-/
import Cb.Ld.LdLkpMaskTreeProofs
import Cb.Ld.LdLkpSegK
import Cb.Ld.LdLkpHead
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section Rules
variable {E J : Type} {Xi Xi' Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}

theorem mjst_map {C : Xi' → (J → E) → Prop} {S : J → Prop} (h : MjStab C S) (φ : Xi' → Xi) :
    MjStab (fun x k => ∃ x₀, C x₀ k ∧ x = φ x₀) S :=
  fun _ k k' hk ⟨x₀, hc, e⟩ => ⟨x₀, h x₀ k k' hk hc, e⟩

/-- If the claim `C` gives a property `P` of the entries alone, so does `D.sp C`. -/
theorem mjsp_keeps (D : MJ E J R) {C : Xi → (J → E) → Prop}
    {P : (J → E) → Prop} (h : ∀ x k, C x k → P k) : ∀ x' k, D.sp C x' k → P k :=
  fun _ k ⟨x, _, hc, _⟩ => h x k hc

theorem mjst_false {X : Type} (C : X → (J → E) → Prop) : MjStab C fun _ => False :=
  fun _ k k' hk hc => by rwa [← funext fun j => hk j fun h => h]

/-- A claim that reads none of the sets S 0, .., S n reads nothing of their union. -/
theorem mjst_upto {X : Type} {C : X → (J → E) → Prop} (S : ℕ → J → Prop) :
    ∀ n, (∀ l ≤ n, MjStab C (S l)) → MjStab C fun j => ∃ l ≤ n, S l j
  | 0, h => mjst_mono (h 0 (le_refl 0)) fun j ⟨l, hl, hj⟩ => by rwa [Nat.le_zero.1 hl] at hj
  | n + 1, h =>
      mjst_mono
          (mjst_or (mjst_upto S n fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (le_refl _)))
          fun j ⟨l, hl, hj⟩ => by
      rcases Nat.lt_or_ge l (n + 1) with h1 | h1
      · exact Or.inl ⟨l, Nat.le_of_lt_succ h1, hj⟩
      · exact Or.inr (by rwa [Nat.le_antisymm hl h1] at hj)

end Rules

section
variable {E : Type} [Field E] [Fintype E]

/-- The `MJ` record of the head `H.headA`. -/
def LdLkp.LkHead.mjHead
    (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E) (Rd : H.J → Prop) :
    MJ E H.J (H.headA Ex M Wp Kc msg).R :=
  (MJ.silent E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True).seq
    ((H.tie.mjTie Ex M Wp Kc msg Rd H.n).pre (fun x => some ((0 : E), x))
      (ExtMap.id Ex) fun x => ((0 : E), x))

/-- The `MJ` record of the keys' side `segK`. -/
def LdLkp.mjSegK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec)
    (M Wp Kc : Type) (msg : M → I.J → E) (Rd : I.J → Prop) :
    MJ E I.J (segK I v' tK Ex M Wp Kc msg).R :=
  ((I.setV (v' + 1)).DK.mjTree Ex M Wp Kc msg Rd v').pre
    (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex) (enterK (I.setV (v' + 1)) tK)

variable (E)

/-- Under `hM` and `hRd`: the head is a link, started with any claim that gives the identity at
every first challenge and reads no own mask of the tie. -/
theorem mjl_head (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E)
    (Dt Rd : H.J → Prop) (C : H.St → (H.J → E) → Prop) (hM : H.tie.MaskOK H.n Dt)
    (hRd : ∀ j, H.tie.srAt Dt H.n j → Rd j)
    (hC : ∀ st k, C st k → ∀ lam : E, H.tie.claim 0 ((0 : E), (st, lam)) k)
    (hs : ∀ l ≤ H.n, MjStab C (H.tie.ownAt l)) :
    (H.mjHead Ex M Wp Kc msg Rd).Link (H.headA Ex M Wp Kc msg).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (fun j => ∃ l ≤ H.n, H.tie.srAt Dt l j)
      (fun j => ∃ l ≤ H.n, H.tie.ownAt l j) C := by
  have hstep : H.tie.StepTo H.n := fun st m j hj =>
    (ldLkpTie_hU E (H.n + 1) (H.PT st m) (Nat.succ_pos _)).1 j hj
  have hs1 : ∀ l ≤ H.n,
      MjStab
        ((MJ.silent (E := E) (J := H.J) E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True).sp C)
        (H.tie.ownAt l) := fun l hl =>
    mjst_sp (hs l hl) (Sr := fun _ => False) (fun _ _ _ _ _ => rfl) fun _ h => h.elim
  have h2 := ldLkpMaskTie_link E H.tie Ex M Wp Kc msg H.n Dt Rd
    (fun x k =>
      ∃ x₀,
        (MJ.silent (E := E) (J := H.J) E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True).sp
          C x₀ k ∧
        x = ((0 : E), x₀))
    hstep hM hRd (by rintro _ k ⟨_, ⟨st, ρ, hc, rfl⟩, rfl⟩; exact hC st k hc ρ.1)
    fun l hl => mjst_map (hs1 l hl) _
  exact mjl_mono
    (mjl_seq (mjl_draw E (Prod.mk : H.St → E → H.St × E) Ex (M × Wp) (fun _ _ => True)
        C fun w => mjCut Rd (msg w.1))
      (mjl_pre (fun x => some ((0 : E), x)) (ExtMap.id Ex) (fun x => ((0 : E), x)) h2
        (mjst_upto _ H.n hs1) (fun o => (((0 : E), o.1), o.2)) (fun w => mjCut Rd (msg w.1))
        (fun _ _ => rfl) fun _ _ => rfl)
      (fun _ h => h.elim) (mjst_upto _ H.n hs))
    (fun _ h => h.elim False.elim id) fun _ h => h.elim False.elim id

/-- Under `hM` and `hRd`: the keys' side is a link, started with any claim that gives the masked
claim on the product of the keys and reads no own mask of the keys' tree. -/
theorem mjl_segK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → I.J → E) (Dt In Rd : I.J → Prop) (C : I.X → (I.J → E) → Prop)
    (hM : (I.setV (v' + 1)).DK.MaskOK v' Dt In)
    (hRd : ∀ j, (I.setV (v' + 1)).DK.srAt Dt In v' j → Rd j)
    (hC : ∀ x k, C x k → keyProd (v' + 1) (I.key (I.st x) k) (I.lam x) + ∑ j, I.fK x j * k j = tK x)
    (hs : ∀ l ≤ v', MjStab C ((I.setV (v' + 1)).DK.ownAt l)) :
    (mjSegK I v' tK Ex M Wp Kc msg Rd).Link (segK I v' tK Ex M Wp Kc msg).H
      (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1))
      (fun j => ∃ l ≤ v', (I.setV (v' + 1)).DK.srAt Dt In l j)
      (fun j => ∃ l ≤ v', (I.setV (v' + 1)).DK.ownAt l j) C := by
  have hsum : ∀ (x : I.X) (m : I.J → E),
      ((I.setV (v' + 1)).DK.lv 0).T.SumHolds
        (enterK (I.setV (v' + 1)) tK x) (fun j => m (((I.setV (v' + 1)).DK.lv 0).toJ j)) ↔
      keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x := fun x m => by
    rw [ldLkpP_sum E (I.setV (v' + 1)).DK (ldLkpInst_stepK E (I.setV (v' + 1))) 0
        (enterK (I.setV (v' + 1)) tK x) m]
    have hu : (I.setV (v' + 1)).DK.U
          (((I.setV (v' + 1)).DK.lv 0).base (enterK (I.setV (v' + 1)) tK x).2) m 0 =
        fun _ => keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) :=
      funext fun θ => ldLkpInst_rootK E (I.setV (v' + 1)) x m θ
    rw [hu, Alg.mle_const]
    exact Iff.rfl
  have h2 := ldLkpMaskTree_link E (I.setV (v' + 1)).DK Ex M Wp Kc msg v' Dt In Rd
    (fun x k => ∃ x₀, C x₀ k ∧ x = enterK (I.setV (v' + 1)) tK x₀)
    (ldLkpInst_stepK E (I.setV (v' + 1))) hM hRd
    (by rintro _ k ⟨x₀, hc, rfl⟩; exact (hsum x₀ k).2 (hC x₀ k hc)) fun l hl => mjst_map (hs l hl) _
  exact mjl_pre (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex)
    (enterK (I.setV (v' + 1)) tK) h2 (mjst_upto _ v' hs)
    (fun o => (enterK (I.setV (v' + 1)) tK o.1, o.2)) (fun w => mjCut Rd (msg w.1))
    (fun _ _ => rfl) fun _ _ => rfl

end
end Cb
