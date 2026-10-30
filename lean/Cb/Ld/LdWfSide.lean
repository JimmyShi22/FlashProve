-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfSide.lean: under the hypotheses of its statement, the preamble of weights-formedness bears
what follows (`IOR.Bears`, Ior/Bears.lean): proof of `Spec.ldWf_side` (Cb/Ld/LdWf.lean). Nothing is
assumed beside the hypotheses in the statement's text.

`noHid`: the set `H.Hid w x` is empty for all w and x. `noTie`: the set `R.tie ρ p` is empty for all
ρ and p. `R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance
for which qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of
`R.need ρ U`. `R.need ρ U`, for a set U of positions of the new implicit instance: `R.given ρ` of
the positions `R.srcO ρ q` for q in U, together with the positions `R.srcE ρ q` for q in U. Here
`Side` (Ior/KnowCollPiece.lean), the conclusion of `Spec.ldWf_side`, has the three fields `noHid`,
`noTie` and `bears : R.Bears bud qi qo`.

Why: the budgets' half of a piece (Ior/KnowCollPiece.lean: `Side`) goes link by link
(`chain_sides`). The sending has it by its own lemma (Cb/Ld/LdSendPiece.lean: `ldSendFam_bears`). A
masked block has it almost for nothing (`side_of_mm`): it sends no oracle. Asked of each lookup by
the statement: its budget holds at the empty set; what it needs of its input oracles is what is
needed of its output oracles.
Steps without rounds that do nothing to the oracles change nothing (`need_post_id`, `need_pre_id`);
a block that only copies its oracles needs what is needed (`need_onlyCopies`, `need_keep`).

Limits: what the head of Cb/Ld/LdWf.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfList
import Cb.Ld.LdSendPiece

set_option autoImplicit false

namespace Iop
namespace IOR
variable {X₁ X₂ X₃ X X' Z : Type} {E E₁ E₂ F : ExtSpec}

theorem need_post_id (R : IOR X₁ E₁ X₂ E₂) (f : X₂ → Option X₃)
    (ρ : Rho R.shape) (U : Finset E₂.Pos) :
    (R.post f (ExtMap.id _)).need ρ U = R.need ρ U := by
  have e1 : (R.post f (ExtMap.id _)).srcO ρ = R.srcO ρ := funext (post_id_srcO R f ρ)
  have e2 : (R.post f (ExtMap.id _)).srcE ρ = R.srcE ρ := funext (post_id_srcE R f ρ)
  unfold need
  rw [e1, e2]
  rfl

theorem wfPre_id_set {E : ExtSpec} {inst : DecidableEq E.Pos} (s : Finset E.Pos) :
    @Finset.biUnion _ _ inst s (ExtMap.id E).src = s := by
  refine Finset.ext fun u => ?_
  simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
  exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩

theorem wfPre_id_tie (R : IOR X₂ E₁ X₃ E₂) (f : X₁ → Option X₂)
    (ρ : Rho R.shape) (p : OPos R.shape) :
    (R.pre f (ExtMap.id _)).tie ρ p = R.tie ρ p := wfPre_id_set _

theorem need_pre_id (R : IOR X₂ E₁ X₃ E₂) (f : X₁ → Option X₂)
    (ρ : Rho R.shape) (U : Finset E₂.Pos) :
    (R.pre f (ExtMap.id _)).need ρ U = R.need ρ U := by
  have e1 : (R.pre f (ExtMap.id _)).extReads ρ = R.extReads ρ := wfPre_id_set _
  have e2 : (R.pre f (ExtMap.id _)).srcE ρ = R.srcE ρ := funext fun q => wfPre_id_set _
  have e3 : (R.pre f (ExtMap.id _)).tie ρ = R.tie ρ := funext fun p => wfPre_id_set _
  unfold need given
  rw [e1, e2, e3]
  rfl

theorem need_onlyCopies {R : IOR X E X' E} (h : R.OnlyCopies) (ρ : Rho R.shape) (U : Finset E.Pos) :
    R.need ρ U = U := by
  classical
  refine Finset.ext fun q => ?_
  rw [mem_need]
  constructor
  · rintro (hq | ⟨u, hu, hq⟩)
    · unfold given at hq
      rw [h.noReads, Finset.empty_union] at hq
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hq
      rw [h.noTie] at hp
      exact absurd hp (Finset.notMem_empty _)
    · rw [(h.src ρ u).1, Finset.mem_singleton] at hq
      rw [hq]
      exact hu
  · exact fun hq => Or.inr ⟨q, hq, by rw [(h.src ρ q).1]; exact Finset.mem_singleton_self q⟩

end IOR
end Iop

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp IOR.Chain

theorem need_keep {X X' Z : Type} {E F : ExtSpec} {R : IOR X E X' E} (h : R.OnlyCopies)
    (ρ : Rho R.shape) (U : Finset (E.prod F).Pos) : (R.keep Z F).need ρ U = U := by
  refine Finset.ext fun q => ?_
  rcases q with q | q
  · rw [← Finset.mem_toLeft, keep_need_left, need_onlyCopies h, Finset.mem_toLeft]
  · rw [← Finset.mem_toRight, keep_need_right, Finset.mem_toRight]

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

theorem lSend_side (B : P.Blk) (q : Finset C.E0.Pos → Prop) : B.lSend.Side q (P.S.qFam q B.t) where
  noHid := fun _ _ => rfl
  noTie := fun ρ p => wfPre_id_tie (ldSendFam P.S P.Sd P.WSt C.E0) (fun rec => some (P.st0 rec)) ρ p
  bears := fun ρ U hU => by
    have h0 := ldSendFam_bears P.S P.Sd P.WSt C.E0 B.t q ρ U hU
    refine ⟨h0.1, ?_⟩
    show q
      (((ldSendFam P.S P.Sd P.WSt C.E0).pre (fun rec => some (P.st0 rec)) (ExtMap.id _)).need ρ U)
    rw [need_pre_id]
    exact h0.2

theorem lLkp_side {B : P.Blk} (h : B.Hyp) {l : ℕ} (hl : l ≤ P.n) (Q : Finset P.Ex.Pos → Prop)
    (hb : ∀ ρ, (B.sub l).P.bud ρ ∅) (hn : ∀ ρ U, (B.sub l).R.need ρ U = U) : (B.lLkp l).Side Q Q :=
  side_of_mm _ _ _ _ _ _ _ _ ((B.Dm l).post _ _) _ Q Q
      (mm_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.lkpM l hl)) hb fun ρ U hU => by
    show Q (((B.sub l).R.post (P.file l) (ExtMap.id _)).need ρ U)
    rw [need_post_id, hn]
    exact hU

theorem lBatt_side {B : P.Blk} (h : B.Hyp) (Q : Finset P.Ex.Pos → Prop) : P.lBatt.Side Q Q := by
  have hc : (P.bt.batt C.E0).OnlyCopies :=
    (OnlyCopies.draw _ _ _).seq
      ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  have m0 := idxLift_mm E C P.S _ _ Unit Unit (P.bt.batt C.E0)
    (P.bt.hon C.E0 fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1) _
    (batt_mm E P.bt C.E0 _ _ B.Rd h.deg h.own)
  refine side_of_mm _ _ _ _ _ _ _ _ (DmL B) _ Q Q
    (mm_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (mm_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) m0))
    (fun _ _ _ _ _ => ⟨trivial, trivial⟩) fun ρ U hU => ?_
  show Q (((((P.bt.batt C.E0).keep P.S.Smp P.S.ext).pre
          (fun x => some (P.toBatt x)) (ExtMap.id _)).post
        (fun x => some (P.toLast x)) (ExtMap.id _)).need
      ρ U)
  rw [need_post_id, need_pre_id, need_keep hc]
  exact hU

theorem cLkp_sides {B : P.Blk} (h : B.Hyp) (q : Finset C.E0.Pos → Prop)
    (hb : ∀ l, l ≤ P.n → ∀ ρ, (B.sub l).P.bud ρ ∅)
    (hn : ∀ l, l ≤ P.n → ∀ ρ U, (B.sub l).R.need ρ U = U) :
    ∀ l, l ≤ P.n → (B.cLkp l).Sides q (P.S.qFam q B.t)
  | 0, hl => by
      rw [cLkp_zero, sides_snoc]
      exact ⟨P.S.qFam q B.t,
        (sides_one _ _ _).2 (lSend_side B q),
        lLkp_side h hl _ (hb 0 hl) (hn 0 hl)⟩
  | l + 1, hl => by
      rw [cLkp_succ, sides_snoc]
      exact ⟨P.S.qFam q B.t,
        cLkp_sides h q hb hn l (Nat.le_of_succ_le hl),
        lLkp_side h hl _ (hb _ hl) (hn _ hl)⟩

end LdWfP

theorem ldWf_side (E : Type) [Field E] [Fintype E] : Spec.ldWf_side E := by
  intro C P B q h hb hn
  have hs : B.chain.Sides q (P.S.qFam q B.t) :=
    (sides_snoc _ _ _ _).2
      ⟨P.S.qFam q B.t, LdWfP.cLkp_sides h q hb hn P.n (Nat.le_refl _), LdWfP.lBatt_side h _⟩
  have hl : IOR.Side B.link.R B.link.H B.link.P.bud q (P.S.qFam q B.t) :=
    chain_sides Unit _ _ B.chain B.p0 q _ hs
  exact
    { noHid := hl.noHid
      noTie := hl.noTie
      bears := fun ρ U hU => by
        have h0 := hl.bears ρ U hU
        have e1 : B.wf.srcO ρ = B.link.R.srcO ρ :=
          funext (post_id_srcO B.link.R (fun x => some (closeX P.S x)) ρ)
        have e2 : B.wf.need ρ U = B.link.R.need ρ U :=
          need_post_id B.link.R (fun x => some (closeX P.S x)) ρ U
        rw [e1, e2]
        exact h0 }

end Cb
