-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendPiece.lean: under the hypotheses of its statements, the sendings of a family are pieces
of a chain.

This file is book-keeping for the composition of a long chain of reductions: for the two sendings
and for a lifted block it shows, under the hypotheses of its statements, beside the bundle, the
fields `noHid`, `noTie` and `bears` of `PieceTr` (Cb/Ld/LdTowerKit.lean).

Definitions, statements and proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a long chain is put together from "pieces" (Cb/Ld/LdTowerKit.lean: `PieceTr`). Pieces are told
with two conditions on sets of positions each, qi for the old implicit instance and qo for the new
one; pieces ask:
  the bundle `GoodT`;
  nothing hidden withheld (`noHid`);
  nothing tied (`noTie`);
  one invariant on positions for each link (`bears`; Ior/Bears.lean): if what follows needs the new
    implicit instance at a set U of positions that qo allows, the block's budget bears the sources
    of U in its own oracles, and what is needed of the old implicit instance is allowed by qi.

Main names, each under the hypotheses of its statement:
  `N.qFam q t`: on positions of (further oracles, words of N): the left part is allowed by q; of
    each member a at most `t a` long positions.
  `S.qSum N q t`: on positions of (further oracles, words of `S.sum N`): what lies in the further
    oracles and in the words of S is allowed by q; of each member a of N at most `t a` long
    positions.
  `Spec.ldSendFam_piece`: the sending of a family (Cb/Ld/LdSendFam.lean) is a piece from `A.cf` to
    the joint over the family (.cf), from q to `N.qFam q t`: nothing is needed of the old oracles
    but what is asked of them.
  `Spec.ldSendSig_piece`: the same for the sending to a statement over S (Cb/Ld/LdSigSum.lean), from
    q to `S.qSum N q t`.
  `Spec.sigLift_piece`: a block on claims about messages that is a piece at the base but for
    knowledge soundness, which it has for each fixed tuple of messages only, and whose honest prover
    ends with the messages with which it began (`GoodAt`, exact, nothing hidden, nothing tied, bears
    from qi to qo), lifted over S, is a piece between the joints over S: the positions in the words
    of S are handed through.

What `Laws`, `Fair`, `ListLE`, `Evades`, `Blind` and `Hides` ask: the head of Cb/Ld/LdRng.lean
("What the sending's hypotheses ask").

Limits: this file says nothing new on errors or zero knowledge.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigSumProofs
import Cb.Ld.LdSigLiftProofs
import Cb.Ld.LdGroupKit
import Blocks.Stage
import Hiop.ChainList
import Blocks.Level2Def
import Blocks.PfrHVZK_rs
import Iop.Deco
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Sig
variable {E : Type} (S N : Sig E) {E₀ : ExtSpec}

/-- the left part is allowed by q; of each member at most `t a` long positions -/
def qFam (q : Finset E₀.Pos → Prop) (t : N.O → ℕ) : Finset (E₀.prod N.ext).Pos → Prop := fun U =>
  q U.toLeft ∧ ∀ a, cnt (fun x : (N.om a).P => (Sum.inr ⟨a, x⟩ : (E₀.prod N.ext).Pos) ∈ U) ≤ t a

/-- the old part is allowed by q; of each member of N at most `t a` long positions -/
def qSum (q : Finset (E₀.prod S.ext).Pos → Prop) (t : N.O → ℕ) :
    Finset (E₀.prod (S.sum N).ext).Pos → Prop := fun U =>
  (∀ V : Finset (E₀.prod S.ext).Pos,
    (∀ p, p ∈ V ↔ ∃ u ∈ U, (Sum.inl p : ((E₀.prod S.ext).prod N.ext).Pos) ∈ (S.mergeE N E₀).src u) →
    q V) ∧
  ∀ a, cnt (fun x : (N.om a).P => (Sum.inr ⟨Sum.inr a, x⟩ : (E₀.prod (S.sum N).ext).Pos) ∈ U) ≤ t a

end Sig

namespace Spec

def ldSendFam_piece : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec)
      (A : Rels Kc X E₀ W) (back : N.Msg → W' → W) (D : N.Sender W W')
      (L t : N.O → ℕ) (q : Finset E₀.Pos → Prop),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws back → D.Blind Sd → D.Nn.Hides (N.budT t) →
    PieceTr (ldSendFam N Sd X E₀) (ldSendFamHon Sd X E₀ D) A.cf (N.over (N.pull A back)).cf
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamNums N Sd X E₀ Kc L t) q (N.qFam q t)

def ldSendSig_piece : Prop :=
  ∀ (E : Type) [Field E] (S N : Sig E) (Sd : N.Seeds) (Kc St Wp Wp' : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Blind Sd → D.Nn.Hides (N.budT t) →
    PieceTr (ldSendSig S N Sd St E₀) (ldSendSigHon Sd St E₀ D) (S.over A).cf
      ((S.sum N).over (S.grow N A bk)).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
      (ldSendSigNums S N Sd St E₀ Kc L t) q (S.qSum N q t)

def sigLift_piece : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec)
      (R : IOR St E₀ St' E₀') (H : R.Honest (S.Msg × Wp) (S.Msg × Wp'))
      (A : Rels Kc St E₀ (S.Msg × Wp)) (B : Rels Kc St' E₀' (S.Msg × Wp'))
      (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (P : Nums Kc R)
      (qi : Finset E₀.Pos → Prop) (qo : Finset E₀'.Pos → Prop) (qS : Finset S.ext.Pos → Prop),
    GoodAt R H A B ext P → H.Exact A.rel P.bud → (∀ w x, H.Hid w x = ∅) →
    (∀ ρ p, R.tie ρ p = ∅) → R.Bears P.bud qi qo →
    PieceTr (R.keep S.Smp S.ext) (S.liftH H) (S.over A) (S.over B)
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) (P.keep S.Smp S.ext)
      (besideQ qi qS) (besideQ qo qS)

end Spec

theorem ldSendP_mem_biUnion {α β : Type} {inst : DecidableEq β} {s : Finset α}
    {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion
theorem ldSendP_mem_image {α β : Type} {inst : DecidableEq β} {f : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

theorem ldSendFam_bears {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    (t : N.O → ℕ) (q : Finset E₀.Pos → Prop) :
    (ldSendFam N Sd X E₀).Bears (fun _ T => N.budT t (ldSendFamSet N Sd T)) q (N.qFam q t) := by
  classical
  intro ρ U hU
  refine ⟨fun a =>
      ⟨Finset.univ.filter fun x : (N.om a).P => (Sum.inr ⟨a, x⟩ : (E₀.prod N.ext).Pos) ∈ U,
        ?_, fun p hp => ?_⟩,
    ?_⟩
  · rw [← cnt_eq_card_filter]
    exact hU.2 a
  · have h1 := Finset.mem_toLeft.1 hp
    obtain ⟨u, hu, hpu⟩ := ldSendP_mem_biUnion.1 h1
    rcases u with u | ⟨a', x⟩
    · exact absurd hpu (Finset.notMem_empty _)
    · obtain ⟨p', hp', he⟩ := ldSendP_mem_image.1 hpu
      have he' : (⟨a', p'⟩ : Σ a, (N.om a).C.NP) = ⟨a, p⟩ := Sum.inl.inj he
      obtain rfl : a' = a := (Sigma.mk.inj he').1
      obtain rfl : p' = p := eq_of_heq (Sigma.mk.inj he').2
      exact Finset.mem_biUnion.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩, hp'⟩
  · have e : (ldSendFam N Sd X E₀).need ρ U = U.toLeft := by
      ext p
      rw [mem_need, mem_given, Finset.mem_toLeft]
      constructor
      · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
        · exact absurd h (Finset.notMem_empty _)
        · exact absurd h (Finset.notMem_empty _)
        · rcases u with u | u
          · rw [Finset.mem_singleton.1 h]
            exact hu
          · exact absurd h (Finset.notMem_empty _)
      · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self p⟩
    rw [e]
    exact hU.1

theorem ldSendFam_piece :
    Spec.ldSendFam_piece := fun E _ N Sd Kc X W W' E₀ A back D L t q hC hF hL hE hD hB hZ =>
  ⟨ldSendFam_chain E N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ,
    fun _ _ => rfl, fun _ _ => rfl,
    ldSendFam_bears N Sd X E₀ t q⟩

theorem ldSendSig_piece : Spec.ldSendSig_piece := by
  intro E _ S N Sd Kc St Wp Wp' E₀ A bk D L t q hC hF hL hE hD hB hZ
  refine ⟨ldSendSig_chain E S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ,
    fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  refine bears_post _ (S.mergeX N St) (S.mergeE N E₀) _ q (N.qFam q t) (S.qSum N q t)
    (ldSendFam_bears N Sd (St × S.Smp) (E₀.prod S.ext) t q) fun U V hV hU => ⟨?_, fun a => ?_⟩
  · exact hU.1 V.toLeft fun p => Finset.mem_toLeft.trans (hV (Sum.inl p))
  · refine (cnt_mono fun x hx => ?_).trans (hU.2 a)
    obtain ⟨u, hu, hxu⟩ := (hV _).1 hx
    rcases u with p | ⟨a' | a', x'⟩
    · exact absurd (Finset.mem_singleton.1 hxu) (by simp)
    · exact absurd (Finset.mem_singleton.1 hxu) (by simp)
    · have he : (⟨a, x⟩ : Σ a, (N.om a).P) = ⟨a', x'⟩ := Sum.inr.inj (Finset.mem_singleton.1 hxu)
      obtain rfl : a = a' := (Sigma.mk.inj he).1
      obtain rfl : x = x' := eq_of_heq (Sigma.mk.inj he).2
      exact hu

theorem sigLift_piece : Spec.sigLift_piece := by
  intro E _ S Kc St St' Wp Wp' E₀ E₀' R H A B ext P qi qo qS g hx hH hT hb
  refine ⟨sigLift_goodT E S Kc St St' Wp Wp' E₀ E₀' R H A B ext P g hx,
    fun w x => hH (S.msgs w.1, w.2) x.1,
    fun ρ p => ?_,
    fun ρ U hU => ⟨?_, ?_, ?_⟩⟩
  · show (R.tie ρ p).map _ = ∅
    rw [hT ρ p, Finset.map_empty]
  · rw [keep_srcO]
    exact (hb ρ U.toLeft hU.1).1
  · show qi ((R.keep S.Smp S.ext).need ρ U).toLeft
    rw [keep_need_left]
    exact (hb ρ U.toLeft hU.1).2
  · show qS ((R.keep S.Smp S.ext).need ρ U).toRight
    rw [keep_need_right]
    exact hU.2

end Cb
