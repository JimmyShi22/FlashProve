-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/OwnOpen.lean: FROM A LINK's OPENING TO A LATER RECORD OF THE SAME LINK: the
half that names no seat. What the head's opening lays; a fold over blocks that each leave what ctxOf
reads leaves it; and a context that counts as open is the open link's. Theorems, proved.

Why. The invariant of Johnson/Goal/Meaning/OwnInv.lean says the open link's list of arrays AT THE
NUMBER THAT THE RECORD BEARS. That this number is the number of the link at whose place the record
stands is local to the link: the opening lays it (openAtt_ctx, openLay_ctx, openLayZero_ctx, there;
headOpenQ_ctx, here), and every block between the opening and the place leaves it.

  mark_failed, openHead_opened   a marked record is not handed on by "unmarked"; so behind
    openHead's yes the head's part counts as open.
  headOpenQ_ctx   a yes of "H.1.quiet" at the letters P: (ctxOf t).2 = some (2, r, P.l, P.X.arrayOf)
    for some r.
  sameCtx_refl, sameCtx_trans, whole_sameQ, fold_ctx   SameCtx over a fold; every Quiet block is
    Whole SameCtx.
  link_of_ctx   (ctxOf t).2 = some (m, r, l, ar) with m ≠ 1 gives L with t.link? = some L, L.link =
    l, L.arrayOf = ar, L.check.rows = r.
  ctx_of_link   the way back: the open link's context is what ctxOf reads.
  own_rows   under the invariant t.check.rows.layout = lay and t.live.rows.layout = lay.

Whole SameCtx of the makers that are not Quiet: commitAtS_ctx, firstAtS_ctx, oneEquation_ctx,
closing_ctx (Johnson/Goal/Meaning/OwnMakers.lean); ctx_kept
(Johnson/Goal/Meaning/K2Share/OwnKept.lean).

Object, letters. Object: ctxOf; headOpenQ; foldBlocks.
Letters: all free.

What is not claimed. WHICH BLOCK STANDS AT WHICH PLACE OF A SEATED TEXT: so nothing yet on any place
(l, i). Nothing on soundness.
-/
import Johnson.Goal.Meaning.OwnMakers
import Johnson.Goal.Meaning.K2Share.OwnKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Johnson.Desc.First.Walk

variable {Cl : Type}

/-! ## What the head's opening lays -/

/-- A record that bears a mark is not handed on by "unmarked". -/
theorem mark_failed (s : S) (n : String) : (s.mark n).failed ≠ none := by
  unfold S.mark
  split
  · rename_i h
    rw [h]
    exact Option.some_ne_none _
  · exact Option.some_ne_none _

/-- Behind openHead's yes the head's part counts as open. -/
theorem openHead_opened {s s₁ : S} (h : s.openHead.unmarked = .ok s₁) {b : HeadOwn}
    (hb : s₁.here = .head b) : b.opened = true := by
  obtain ⟨e, hf⟩ := (S.unmarked_ok _ _).1 h
  rw [← e] at hb hf
  have hm : ∀ n, s.openHead = s.mark n → False := fun n k => by
    rw [k] at hf
    exact mark_failed _ _ hf
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true
    · exact (hm "state-open-head" (by simp [S.openHead, hh, ho])).elim
    · have k : s.openHead.here =
          .head { a with opened := true, L := { a.L with check := s.check } } := by
        simp [S.openHead, hh, ho]
      rw [k] at hb
      cases hb
      rfl
  | between => exact (hm "state-open-head" (by simp [S.openHead, hh])).elim
  | lay a => exact (hm "state-open-head" (by simp [S.openHead, hh])).elim
  | att a => exact (hm "state-open-head" (by simp [S.openHead, hh])).elim
  | fin a => exact (hm "state-open-head" (by simp [S.openHead, hh])).elim
  | mem a => exact (hm "state-open-head" (by simp [S.openHead, hh])).elim

open VerifiableInference.Desc.First.K2 in
/-- **"H.1.quiet"**: the context that it leaves open. -/
theorem headOpenQ_ctx {P : HeadPar} {s t : S} (h : headOpenQ P s = .ok t) :
    ∃ r, (ctxOf t).2 = some (2, r, P.l, P.X.arrayOf) := by
  unfold headOpenQ at h
  split at h
  · rename_i a ha
    split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := ebind h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hfr, h⟩ := ebind h
        dsimp only at h
        have hL := (Law.front_ok hfr).2.2.1
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h1, h⟩ := ebind h
                split at h
                · rename_i b hb'
                  cases h
                  have ho := openHead_opened h1 hb'
                  refine ⟨L.check.rows, ?_⟩
                  show some ((if b.opened = true then 2 else 1), L.check.rows, L.link, L.arrayOf) =
                    _
                  rw [if_pos ho, hL]
                · cases h
        · cases h
  · cases h

/-! ## Over a stretch that leaves ctxOf -/

theorem sameCtx_refl (s : S) : SameCtx s s := rfl

theorem sameCtx_trans (a b c : S) (h : SameCtx a b) (k : SameCtx b c) : SameCtx a c :=
  Eq.trans k h

theorem whole_sameQ {b : Block S Cl} (W : Whole Quiet b) : Whole SameCtx b :=
  whole_mono (fun _ _ q => q.ctx) W

/-- **A fold over blocks that each leave what ctxOf reads leaves it.** -/
theorem fold_ctx {ft : Nat} {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, Decides SameCtx b) {s : S}
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft bs s rs cols = .ok r) : ctxOf r.1 = ctxOf s :=
  Keeps.foldBlocks_keeps SameCtx sameCtx_refl sameCtx_trans ft bs hb s rs cols r h

/-! ## From ctxOf to the open link -/

/-- **A context that counts as open is the open link's.** -/
theorem link_of_ctx {t : S} {m l : Nat} {r : ReqRows} {ar : Array (Nat × String)}
    (h : (ctxOf t).2 = some (m, r, l, ar)) (hm : m ≠ 1) :
    ∃ L, t.link? = some L ∧ L.link = l ∧ L.arrayOf = ar ∧ L.check.rows = r := by
  unfold ctxOf at h
  unfold S.link?
  cases hh : t.here with
  | between => simp [hh] at h
  | fin a => simp [hh] at h
  | mem a => simp [hh] at h
  | lay a =>
    simp only [hh, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨a.L, rfl, h.2.2.1, h.2.2.2, h.2.1⟩
  | att a =>
    simp only [hh, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨a.L, rfl, h.2.2.1, h.2.2.2, h.2.1⟩
  | head a =>
    simp only [hh, Option.some.injEq, Prod.mk.injEq] at h
    by_cases ho : a.opened = true
    · exact ⟨a.L, by simp [ho], h.2.2.1, h.2.2.2, h.2.1⟩
    · rw [if_neg ho] at h
      exact absurd h.1.symm hm

/-- The open link's context is what ctxOf reads. -/
theorem ctx_of_link {t : S} {L : LinkCtx} (h : t.link? = some L) :
    ∃ m, (ctxOf t).2 = some (m, L.check.rows, L.link, L.arrayOf) := by
  unfold S.link? at h
  unfold ctxOf
  cases hh : t.here with
  | between => simp [hh] at h
  | fin a => simp [hh] at h
  | mem a => simp [hh] at h
  | lay a =>
    simp only [hh, Option.some.injEq] at h
    subst h
    exact ⟨0, rfl⟩
  | att a =>
    simp only [hh, Option.some.injEq] at h
    subst h
    exact ⟨0, rfl⟩
  | head a =>
    simp only [hh] at h
    split at h
    · cases h
      exact ⟨_, rfl⟩
    · cases h

/-- **Under the invariant both copies of the rows' layout that the calls can read are lay**: the
walk's own, and the live one (the open link's, where a link is open). -/
theorem own_rows {A : Nat → Array (Nat × String)} {lay : OnBytes.Params.ReqLayout} {t : S}
    (I : OwnInv A lay t) : t.check.rows.layout = lay ∧ t.live.rows.layout = lay := by
  refine ⟨I.1, ?_⟩
  unfold S.live
  cases hL : t.link? with
  | none => exact I.1
  | some L =>
    obtain ⟨m, hm⟩ := ctx_of_link hL
    exact (I.2 _ hm).1

#print axioms own_rows
#print axioms headOpenQ_ctx
#print axioms fold_ctx
#print axioms link_of_ctx

end Meaning.K2
