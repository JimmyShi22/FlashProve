-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamTreesSh.lean: **THE COMPARISONS OF TREES' NUMBERS AT THE SHARED CHAIN, AT N.tenant := tenantSh (SharedMembers.lean): FROM TWO EQUATIONS ON TWO PIECES' BASES.** Statements and proofs; counting alone.
  hlo_sh          N.lo ≤ every tenant's tree.
  tU_sh | tO_sh | tS_sh   the three comparisons (share_seamed's binders tU · tO · tS): o_u's tree lies below lo + (the number of trees of o_u's sending) · o_omega's and o_sp's below that + (the number of trees of o_omega's sending): by the planner's own law
                  (lay_lt: a message's tree is one of the layout's).
  htree_sh        its htree2 | htree5: each member's tree is (its sending's first tree) + j with j below the sending's number of trees.
  **sb_sh**       SentBefore N f l k x m FOR ALL THREE MESSAGES AT EVERY BLOCK k ≥ 6 of a tiled row (so nine_paid's | ten_paid's sb, and word_seat's window at 9 | 10): from: the base of the row's piece number 3 is lo + layU.shapes.size · that of number 6 is lo + layU.shapes.size + layO.shapes.size.
LEFT: THESE TWO EQUATIONS (the data's: how many trees the two sendings' pieces bear, and that no other piece in front of number 6 bears any) · Tiled (from "the pieces fit": tiledOfFit, TilesCutProofs.lean).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SentBeforeTiled
import Johnson.Desc.Sound.SeamNumbersSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

section
variable (lo : ℕ) (layU layO : TreeLay)

theorem hlo_sh (m : Msg2) : lo ≤ (tenantSh lo layU layO m).1 := by
  cases m <;> simp only [tenantSh] <;> omega

variable (codes : Codes) (sentU sentO : Array OracleNotice)
  (hlU : layTrees codes sentU = some layU) (hlO : layTrees codes sentO = some layO)
  (hU : 0 < sentU.size) (hO : 1 < sentO.size)

include hlU hU in
theorem tU_sh : (tenantSh lo layU layO .oU).1 < lo + layU.shapes.size := by
  have l0 := OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU hU
  simp only [tenantSh]
  omega

include hlO hO in
theorem tO_sh : (tenantSh lo layU layO .oOmega).1 < lo + layU.shapes.size + layO.shapes.size := by
  have l0 := OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (show 0 < sentO.size by omega)
  simp only [tenantSh]
  omega

include hlO hO in
theorem tS_sh : (tenantSh lo layU layO .oSp).1 < lo + layU.shapes.size + layO.shapes.size := by
  have l1 := OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO hO
  simp only [tenantSh]
  omega

include hlU hlO hU hO in
/-- Each member's tree, counted from its sending's first tree. -/
theorem htree_sh :
    (∃ j, (tenantSh lo layU layO .oU).1 = lo + j ∧ j < layU.shapes.size) ∧
      (∃ j, (tenantSh lo layU layO .oOmega).1 = lo + layU.shapes.size + j ∧ j < layO.shapes.size) ∧
      ∃ j, (tenantSh lo layU layO .oSp).1 = lo + layU.shapes.size + j ∧ j < layO.shapes.size :=
  ⟨⟨_, rfl, OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU hU⟩,
    ⟨_, rfl, OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (show 0 < sentO.size by omega)⟩,
    ⟨_, rfl, OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO hO⟩⟩

variable {P₁ S₂ Cl Cells Tok : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (f : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
  (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))

include hlU hlO hU hO in
/-- **SentBefore, for all three messages, at every block from number 6 on.** -/
theorem sb_sh (hN : N.tenant = tenantSh lo layU layO) (hNlo : N.lo = lo) (hT : Tiled f l)
    (x3 x6 : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (h3 : (f :: l)[3]? = some x3)
    (h6 : (f :: l)[6]? = some x6) (b3 : x3.base = lo + layU.shapes.size)
    (b6 : x6.base = lo + layU.shapes.size + layO.shapes.size) (k : ℕ) (hk : 6 ≤ k)
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (hx : (f :: l)[k]? = some x) (m : Msg2) :
    SentBefore N f l k x m := by
  have hl : N.lo ≤ (N.tenant m).1 := by rw [hN, hNlo]; exact hlo_sh lo layU layO m
  cases m
  · exact sentBefore_base N f l hT _ hl 3 k (by omega) x3 h3
      (by rw [hN, b3]; exact tU_sh lo layU layO codes sentU hlU hU) x hx
  · exact sentBefore_base N f l hT _ hl 6 k hk x6 h6
      (by rw [hN, b6]; exact tO_sh lo layU layO codes sentO hlO hO) x hx
  · exact sentBefore_base N f l hT _ hl 6 k hk x6 h6
      (by rw [hN, b6]; exact tS_sh lo layU layO codes sentO hlO hO) x hx

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.hlo_sh
#print axioms Desc.K14.Law.Fence.tU_sh
#print axioms Desc.K14.Law.Fence.tO_sh
#print axioms Desc.K14.Law.Fence.tS_sh
#print axioms Desc.K14.Law.Fence.htree_sh
#print axioms Desc.K14.Law.Fence.sb_sh
