--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WFold.lean: W IS THE COMMITTED FOLD: Spec.fold
(Johnson/Desc/K14/Law/WFoldSpec.lean), proved. A theorem.

  plan_at_yes  a yes of the chain's own first block gives the two facts on the plan that the fold
               wants: the index's shape is in order, and the matrix has room before the pads: the
               block asks the public shape's conditions itself (linPoint_ok).
  dot_at_yes   a yes of that block, the point's high part no bad point of the key's, near and
               RecAll and DotU behind: tab decodes, and (Dot)'s equation holds with the decoded
               matrix at the drawn point. The content of point_yes
               (Johnson/Desc/K14/Law/PointCounts.lean) at the block's own decision: no piece, no
               frame, no transcript. Of the yes it spends: the key stays; the plan's two facts.
  w_is_the_committed_fold   **the statement**: if moreover the point is not lost for this very
               vector: W's message holds g^T M at every column.
Limits. THE STEP WITHOUT CHANCE, AT ONE DRAWN POINT; NOT THE ROUND's LAW; NO COUNT: see the Spec.
ON CREDIT: near, RecAll and DotU behind the block are premises. THE LAWS THAT BEAR THESE NAMES IN
FRONT (sendU_goodIn, rec_goodInR, loc_goodIn4', zeta_goodIn7, split_goodIn8) CANNOT FEED THIS
THEOREM AS THEY STAND: they are laws of the rule of composition, up to lost draws, at pieces: none
hands near AT A POINT. What composes with them is point_goodInY2, whose relation in front has DecX2
and VIs already; from there wis_iff_vis gives WFold. So in the rule of composition this theorem is
the inside of point_goodIn said again, not a link. Their letters do fit. (Dot)'s equation at
o_omega's number is paid by no block of the shared chain: it crosses to the proof's last chain. The
three stand at withNext s', whatever the record notes: at a record that has noted o_u already the
theorem is idle, not false.
The code's size (logN ≤ 32) is a premise on the plan. err, eM, rank, tab are free letters, tied to
nothing in front: for a count of the key's bad points err, eM, rank must be the plan's (the
statement on codes' own conditions). dot_at_yes has the decoder's radius eM and near's e' as two
letters; the statement has one. NO MEMBER IS SHOWN: near has not been run at an honest witness's
words; a theorem under premises at free letters can be idle. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.WFoldSame
import Johnson.Desc.K14.Law.Condition
import Johnson.Desc.K14.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K13.Law (EvalAt WIs matBy)

/-- A yes of "LIN point" gives the two facts on the plan. -/
theorem plan_at_yes (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (s s' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hyes : b1.decide s rs gs = .ok s') :
    P.par.S.fold.index.ok = true ∧
      P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain := by
  have hok := linPoint_ok _ _ _ _ (point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hyes)
  refine ⟨index_ok_of_linOk _ _ hok, ?_⟩
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hS : P.par.S.ok = true := by tauto
  simp only [LinShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
  tauto

/-- **What a yes of "LIN point" gives, at its own decision.** -/
theorem dot_at_yes (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (ha : P.par.S.fold.index.code.logN ≤ 32) (err eM e' : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (s s' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (psi : Fin P.par.S.kCol → GE)
    (hyes : b1.decide s rs gs = .ok s')
    (hpsi : s'.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn psi)
    (hfit : s.loc.key.fits P.par.S.fold.index = true) (rgw : Words GE) (g V : Nat → GE)
    (hnb : ¬ BadX2 P.par err eM rank e' tab s.loc.key
      (gamOf P.par.S.kLo P.par.S.fold.index.v psi))
    (hnear : NearAt OnBytes.Model.Reading.gl P.par (withNext P.par s') rgw tab e')
    (hrec : RecAll OnBytes.Model.Reading.gl P.par (withNext P.par s') rgw)
    (hdot : DotUAt P.par.S g (withNext P.par s').loc rgw V) :
    DecX2 P.par err eM rank tab s.loc.key ∧
      DotTrue P.par.S g (TabX2 P.par err eM rank tab s.loc.key) V psi := by
  obtain ⟨hi, hroom⟩ := plan_at_yes P b1 b2 b3 b4 b5 b6 b7 b8 hbl s s' rs gs hyes
  have k1 := point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hyes
  obtain ⟨r, -, -, hkeyE, -, -⟩ := linPoint_inv _ _ _ _ k1
  have hk : (withNext P.par s').loc.key = s.loc.key := hkeyE
  have e1 : (withNext P.par s').loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn psi := hpsi
  have eg : (gamma P.par.S (withNext P.par s').loc).map OnBytes.Model.Reading.gl.val =
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v psi) := by
    unfold gamma
    rw [List.map_drop, e1]
    exact drop_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have et : ((withNext P.par s').loc.psiSh.take P.par.S.kLo).map
      OnBytes.Model.Reading.gl.val = List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v psi) := by
    rw [List.map_take, e1]
    exact take_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have eapp : List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v psi) ++
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v psi) = List.ofFn psi := by
    rw [← take_ofFn, ← drop_ofFn]
    exact List.take_append_drop _ _
  have h := good_of_notBad2 P.par ha err eM rank e' tab (withNext P.par s') rgw _ hi hroom
    (by rw [hk]; exact hfit) (by rw [hk]; exact hnb) eg hnear hrec
  rw [hk] at h
  obtain ⟨hdec, hU⟩ := h
  unfold DotUAt at hdot
  rw [et, e1, ← eapp] at hdot
  have hfin := dotTrue_of P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v
    (TabX2 P.par err eM rank tab s.loc.key) _ _ g (uOf (withNext P.par s').loc rgw) V (by simp)
    hU hdot
  rw [eapp] at hfin
  exact ⟨hdec, hfin⟩

/-- **W is the committed fold.** -/
theorem w_is_the_committed_fold : Spec.fold := by
  intro P b1 b2 b3 b4 b5 b6 b7 b8 hbl ha err eM rank tab s s' rs gs psi hyes hpsi hfit
    D m rgw g V hg hvec hnb hno hnear hrec hdot
  obtain ⟨hdec, hdt⟩ := dot_at_yes P b1 b2 b3 b4 b5 b6 b7 b8 hbl ha err eM eM rank tab s
    s' rs gs psi hyes hpsi hfit rgw g V hnb hnear hrec hdot
  have hV : VIs P.par.S g (TabX2 P.par err eM rank tab s.loc.key) V := by
    by_contra hn
    exact hno ⟨hn, hdt⟩
  exact ⟨hdec, (wis_iff_vis P.par.S D m _ g V hg hvec).2 hV⟩

end Desc.K14.Law
