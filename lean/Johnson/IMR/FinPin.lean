-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FinPin.lean: THE FINISH's FRONT, AS Johnson/IMR/FrontPin.lean HAS THE LINKS'
AND THE HEAD's; AND THE CARRIER FROM THE HEAD's LINK's CLOSING TO THE FINISH: at the proof file's
seat, in the goals' scope, from the fold's return alone.
  front_len: in scope the part of the flat list in front of the sub-protocols behind the last link
    has 353 entries (links_flat_352, BackSeat.lean).
  tail_frame_head: NOBODY TURNS THE FRAME BETWEEN THE HEAD's LINK's CLOSING AND THE FINISH: with s
    the state in front of that closing (the cut 350) and L the link open there: closeFrame, at L's
    frame and s's statement, has returned some y, and the walk's WHOLE frame at the cut 353 is y.1
    (Johnson/IMR/TailFrame.lean's tail_frame at l = 24, where no "laid" follows).
  fin_link: at the cut 353 the walk's frame's link is 25.
  front_pin_fin: THE TOP: at the front fx that K2.frontAt makes of the state behind the quiet step
    "F.0.front" at the cut 353 (that step's accept is a premise): the codes are the public ones; the
    messages are the state's at 353; fx.T = K2.targetAt sh 25; fx.others is the one fold's mask's
    notice, of the shape; fx.f.link = 25; the carried rows' code, mask code and number of masks are
    the shape's two and 2.
sh := Z.first.shape.
LIMIT: front_pin_fin ENDS IN THE PLAN's TERMS (Z.first.codes, K2.targetAt sh 25, the shape's two
codes): that these are the written front's is not shown here: closed comparisons, under premises on
the public shape and codes, are owed beside it.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.HeadMembers
import Johnson.IMR.BackSeat
import Johnson.IMR.K2ShareAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K9
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem front_len (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : (frontOf c).length = 353 := by
  unfold frontOf
  rw [List.length_cons, (IM.links_flat_352 hS hR O).2]

/-- **FROM IN FRONT OF THE HEAD's LINK's CLOSING TO IN FRONT OF THE FINISH.** -/
theorem tail_frame_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₃ R₂ : List Fmt.RoundView} {C C₃ C₂ : List VerifiableInference.Desc.OpenedColumn} {s t₂ : S}
    (g3 : foldBlocks 0 (c.blocksInOrder.take 350) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (L : LinkCtx) (Q : Close.Par) (rs : List Fmt.RoundView) (y : ReqFrame × Statement),
      s.link? = some L ∧ L.link = 24 ∧
      Close.closeFrame (K9.recOf s).owed L.check.frame s.st (Close.entries Q) rs = .ok y ∧
      t₂.check.frame = y.1 := by
  obtain ⟨L, hL, eLn, -⟩ := group_head hS hR O 10 (by omega) s R₃ C₃ g3
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  obtain ⟨s4, r4, q4, g4⟩ := fold_cut (k := 351) 2 f₂
  obtain ⟨s5, r5, q5, g5⟩ := fold_cut (k := 352) 1 f₂
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  -- the closing
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : 24 < 25) eL e1
  rw [hlen, show 14 * 24 + 9 + 4 + 1 = 350 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g3 g4
  have dx : x.retype.decide s rs gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s s4 rs gs).1 d).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL
  -- the shutting
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5 := IM.close_numbers hS hR O (by omega : 24 < 25) eL e15
  rw [hlen, show 14 * 24 + 9 + 4 + 2 = 351 by omega] at ib5
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L5, hL5, e5, -⟩ := shut_gby (fun f => f) (C := Unit) pw (Q.piece + 1) s4 rs5 gs5 s5 dx5
    _ hl4
  have e5' : L5.check.frame = y.1 := e5
  -- "cleared"
  have iC' : c.blocksInOrder[352]? = some bC := by
    rw [show 352 = 14 * 24 + 9 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 f₂
  rw [dC] at d6
  have k6 := framesOf_clear hfs f (List.mem_of_getElem? hf) s5 t₂ ((hClear s5 t₂).1 d6).1
  exact ⟨L, Q, rs, y, hL, eLn, hy', by rw [k6.1, live_open hL5, e5']⟩

/-- At the cut 353 the walk's frame's link is 25. -/
theorem fin_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.check.frame.link = 25 := by
  obtain ⟨s, R₃, C₃, g3⟩ := fold_cut (k := 350) 3 f₂
  obtain ⟨L, Q, rs, y, hL, -, hy, ef⟩ := tail_frame_head hS hR O g3 f₂
  obtain ⟨n₀, n₄, n₆, f, H, -, lk, -, -⟩ := walk_head hS hR O (n := 10) (by omega) g3
  obtain ⟨L', hL', e1, -⟩ := H.link
  obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
  obtain ⟨G, rows, -, -, ey⟩ := Close.closeFrame_lays (f' := y.1) (S' := y.2) hy
  rw [ef, ey, e1]
  show (headF f n₄ n₆ 10).link + 1 = 25
  have : (headF f n₄ n₆ 10).link = f.link := by
    unfold headF
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [this, lk]

/-- **THE FRONT AT THE FINISH.** t': the state behind the quiet step "F.0.front". -/
theorem front_pin_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ t' : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (h : K2.finishFrontQ t₂ = .ok t') {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hf : K2.frontAt q t' = some fx) :
    fx.st.codes = Z.first.codes ∧ fx.st.oracles = t₂.st.oracles ∧
      fx.T = K2.targetAt Z.first.shape 25 ∧
      fx.others = #[foldMaskNotice ((K2.frameAtLink Z.first.shape 25).foldShape 25 {})] ∧
      fx.f.link = 25 ∧
      fx.f.rows.code = Z.first.shape.code ∧ fx.f.rows.maskCode = Z.first.shape.maskCode ∧
      fx.f.rows.masks = 2 := by
  have hk := fin_link hS hR O f₂
  have Rr : RecAll Z.first.codes Z.first.shape t₂ := open_recAll hS hR O (by decide)
    (by rw [front_len hS hR O]) f₂
  obtain ⟨-, -, -, eo, -⟩ := fin_front h hq hf
  obtain ⟨a, G, ha, hG, hg, Fa, Rt⟩ := finishFrontQ_group h Rr
  obtain ⟨G', x, s₁, a', k⟩ := (K2.finishFrontQ_iff t₂ t').1 h
  obtain ⟨G₁, S', g, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  have hal : a.fr.link = 25 := by
    have e : t'.here = .fin { a' with G := some G', fr := x.f } := by rw [k.out]
    rw [ha] at e
    injection e with e
    rw [e]
    show x.f.link = 25
    rw [fa.out]
    exact hk
  obtain ⟨r1, r2, r3⟩ := rows_of_pub Fa (by rw [hal]; decide)
  unfold K2.frontAt at hf
  rw [hq, ha] at hf
  have hf' : a.G.map (fun G => K2.finFrontOf t' a G) = some fx := hf
  rw [hG] at hf'
  obtain rfl : K2.finFrontOf t' a G = fx := Option.some.inj hf'
  refine ⟨Rt.codes, eo, ?_, ?_, hal, r1, r2, r3⟩
  · show G.target = _
    unfold K2.targetAt
    rw [hk] at hg
    rw [Array.getD_eq_getD_getElem?, hg]
    rfl
  · show #[foldMaskNotice (a.fr.foldShape a.fr.link {})] = _
    rw [hal, K2.foldShape_pub Fa 25]

end

#print axioms front_len
#print axioms tail_frame_head
#print axioms fin_link
#print axioms front_pin_fin

end Meaning.K2
