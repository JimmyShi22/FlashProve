-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FinKept.lean: THE FINISH KEEPS NO OLD MESSAGE: A LAW WITH ONE NAMED
PREMISE (the public shape is the written one): at the proof file's seat, in the goals' scope.
  flagsHead sh: the flags of what "H:2" lays into group 24, of the shape: false, the target's "kept
    again", "life > 0" of the head's link's messages of moment 0.
  flags_head_false, olds_fin: THE CLOSED HALF, by Lean's kernel, at the written shape: these flags
    are all false; oldsAt 25 = [].
  tail_rows_head: from in front of the batching of the head's link (the cut 347) to in front of the
    finish (the cut 353): with L the open link and G the statement's group number 24: the walk's
    frame's carried rows' layout has G's members and flags (Johnson/IMR/GroupTail.lean's tail_rows
      at
    l = 24, where no "laid" follows).
  at_head_entry: Johnson/IMR/FrameAt.lean's At and Below behind "H:2" (the cut 340), with the
    frame's moment,
    link, group and shape: Johnson/IMR/HeadFill.lean's head_holds joined to
      Johnson/IMR/FrameAll.lean's
    entry_head_frame.
  step_at24, at_head: At at the cut 347, in front of the head's link's batching: the flags are those
    that "H:2" lays, then the flags of the frame's moments 1 and 2.
  olds_at_fin: THE TOP: at the front fx that K2.frontAt makes of the state behind the quiet step
    "F.0.front" at the cut 353: (switchKept fx.f.rows).toList = oldsAt 25 (= []).
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FinCount
import Johnson.IMR.FlagsAt
import Johnson.IMR.FrameAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile (Cl)

/-- The flags of what "H:2" lays into group 24. -/
def flagsHead (sh : ReqShape) : List Bool :=
  false :: (K2.targetAt sh 24).kept.toList.map (·.keptAgain) ++
    ((K2.frameAtLink sh 24).atMoment 0).map fun m => decide (0 < m.life)

set_option maxRecDepth 1000000 in
theorem flags_head_false : ((flagsHead proofSizedFull.request).all fun b => !b) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem olds_fin : K2.oldsAt 25 = [] := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **FROM IN FRONT OF THE BATCHING OF THE HEAD's LINK TO IN FRONT OF THE FINISH.** -/
theorem tail_rows_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Ru R₂ : List Fmt.RoundView} {C Cu C₂ : List VerifiableInference.Desc.OpenedColumn} {u t₂ : S}
    (fu : foldBlocks 0 (c.blocksInOrder.take 347) (ProofFile.startS Z p) R C = .ok (u, Ru, Cu))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ L G, u.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24 ∧
      u.st.groups[24]? = some G ∧
      t₂.check.frame.rows.layout.members = G.members ∧
      t₂.check.frame.rows.layout.kept = G.kept := by
  obtain ⟨L, hL, eLn, eLg⟩ := group_head hS hR O 7 (by omega) u Ru Cu fu
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  have cut : ∀ n ≤ 6, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (347 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 347 + n) (6 - n)
      (by rw [show 347 + n + (6 - n) = 353 by omega]; exact f₂)
  have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
    intro b₁ e1
    have i1 : c.blocksInOrder[339]? = some b₁ := by
      have q := IM.hear_at_flat eL e1
      rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1).trans
        (by omega : 14 * 24 + 1 + 2 = 339)] at q
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 340) 7 fu
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 339) f₁
    obtain ⟨rs0, gs0, d0⟩ := fold_next i1 f₀ f₁
    exact ⟨_, _, _, _, d0⟩
  have hruns := hear_runs24 tl_refl tl_trans (fun _ _ => tl_of_quiet) hS hR O eL hy
  have blk : ∀ n ≤ 5, ∃ b, c.blocksInOrder[347 + n]? = some b := fun n hn =>
    ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 iC).1
      omega)⟩
  have step : ∀ n ≤ 4, ∀ t r q t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (347 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (347 + (n + 1))) (ProofFile.startS Z p) R C = .ok (t', r', q') →
      Tl t t' := by
    intro n hn t r q t' r' q' g g'
    obtain ⟨b, ib⟩ := blk n (by omega)
    obtain ⟨rs, gs, d⟩ := fold_next ib g g'
    exact rest_of_runs tl_refl tl_trans (fun p _ hcl => batch_tl p hcl) closeOf_tl hS hR O
      (by omega : 24 < 25) eL hruns hn
      (by rw [hlen, show 14 * 24 + 9 + 2 + n = 347 + n by omega]; exact ib) t rs gs t' d
  obtain ⟨s1, r1, q1, g1⟩ := cut 1 (by omega)
  obtain ⟨s2, r2, q2, g2⟩ := cut 2 (by omega)
  obtain ⟨s3, r3, q3, g3⟩ := cut 3 (by omega)
  obtain ⟨s4, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨s5, r5, q5, g5⟩ := cut 5 (by omega)
  have T03 : Tl u s3 := tl_trans _ _ _ (tl_trans _ _ _ (step 0 (by omega) u Ru Cu s1 r1 q1 fu g1)
    (step 1 (by omega) s1 r1 q1 s2 r2 q2 g1 g2)) (step 2 (by omega) s2 r2 q2 s3 r3 q3 g2 g3)
  -- the closing, by itself
  obtain ⟨L3, hL3, e3, n3⟩ := T03.2 L hL
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : 24 < 25) eL e1
  rw [hlen, show 14 * 24 + 9 + 4 + 1 = 347 + 3 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g3 g4
  have dx : x.retype.decide s3 rs gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s3 s4 rs gs).1 d).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL3
  obtain ⟨-, -, G3, hG3, m1, m2⟩ := Close.closeFrame_groups hy'
  have eg3 : L3.check.frame.group = 24 := by
    have := congrArg (fun z => z.2.2) e3
    exact this.trans eLg
  rw [eg3] at hG3
  have pr := T03.1.2 24
  rw [hG3] at pr
  obtain ⟨G, hG, eG⟩ := Option.map_eq_some_iff.1 pr.symm
  have eGm : G.members = G3.members := congrArg Prod.fst eG
  have eGk : G.kept = G3.kept := congrArg Prod.snd eG
  -- the shutting; "cleared"
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5 := IM.close_numbers hS hR O (by omega : 24 < 25) eL e15
  rw [hlen, show 14 * 24 + 9 + 4 + 2 = 347 + 4 by omega] at ib5
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L5, hL5, e5, -⟩ := shut_gby (fun f => f) (C := Unit) pw (Q.piece + 1) s4 rs5 gs5 s5 dx5
    _ hl4
  have e5' : L5.check.frame = y.1 := e5
  have iC' : c.blocksInOrder[347 + 5]? = some bC := by
    rw [show 347 + 5 = 14 * 24 + 9 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 f₂
  rw [dC] at d6
  have k6 := framesOf_clear hfs f (List.mem_of_getElem? hf) s5 t₂ ((hClear s5 t₂).1 d6).1
  have ef : t₂.check.frame = y.1 := by rw [k6.1, live_open hL5, e5']
  exact ⟨L, G, hL, eLn, eLg, hG, by rw [ef, m1, eGm], by rw [ef, m2, eGk]⟩

/-- **BEHIND "H:2".** -/
theorem at_head_entry (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ f : ReqFrame, At 24 #[t₀.st.oracles.size] (flagsHead Z.first.shape) f t₁ ∧ Below 24 t₁ ∧
      f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.shape = Z.first.shape := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  obtain ⟨x, a, hx, ha, -, -, -⟩ := h1_front (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨G, f, hG, hk, ⟨L, hL, eLf, eLn⟩, mo, lk, gp, -, sh, kb, ow⟩ :=
    entry_head_frame hS hR O f₀ f₁
  have hfx : K2.frontAt headQ t₀ = some (K2.headFrontOf t₀ a G.target) := by
    unfold K2.frontAt
    rw [show headQ.stands = .head from rfl, ha, hk, hG]
    rfl
  have Hh := head_holds hS hR O f₀ f₁ rfl hfx
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide)
    (by have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide); omega) f₀
  obtain ⟨-, -, eT, -⟩ := front_pin_head hS hR O f₀ rfl hfx
  have eT' : G.target = K2.targetAt Z.first.shape 24 := eT
  have em : ((K2.switchGain (K2.headFrontOf t₀ a G.target) ++
      K2.ownGain (K2.headFrontOf t₀ a G.target)).map (·.1)).toArray =
      #[t₀.st.oracles.size] ++ L.check.frame.keptBefore ++ L.check.frame.own := by
    rw [eLf, kb, ow, gain_fst]
    apply Array.toList_inj.1
    simp [K2.headFrontOf]
  obtain ⟨a1, a2⟩ := at_of_holds Hh hL eLn em
  rw [eLf, gain_snd] at a1
  have efl : (false :: (K2.headFrontOf t₀ a G.target).T.kept.toList.map (·.keptAgain) ++
      (K2.headFrontOf t₀ a G.target).own.map fun m => decide (0 < m.life)) =
      flagsHead Z.first.shape := by
    show (false :: G.target.kept.toList.map (·.keptAgain) ++
      (t₀.check.frame.atMoment 0).map fun m => decide (0 < m.life)) = _
    rw [eT', K2.atMoment_pub Rr.walk hk 0]
    rfl
  rw [efl] at a1
  exact ⟨f, a1, a2, mo, lk, gp, sh.trans Rr.walk.shape⟩

/-- Over a later sending's sub-protocol of the head's link: the frame and the group. -/
theorem step_at24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 4 ∨ j = 6) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (338 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (338 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (hg : f.group = 24)
    (H : At 24 pre fl f s) (B : Below 24 s) :
    At 24 pre (fl ++ K1.flagsAt f) (laterF f s.st.oracles.size) s' ∧ Below 24 s' := by
  obtain ⟨Lk, eL, -, hA⟩ := hear_flat24 hS hR O
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ24 hS hR O hj eL e d'
  obtain ⟨a1, a2⟩ := at_commit cm hg H B
  exact ⟨at_quiet qv a1, below_quiet qv a2⟩

/-- **IN FRONT OF THE BATCHING OF THE HEAD's LINK**: every flag of group 24 is one that "H:2" lays
or one of the frame's moments 1 and 2. -/
theorem at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Ru : List Fmt.RoundView} {C Cu : List VerifiableInference.Desc.OpenedColumn} {u : S}
    (fu : foldBlocks 0 (c.blocksInOrder.take 347) (ProofFile.startS Z p) R C = .ok (u, Ru, Cu)) :
    ∃ (pre : Array Nat) (f f' f'' : ReqFrame),
      At 24 pre (flagsHead Z.first.shape ++ K1.flagsAt f ++ K1.flagsAt f') f'' u ∧
      f.shape = Z.first.shape ∧ f.moment = 1 ∧ f'.shape = Z.first.shape ∧ f'.moment = 2 := by
  have cut : ∀ n ≤ 8, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (339 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 339 + n) (8 - n)
      (by rw [show 339 + n + (8 - n) = 347 by omega]; exact fu)
  obtain ⟨t₀, r0, q0, g0⟩ := cut 0 (by omega)
  obtain ⟨t₁, r1, q1, g1⟩ := cut 1 (by omega)
  obtain ⟨t₂, r2, q2, g2⟩ := cut 2 (by omega)
  obtain ⟨t₃, r3, q3, g3⟩ := cut 3 (by omega)
  obtain ⟨t₄, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨t₅, r5, q5, g5⟩ := cut 5 (by omega)
  obtain ⟨t₆, r6, q6, g6⟩ := cut 6 (by omega)
  obtain ⟨t₇, r7, q7, g7⟩ := cut 7 (by omega)
  obtain ⟨f, a1, b1, mo, lk, gp, sh⟩ := at_head_entry hS hR O g0 g1
  have k2 := step_quiet24 hS hR O (j := 2) (by omega) g1 g2
  have k3 := step_quiet24 hS hR O (j := 3) (by omega) g2 g3
  obtain ⟨a4, b4⟩ := step_at24 hS hR O (j := 4) (Or.inl rfl) g3 g4 gp
    (at_quiet k3 (at_quiet k2 a1)) (below_quiet k3 (below_quiet k2 b1))
  have k5 := step_quiet24 hS hR O (j := 5) (by omega) g4 g5
  obtain ⟨a6, -⟩ := step_at24 hS hR O (j := 6) (Or.inr rfl) g5 g6
    (f := laterF f t₃.st.oracles.size) gp (at_quiet k5 a4) (below_quiet k5 b4)
  have k7 := step_quiet24 hS hR O (j := 7) (by omega) g6 g7
  have k8 := step_quiet24 hS hR O (j := 8) (by omega) g7 fu
  refine ⟨_, f, laterF f t₃.st.oracles.size, _, at_quiet k8 (at_quiet k7 a6), sh, mo, sh, ?_⟩
  show f.moment + 1 = 2
  rw [mo]

/-- **THE FINISH KEEPS NO OLD MESSAGE.** t': the state behind the quiet step "F.0.front". -/
theorem olds_at_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = proofSizedFull.request) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ t' : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (h : K2.finishFrontQ t₂ = .ok t') {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hf : K2.frontAt q t' = some fx) :
    (switchKept fx.f.rows).toList = K2.oldsAt 25 := by
  obtain ⟨-, -, er, -⟩ := front_nums_fin hS hR O f₂ h hq hf
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 347) 6 f₂
  obtain ⟨L, G, -, -, -, hG, m1, m2⟩ := tail_rows_head hS hR O fu f₂
  obtain ⟨pre, f, f', f'', Ha, s1, mo1, s2, mo2⟩ := at_head hS hR O fu
  obtain ⟨G', hG', -, ek, -, -⟩ := Ha.group
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut (k := 339) 8 fu
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide)
    (by have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide); omega) f₀
  have F1 := flags_false Rr.ok s1 (by omega : 1 ≤ f.moment)
  have F2 := flags_false Rr.ok s2 (by omega : 1 ≤ f'.moment)
  have F0 : ∀ b ∈ flagsHead Z.first.shape, b = false := by
    intro b hb
    rw [hsh] at hb
    simpa using List.all_eq_true.1 flags_head_false b hb
  have hk : keptOf G.members
      (flagsHead Z.first.shape ++ K1.flagsAt f ++ K1.flagsAt f').toArray = #[] := by
    refine keptOf_none fun b hb => ?_
    have hb' : b ∈ flagsHead Z.first.shape ++ K1.flagsAt f ++ K1.flagsAt f' := by simpa using hb
    rcases List.mem_append.1 hb' with k | k
    · rcases List.mem_append.1 k with k | k
      · exact F0 b k
      · exact F1 b k
    · exact F2 b k
  rw [er, switchKept_eq, m1, m2, ek, hk, olds_fin]

end

#print axioms flags_head_false
#print axioms olds_fin
#print axioms tail_rows_head
#print axioms at_head_entry
#print axioms at_head
#print axioms olds_at_fin

end Meaning.K2
