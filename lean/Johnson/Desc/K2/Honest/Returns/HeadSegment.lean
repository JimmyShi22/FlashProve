-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/HeadSegment.lean: WHAT Returns/SeatsWalk.lean AND
Returns/SendCounts.lean HAVE AT THE SEGMENTS 1 TO 23, AT THE LAST SEGMENT (NUMBER 24, THE OUTPUT
HEAD's): THE MESSAGES THAT THE PLACE BEHIND THE LAST SEGMENT OPENS, AS NUMBERS, AND HOW MANY
MESSAGES EACH OF THE SEGMENT's THREE SENDINGS ADDS. In the goals' scope, from the returns of one
fold. A tool for `ReadFits.own` behind the last segment. Statements with their proofs: calls.

  `closing_behind_cleared` from the fold's return at 353: the state w of the same fold at 350, the
                    segment Lw that is open there, and a yes of the frame's closing at Lw's own
                    frame and w's own statement. `closed_behind_cleared` (Returns/ClosedArms.lean)
                    says it with "there are a frame and a statement": ITS PROOF STANDS HERE AGAIN,
                    LINE FOR LINE, COPIED BY PROGRAM, WITH THE STATEMENT STRENGTHENED
  `fresh_behind_cleared` the carried rows' fresh mask at 353, counted from the count n₀ at 339
  `h2_count`, `entry_count_head` ON THE TEXT and AT THE SEAT: over the output head's switch (339 to
                    340): one carrying message, the kept copies, the own messages of moment 0, one
                    fresh mask
  `step_count24` over hearing sub-protocol number 4 or 6 of the segment (342 to 343, 344 to 345)
  `members_behind_cleared` the carried rows' layout's members at 353, AS RANGES off the counts at
                    339, 342, 344: what the library's Johnson/IMR/FlagsNamed.lean names in its head
                    as not claimed at this segment
  `counts_head` the three sendings together

By, all the library's: what `closed_behind_cleared` calls · `closeFrame_reads`
(Johnson/Desc/First/Link/Law/CloseReads.lean) · `mask_head_named` (Johnson/IMR/MaskHeadNamed.lean) ·
`tail_rows_head` (Johnson/IMR/FinKept.lean) · `members_head_named` (Johnson/IMR/FlagsNamed.lean) ·
`entry_head_frame`, `frame_walk_head`, `hear_flat24`, `hear_commitQ24`, `h1_fr`
(Johnson/IMR/FrameAll.lean) · `k2_head_of` (Johnson/IMR/K2Seat.lean), `k7_sits`, `k7_sits_yes`
(Johnson/IMR/FirstSeats.lean) · `yes_alone` (Johnson/IMR/SeatForm.lean) · `yes_size`,
`headOpenQ_size` (Johnson/Top/H0/Tw/K2C/StillKeeps.lean) · `link_inv`
(Johnson/Top/H0/Tw/K2C/Closed.lean) · `front_pin_head` (Johnson/IMR/FrontPin.lean) · `open_recAll`
(Johnson/IMR/ListsEnds.lean), `atMoment_of` (Johnson/IMR/FlagsAt.lean) · `frontAt_of`
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean), `headQ` (Johnson/IMR/FinCount.lean). This folder's
`commit_count` (Returns/SendCounts.lean). `h2_count`'s walk over the place's forms is the library's
`h2_frame`'s (Johnson/IMR/FrameAll.lean), retyped.

Limits. That a fold returns is shown of no proof here. The walk over the seats stands typed a
seventh time in this folder. This file's imports are heavy. Nothing on any property.




-/
import Johnson.Desc.K2.Honest.Returns.ClosedArms
import Johnson.Desc.K2.Honest.Returns.SendCounts
import Johnson.IMR.MaskHeadNamed
import Johnson.Desc.First.Link.Law.CloseReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Model (LinkCtx)
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Close (closeFrame)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open Meaning.K2 (Opn laterF seqF frame_walk_head entry_head_frame framesOf_clear framesOf_grows
  closing_yes shutting_opn andThen_yes fold_back fold_next fold_cut mask_head_named
  tail_rows_head members_head_named hear_flat24 hear_commitQ24 h1_fr front_pin_head open_recAll
  front_len atMoment_of msgsAt headQ)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind "cleared" of the last segment, with the state in front of the closing named.** -/
theorem closing_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (w : S) (Rw : List Fmt.RoundView) (Cw : List VerifiableInference.Desc.OpenedColumn) (Lw : LinkCtx)
      (Q : First.Close.Par) (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      foldBlocks 0 (c.blocksInOrder.take 350) (ProofFile.startS Z p) R C = .ok (w, Rw, Cw) ∧
      w.link? = some Lw ∧ Lw.link = 24 ∧
      closeFrame (K9.recOf w).owed Lw.check.frame w.st (First.Close.entries Q) rs = .ok x ∧
      t₀.check.frame = x.1 ∧ Grows x.2 t₀.st := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  -- "the last segment: cleared"
  obtain ⟨Lk, g, _, _, bC, eL, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 352) f₀
  obtain ⟨rsC, gsC, dc⟩ := fold_next (k := 352) iC fu f₀
  rw [dC] at dc
  have hcf := ((hclr u t₀).1 dc).1
  have hck := (framesOf_clear hfs g (List.mem_of_getElem? hg) u t₀ hcf).1
  have hgr : Grows u.st t₀.st := (framesOf_grows hfs g (List.mem_of_getElem? hg)).2.2 u t₀ hcf
  -- the shutting and the closing
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have j₂ := IM.close_numbers hS hR O (by omega : 24 < 25) eL a1
  have i₂ := j₂
  rw [hlen] at i₂
  rw [show 14 * 24 + Lk.hear.length + 4 + 2 = 14 * 24 + Lk.hear.length + 6 by omega] at j₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 351) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next (k := 351) i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have est := shut_st (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : 24 < 25) eL c1
  rw [hlen] at i₁
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 350) fv
  obtain ⟨rs₁, gs₁, d₁⟩ := fold_next (k := 350) i₁ fw fv
  have dx₁ : x₁.retype.decide w rs₁ gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v rs₁ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  -- in front of the closing the segment is open
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) 10 fw
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
  obtain ⟨t₃, r₃, c₃, g₃⟩ := fold_cut (k := 340 + 2) 8 fw
  obtain ⟨t₅, r₅, c₅, g₅⟩ := fold_cut (k := 340 + 4) 6 fw
  obtain ⟨_, f', -, -, H, -⟩ := entry_head_frame hS hR O f₁ f₂
  obtain ⟨Lw, hLw, -, hLl⟩ := (frame_walk_head hS hR O (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₂ H).1 10 (by omega) w Rw Cw fw
  obtain ⟨x, hx, hv, hvst⟩ := closing_yes (C := Unit) dx₁ hLw
  have Hv : Opn 24 x.1 v := ⟨_, hv, rfl, hLl⟩
  obtain ⟨Lu, hLu, hLuf, -⟩ := shutting_opn hS hR O (by omega : 24 < 25) eL j₂ d₂ Hv
  refine ⟨w, Rw, Cw, Lw, Q, rs₁, x, fw, hLw, hLl, hx, ?_, ?_⟩
  · rw [hck]
    unfold S.live
    rw [hLu]
    exact hLuf
  · rw [← hvst, ← est]
    exact hgr

/-- **The fresh mask that the place behind the last segment opens, as a number.** -/
theorem fresh_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ Ra : List Fmt.RoundView} {C C₂ Ca : List VerifiableInference.Desc.OpenedColumn}
    {t₂ ta : S}
    (fa : foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (ta, Ra, Ca))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.check.frame.rows.fresh =
      ta.st.oracles.size + (1 + (First.K2.targetAt Z.first.shape 24).kept.size) +
        msgsAt Z.first.shape 24 0 := by
  obtain ⟨w, Rw, Cw, Lw, Q, rs, x, fw, hLw, -, hx, hf, -⟩ := closing_behind_cleared hS hR O f₂
  obtain ⟨_, m, -, -, hm, hfr⟩ := closeFrame_reads hx
  obtain ⟨t₀, R₀, C₀, L, g₀, hL, -, hmask⟩ := mask_head_named hS hR O (n := 10) (by omega) fw
  obtain rfl : t₀ = ta := congrArg Prod.fst (Except.ok.inj (g₀.symm.trans fa))
  obtain rfl : L = Lw := Option.some.inj (hL.symm.trans hLw)
  rw [hf, hfr]
  exact Option.some.inj (hm.symm.trans hmask)

/-- **On the text: over the output head's switch.** -/
theorem h2_count {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ G : ReqGroup, s.check.frame.groups[s.check.frame.link]? = some G ∧
      t.st.oracles.size = s.st.oracles.size +
        (1 + G.target.kept.size + ((s.check.frame.atMoment 0).length + 1)) := by
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨w, a1, a2⟩ := andThen_yes (n := x.name) h
      have a1' : First.K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) s _ _ =
          .ok w := a1
      have a2' : First.K2.headOpenQ HP w = .ok t := a2
      obtain ⟨x', hF, e1, -, e2, -⟩ := First.K2.yes_size a1'
      rcases hF with ⟨k, -⟩ | ⟨-, a', G, -, hG, rfl⟩ | ⟨k, -⟩
      · cases k
      · refine ⟨G, hG, ?_⟩
        rw [First.K2.headOpenQ_size a2', e2, e1]
        simp [_root_.Tw.K2.switchNotices, First.K2.headFrontOf, ReqFrame.notices]
        omega
      · cases k
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        First.K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **At the seat: over the output head's switch.** -/
theorem entry_count_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List VerifiableInference.Desc.OpenedColumn}
    {t₁ t₂ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (340)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.st.oracles.size = t₁.st.oracles.size +
      (1 + (First.K2.targetAt Z.first.shape 24).kept.size + (msgsAt Z.first.shape 24 0 + 1)) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
  obtain ⟨Lk, b0, eL, e0, J, -⟩ := IM.k7_sits hS hR O
  obtain ⟨Lk', b1, x, eL', e1, -, la, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have q := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have q := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨a, ha, -⟩ := h1_fr (IM.k7_sits_yes hS hR O J d0).1
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  obtain ⟨G, hG, hc⟩ :=
    h2_count hx ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1 ha
  have Rr := open_recAll hS hR O (by omega : 2 ≤ 339) (by rw [front_len hS hR O]; omega) f₁
  have hfx : First.K2.frontAt headQ t₁ = some (First.K2.headFrontOf t₁ a G.target) :=
    First.K2.frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, ha, hG, rfl⟩))
  obtain ⟨-, -, eT, -, hk, -⟩ := front_pin_head hS hR O f₁ rfl hfx
  have eT' : G.target = First.K2.targetAt Z.first.shape 24 := eT
  obtain ⟨-, -, -, hk1, -⟩ := entry_head_frame hS hR O f₁ f₂
  rw [hc, eT', atMoment_of Rr.walk.shape hk1]
  rfl

/-- **At the seat: over a later sending's sub-protocol of the last segment.** -/
theorem step_count24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 4 ∨ j = 6) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (338 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (338 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {f : ReqFrame} (H : Opn 24 f s) :
    s'.st.oracles.size = s.st.oracles.size + (f.atMoment f.moment).length := by
  obtain ⟨Lk, eL, -, hA⟩ := hear_flat24 hS hR O
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ24 hS hR O hj eL e d'
  obtain ⟨L, hL, e1, -⟩ := H
  rw [qv.1.1, commit_count cm hL, e1]

/-- **The members that the place behind the last segment opens, as ranges.** -/
theorem members_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (t₀ t₃ t₅ : S) (R₀ R₃ R₅ : List Fmt.RoundView) (C₀ C₃ C₅ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      foldBlocks 0 (c.blocksInOrder.take (342)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) ∧
      foldBlocks 0 (c.blocksInOrder.take (344)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅) ∧
      t₂.check.frame.rows.layout.members = #[t₀.st.oracles.size] ++
        (Array.range (First.K2.targetAt Z.first.shape 24).kept.size).map
          (· + (t₀.st.oracles.size + 1)) ++
        ((Array.range (msgsAt Z.first.shape 24 0)).map
            (· + (t₀.st.oracles.size + (1 + (First.K2.targetAt Z.first.shape 24).kept.size))) ++
          (Array.range (msgsAt Z.first.shape 24 1)).map (· + t₃.st.oracles.size) ++
          (Array.range (msgsAt Z.first.shape 24 2)).map (· + t₅.st.oracles.size)) := by
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 347) 6 f₂
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 340) 7 fu
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 339) f₁
  obtain ⟨t₃, R₃, C₃, g₃⟩ := fold_cut (k := 340 + 2) 5 fu
  obtain ⟨t₅, R₅, C₅, g₅⟩ := fold_cut (k := 340 + 4) 3 fu
  obtain ⟨L, G, hL, -, -, hG, hmem, -⟩ := tail_rows_head hS hR O fu f₂
  obtain ⟨t₀', R₀', C₀', L', G', g₀', hL', -, -, hG', em, -⟩ :=
    members_head_named hS hR O (n := 7) (by omega) fu
  obtain rfl : t₀ = t₀' := congrArg Prod.fst (Except.ok.inj (f₀.symm.trans g₀'))
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  obtain ⟨Gr, f, hGr, hk1, H, mo, lk, -, -, sh, kb, ow⟩ := entry_head_frame hS hR O f₀ f₁
  obtain ⟨Lu, hLu, eLu, -⟩ := (frame_walk_head hS hR O (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₁ H).1 7 (by omega) u Ru Cu fu
  obtain rfl : L' = Lu := Option.some.inj (hL'.symm.trans hLu)
  have Rr := open_recAll hS hR O (by omega : 2 ≤ 339) (by rw [front_len hS hR O]; omega) f₀
  have s1 : f.shape = Z.first.shape := sh.trans Rr.walk.shape
  have eGr : Gr.target = First.K2.targetAt Z.first.shape 24 := by
    unfold First.K2.targetAt
    rw [← Rr.walk.groups, Array.getD_eq_getD_getElem?, hGr]
    rfl
  have e7 : seqF f t₃.st.oracles.size t₅.st.oracles.size 7 =
      laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size := rfl
  refine ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, f₀, g₃, g₅, ?_⟩
  rw [hmem, em, eLu, e7]
  show #[t₀.st.oracles.size] ++ f.keptBefore ++
      (f.own ++ (Array.range (f.atMoment f.moment).length).map (· + t₃.st.oracles.size) ++
        (Array.range ((laterF f t₃.st.oracles.size).atMoment
          (laterF f t₃.st.oracles.size).moment).length).map (· + t₅.st.oracles.size)) = _
  have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
    show f.moment + 1 = 2
    rw [mo]
  unfold msgsAt
  rw [m2, mo, atMoment_of s1 lk, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk, kb, ow,
    eGr, atMoment_of Rr.walk.shape hk1]

/-- **The three sendings of the last segment.** -/
theorem counts_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ R₁ R₃ R₄ R₅ R₆ : List Fmt.RoundView}
    {C C₀ C₁ C₃ C₄ C₅ C₆ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ t₃ t₄ t₅ t₆ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (340)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (342)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₄ : foldBlocks 0 (c.blocksInOrder.take (343)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (344)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    (f₆ : foldBlocks 0 (c.blocksInOrder.take (345)) (ProofFile.startS Z p) R C = .ok (t₆, R₆, C₆)) :
    t₁.st.oracles.size = t₀.st.oracles.size +
        (1 + (First.K2.targetAt Z.first.shape 24).kept.size + (msgsAt Z.first.shape 24 0 + 1)) ∧
      t₄.st.oracles.size = t₃.st.oracles.size + msgsAt Z.first.shape 24 1 ∧
      t₆.st.oracles.size = t₅.st.oracles.size + msgsAt Z.first.shape 24 2 := by
  obtain ⟨Gr, f, -, -, H, mo, lk, -, -, sh, -, -⟩ := entry_head_frame hS hR O f₀ f₁
  have Rr := open_recAll hS hR O (by omega : 2 ≤ 339) (by rw [front_len hS hR O]; omega) f₀
  have s1 : f.shape = Z.first.shape := sh.trans Rr.walk.shape
  have W := (frame_walk_head hS hR O (n₃ := t₃.st.oracles.size) (n₅ := t₅.st.oracles.size)
    (fun t r q h => by rw [f₃] at h; cases h; rfl)
    (fun t r q h => by rw [f₅] at h; cases h; rfl) f₁ H).1
  have b1 : Opn 24 f t₃ := W 2 (by omega) t₃ R₃ C₃ f₃
  have b2 : Opn 24 (laterF f t₃.st.oracles.size) t₅ := W 4 (by omega) t₅ R₅ C₅ f₅
  refine ⟨entry_count_head hS hR O f₀ f₁, ?_, ?_⟩
  · rw [step_count24 hS hR O (j := 4) (Or.inl rfl) f₃ f₄ b1, mo, atMoment_of s1 lk]
    rfl
  · rw [step_count24 hS hR O (j := 6) (Or.inr rfl) f₅ f₆ b2]
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    rw [m2, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk]
    rfl

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.closing_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fresh_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.h2_count
#print axioms VerifiableInference.Desc.K2.Honest.Returns.entry_count_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.step_count24
#print axioms VerifiableInference.Desc.K2.Honest.Returns.members_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.counts_head
