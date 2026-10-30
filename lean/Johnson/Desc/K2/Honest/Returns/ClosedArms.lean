-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ClosedArms.lean: THE BRIDGE OF Returns/ClosedReached.lean AT THE TWO
OTHER SORTS OF PLACE OF A SWITCH: AT A STATE REACHED IN FRONT OF THE OUTPUT HEAD's SWITCH (NUMBER
339), AND BEHIND THE QUIET FRONT OF THE PLACE BEHIND THE LAST SEGMENT (NUMBER 353), THE FRAME THAT
THE SWITCH's FRONT READS CARRIES THE ROWS THAT THE LAST CLOSING RETURNED, AND THE STATEMENT HAS
GROWN OUT OF THE CLOSING's. SO, WITH NO TEST ON THE PUBLIC PART, AT BOTH FRONTS: the eight of
`ReadFits` on the layout · `OldFits.rows` · `named` · `TablesFit.claimKept`. Statements with their
proofs: calls; two proofs of the library's typed again with another clause.

  `headFrontQ_rows`, `finishFrontQ_rows` the two quiet fronts lay the walk's carried rows into the
                    frame of their own: THE LIBRARY's `headFrontQ_fr`
                    (Johnson/Top/H0/Tw/K2C/HeadLink.lean) and `finishFrontQ_fr`
                    (Johnson/Top/H0/Tw/K2C/FinFront.lean) tell other fields by the same first lines
  `grows_fresh` a statement with a fresh group pushed has grown out of the statement
  `closed_behind_cleared` THE BRIDGE BEHIND THE LAST SEGMENT, from the fold's return at the cut 353:
                    `closed_behind_laid`'s walk at segment 24, which has nine hearing sub-protocols
                    and no "laid" behind it
  `head_closed_reached` at 339, under `s.here = .head a`: `a.fr.rows` is what the closing of segment
                    23 returned: `closed_behind_laid` at the cut 338, then across the place that
                    hears the reply
  `fin_closed_reached` at 353, behind the quiet front's yes, under `t.here = .fin a`: the like
  `head_lay_reached`, `fin_lay_reached` `LayFits` at the two fronts
  `head_members_reached`, `fin_members_reached` `rows`, `named`, `claimKept` at the two fronts, each
                    in its structure's own letters

By, all the library's: `headFrontQ_iff`, `finishFrontQ_iff`, `firstFront_iff`, `finishFront_iff`
(Johnson/Top/H0/Tw/K2C/Asks.lean) · `headFrontQ_st` (Johnson/Top/H0/Tw/K2C/FrontGroup.lean) ·
`finishFrontQ_st` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `frame_of` (Johnson/IMR/FrameSeat.lean) ·
`close_of` (Johnson/IMR/CloseSeat.lean) · `close_numbers`, `k7_sits`, `k7_sits_yes`
(Johnson/IMR/FirstSeats.lean) · `yes_alone` (Johnson/IMR/SeatForm.lean) · `flatIx_scope`
(Johnson/IMR/FlatScope.lean) · `hear_at_flat` (Johnson/IMR/FlatIx.lean) · `framesOf_clear`,
`closing_yes` (Johnson/IMR/GroupTail.lean) · `framesOf_grows`
(Johnson/Goal/Meaning/GrowsSeated.lean) · `shutting_opn`, `frame_walk_head`, `entry_head_frame`
(Johnson/IMR/FrameAll.lean) · `andThen_yes`, `fold_back`, `fold_next` (Johnson/IMR/FoldTools.lean) ·
`fold_cut` (Johnson/IMR/GroupRest.lean) · `guarded_yes` (Johnson/Desc/Sound/SeatGuardLaws.lean) ·
`reply_record` (Johnson/Desc/Kinds/Law/ReplyPins.lean) · `reach_raw`, `Reach.fold`
(Johnson/Top/H0/Walk/Reach.lean). Near relatives, not called: `front_nums_head`
(Johnson/IMR/HeadFront.lean): from the fold's returns at the cuts 338 and 339, at a front that the
head's place reads: its carried rows are the walk's at 338, and its group is 24:
`head_closed_reached`'s step across the place that hears the reply, under one look-up more ·
`frame_at_head` (Johnson/P1K2R/FencesReached.lean), `h1_headFr` (Johnson/IMR/ListsEnds.lean),
`h1_check` (Johnson/IMR/FrontPin.lean): the same seat at 338, read for other fields; their lines on
it stand here again · `finishFrontQ_keeps` (Johnson/Top/H0/Tw/K2C/SendsOn.lean) at "grows":
`grows_fresh` behind `finishFrontQ_st`, by another road.

Limits. `here` is a premise at both places, the quiet front's yes at the second; at 339
`head_here_reached` (Returns/LinkReached.lean) has "there is an a". `OldFits.mainVars`, `d0`, `d1`,
`ReadFits.placed`, `stated`, and "no count of rows waits" at these two places: not typed here.
"Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any property.




-/
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.P1K2R.FencesReached
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Top.H0.Tw.K2C.SendsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows GroupGrows OracleGrows
  guarded_yes)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontQ finishFrontQ headFrontQ_iff finishFrontQ_iff
  headFrontQ_st finishFrontQ_st withFresh headFrontOf finFrontOf)
open VerifiableInference.Desc.First.Close (closeFrame)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (Opn frame_walk_head entry_head_frame framesOf_clear framesOf_grows closing_yes
  shutting_opn andThen_yes fold_back fold_next fold_cut)
open ProofFile (Cl)

/-! ## The two quiet fronts keep the carried rows -/

/-- The head's quiet front lays the walk's carried rows into the head's own frame. THE LIBRARY's
`headFrontQ_fr` (Johnson/Top/H0/Tw/K2C/HeadLink.lean) tells six other fields by the same lines. -/
theorem headFrontQ_rows {tl : OnBytes.Model.HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    ∃ a, s'.here = .head a ∧ a.fr.rows = s.check.frame.rows := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  obtain ⟨L, G, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.front
  refine ⟨{ a with fr := x.f }, by rw [k.out], ?_⟩
  show x.f.rows = _
  rw [fa.out]

/-- The like for the quiet front behind the last segment. -/
theorem finishFrontQ_rows {s t : S} (h : finishFrontQ s = .ok t) :
    ∃ a, t.here = .fin a ∧ a.fr.rows = s.check.frame.rows := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s t).1 h
  obtain ⟨G', S', g, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  refine ⟨{ a with G := some G, fr := x.f }, by rw [k.out], ?_⟩
  show x.f.rows = _
  rw [fa.out]

/-- A statement with a fresh group pushed has grown out of the statement. -/
theorem grows_fresh (T : Statement) (c m : Nat) : Grows T (withFresh T c m) := by
  refine ⟨rfl, fun i G hG => ⟨G, ?_, GroupGrows.refl G⟩, fun i x hx => ⟨x, hx, OracleGrows.refl x⟩⟩
  have hi := (Array.getElem?_eq_some_iff.1 hG).1
  rw [← hG]
  simp [withFresh, Array.getElem?_push, Nat.ne_of_lt hi]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-! ## The bridge behind the last segment -/

/-- **Behind "cleared" of the last segment the walk's frame is what its closing returned, and the
statement has grown out of the closing's.** -/
theorem closed_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ t₀.check.frame = x.1 ∧ Grows x.2 t₀.st := by
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
  refine ⟨_, _, _, _, _, x, hx, ?_, ?_⟩
  · rw [hck]
    unfold S.live
    rw [hLu]
    exact hLuf
  · rw [← hvst, ← est]
    exact hgr

/-! ## At the two arms' fronts -/

/-- **In front of the output head's switch the head's own frame carries what the last closing
returned.** -/
theorem head_closed_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ a.fr.rows = x.1.rows ∧ Grows x.2 s.st := by
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [ix 0] at k
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨m, a1, a2⟩ := andThen_yes d0'
  have hq : headFrontQ Bs.G₀.W.H.tl tm = .ok m :=
    ((guarded_yes _ (fun _ => false) _ rfl tm _ _ m).1 a1).1
  obtain ⟨a', ha', hrows⟩ := headFrontQ_rows hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 Bs.G₀.W.hS.V a2
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.head a' = .head a := ha'.symm.trans here
    cases e
    rfl
  obtain ⟨owed, f, S₀, es, rs', x, hx, hf, hg⟩ := closed_behind_laid hS hR O (l := 23) (by omega) fm
  refine ⟨owed, f, S₀, es, rs', x, hx, by rw [hrows, hf], ?_⟩
  show Grows x.2 m.st
  rw [headFrontQ_st hq]
  exact hg.trans (grows_fresh _ _ _)

/-- **The like behind the quiet front of the place behind the last segment.** -/
theorem fin_closed_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ a.fr.rows = x.1.rows ∧ Grows x.2 t.st := by
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  obtain ⟨a', ha', hrows⟩ := finishFrontQ_rows he
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  obtain ⟨owed, f, S₀, es, rs', x, hx, hf, hg⟩ := closed_behind_cleared hS hR O f₀
  refine ⟨owed, f, S₀, es, rs', x, hx, by rw [hrows, hf], ?_⟩
  rw [finishFrontQ_st he]
  exact hg.trans (grows_fresh _ _ _)

/-- **The eight of `ReadFits` on the layout, at the head's front.** -/
theorem head_lay_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) :
    LayFits (headFrontOf s a T).st (headFrontOf s a T).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  show LayFits s.st a.fr.rows
  rw [hf]
  exact layFits_of_close hx hg

/-- **The like at the front behind the last segment.** -/
theorem fin_lay_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) :
    LayFits (finFrontOf t a Q).st (finFrontOf t a Q).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  show LayFits t.st a.fr.rows
  rw [hf]
  exact layFits_of_close hx hg

/-- **`OldFits.rows`, `named`, `TablesFit.claimKept` at the head's front.** -/
theorem head_members_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) :
    (headFrontOf s a T).f.rows.keptRows =
        ((switchKept (headFrontOf s a T).f.rows).toList.map fun o =>
          ((headFrontOf s a T).st.oracles.getD o default).shape.mainRows).sum ∧
      (∀ k ∈ (headFrontOf s a T).f.rows.kept.toList,
        k.oracle ∈ (switchKept (headFrontOf s a T).f.rows).toList) ∧
      ∀ k ∈ (headFrontOf s a T).f.rows.kept.toList,
        Own.formFits k.c ((headFrontOf s a T).st.tableBits k.oracle .main) = true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  show a.fr.rows.keptRows = ((switchKept a.fr.rows).toList.map fun o =>
      (s.st.oracles.getD o default).shape.mainRows).sum ∧
    (∀ k ∈ a.fr.rows.kept.toList, k.oracle ∈ (switchKept a.fr.rows).toList) ∧
    ∀ k ∈ a.fr.rows.kept.toList, Own.formFits k.c (s.st.tableBits k.oracle .main) = true
  rw [hf]
  exact ⟨rows_of_close hx hg, named_of_close hx, claimKept_of_close hx hg⟩

/-- **The like at the front behind the last segment.** -/
theorem fin_members_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) :
    (finFrontOf t a Q).f.rows.keptRows =
        ((switchKept (finFrontOf t a Q).f.rows).toList.map fun o =>
          ((finFrontOf t a Q).st.oracles.getD o default).shape.mainRows).sum ∧
      (∀ k ∈ (finFrontOf t a Q).f.rows.kept.toList,
        k.oracle ∈ (switchKept (finFrontOf t a Q).f.rows).toList) ∧
      ∀ k ∈ (finFrontOf t a Q).f.rows.kept.toList,
        Own.formFits k.c ((finFrontOf t a Q).st.tableBits k.oracle .main) = true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  show a.fr.rows.keptRows = ((switchKept a.fr.rows).toList.map fun o =>
      (t.st.oracles.getD o default).shape.mainRows).sum ∧
    (∀ k ∈ a.fr.rows.kept.toList, k.oracle ∈ (switchKept a.fr.rows).toList) ∧
    ∀ k ∈ a.fr.rows.kept.toList, Own.formFits k.c (t.st.tableBits k.oracle .main) = true
  rw [hf]
  exact ⟨rows_of_close hx hg, named_of_close hx, claimKept_of_close hx hg⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.headFrontQ_rows
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finishFrontQ_rows
#print axioms VerifiableInference.Desc.K2.Honest.Returns.grows_fresh
#print axioms VerifiableInference.Desc.K2.Honest.Returns.closed_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_closed_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_closed_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_lay_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_lay_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_members_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_members_reached
