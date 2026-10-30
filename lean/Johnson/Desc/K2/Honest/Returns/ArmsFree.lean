-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsFree.lean: AT THE TWO OTHER SORTS OF PLACE OF A SWITCH (IN FRONT
OF THE OUTPUT HEAD's, NUMBER 339; BEHIND THE QUIET FRONT OF THE PLACE BEHIND THE LAST SEGMENT,
NUMBER 353), AT A REACHED STATE, IN THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART: NO COUNT OF
ROWS WAITS (`HeadBehind.waits`, `FinBehind.waits`, Returns/ArmsBehind.lean) · `OldFits.mainVars` ·
`d0` · `d1` · `ReadFits.placed` · `stated`. What Returns/WaitsReached.lean,
Returns/ClosedReached.lean and Returns/MembersReached.lean have at the links. Statements with their
proofs: calls.

  `owed_behind_cleared` from the fold's return at the cut 353: nothing is owed: `owed_behind_laid`'s
                    walk at segment 24, which has no "laid" behind it
  `head_waits_reached`, `fin_waits_reached` `s.noneWaits = true` at 339; `t.noneWaits = true` behind
                    the quiet front at 353
  `carried_of_close` `mainVars`, `d0`, `d1` for what a closing returns, at every statement grown out
                    of its own: what `link_carried_free` (Returns/ClosedReached.lean) spells at the
                    link
  `head_carried_free`, `fin_carried_free` at the two fronts
  `head_book_reached`, `fin_book_reached` `placed` and `stated` in `ReadFits`' own letters, at what
                    the reading is handed

By, all the library's: `frame_of` (Johnson/IMR/FrameSeat.lean) · `close_of`
(Johnson/IMR/CloseSeat.lean) · `close_numbers`, `k7_sits`, `k7_sits_yes`
(Johnson/IMR/FirstSeats.lean) · `yes_alone` (Johnson/IMR/SeatForm.lean) · `flatIx_scope`
(Johnson/IMR/FlatScope.lean) · `hear_at_flat` (Johnson/IMR/FlatIx.lean) · `closing_keeps`
(Johnson/Desc/First/Close/Law/Leaves.lean) · `headFrontQ_rest`
(Johnson/Top/H0/Tw/K2C/FrontGroup.lean), `finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean):
the two quiet fronts keep what is owed and the book · `finishFrontQ_size`
(Johnson/Top/H0/Tw/K2C/StillKeeps.lean) · `closeFrame_carried`
(Johnson/Desc/First/Close/Law/CarriedRows.lean) · `closeFrame_all`
(Johnson/Goal/Meaning/RecK10.lean) · `bookHas_reached` (Johnson/IMR/AtReach.lean) · `front_len`
(Johnson/IMR/FinPin.lean) · `andThen_yes`, `fold_back`, `fold_next` (Johnson/IMR/FoldTools.lean) ·
`guarded_yes` (Johnson/Desc/Sound/SeatGuardLaws.lean) · `reply_record`
(Johnson/Desc/Kinds/Law/ReplyPins.lean) · `reach_raw`, `Reach.fold`
(Johnson/Top/H0/Walk/Reach.lean). A near relative, not called: `joined_stand`
(Johnson/Desc/Kinds/Law/ReplyShape.lean): "none waits" across the place that hears the reply, in
another form of that place.

Limits. `here` is a premise where a front is named, the quiet front's yes at the second place.
"Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. The walk over the seats stands typed again, as in
Returns/ClosedArms.lean. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.ClosedArms
import Johnson.Desc.K2.Honest.Returns.WaitsReached
import Johnson.Top.H0.Tw.K2C.StillKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows guarded_yes)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontQ finishFrontQ headFrontQ_rest finishFrontQ_rest
  finishFrontQ_size headFrontOf finFrontOf)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_carried closing_keeps)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (closeFrame_all andThen_yes fold_back fold_next)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

/-- `OldFits.mainVars`, `d0`, `d1` for what a closing returns. -/
theorem carried_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    (∀ v ∈ x.1.rows.c.tensors, v.vars = (T.codes.base.getD x.1.rows.code default).logEll) ∧
      (x.1.rows.d.getD 0 #[]).size ≤ (T.codes.mask.getD x.1.rows.maskCode default).ell ∧
      (x.1.rows.d.getD 1 #[]).size ≤ (T.codes.mask.getD x.1.rows.maskCode default).ell := by
  obtain ⟨Gf, G, -, -, CO⟩ := closeFrame_carried h
  obtain ⟨-, -, -, -, -, hcode, hmask, -, -⟩ := closeFrame_all (f' := x.1) (S' := x.2) h
  rw [hg.1, hcode, hmask]
  exact ⟨CO.vars, le_of_eq CO.d0, le_of_eq CO.d1⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **Behind "cleared" of the last segment nothing is owed.** -/
theorem owed_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.rowsOwed = none := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, g, _, _, bC, eL, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 352) f₀
  obtain ⟨rsC, gsC, dc⟩ := fold_next (k := 352) iC fu f₀
  rw [dC] at dc
  have e1 := framesOf_clear_owed hfs g (List.mem_of_getElem? hg) u t₀ ((hclr u t₀).1 dc).1
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have i₂ := IM.close_numbers hS hR O (by omega : 24 < 25) eL a1
  rw [hlen] at i₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 351) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next (k := 351) i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have e2 := shut_owed (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : 24 < 25) eL c1
  rw [hlen] at i₁
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 350) fv
  obtain ⟨rs₁, gs₁, d₁⟩ := fold_next (k := 350) i₁ fw fv
  have dx₁ : x₁.retype.decide w rs₁ gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v rs₁ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  have e3 := (closing_keeps (Cl := Unit) Q w v rs₁ gs₁ dx₁).2.2.2.2.2
  rw [e1, e2, e3]

/-- **`HeadBehind.waits` at a reached state.** -/
theorem head_waits_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) : s.noneWaits = true := by
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
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 Bs.G₀.W.hS.V a2
  have e0' : tm.rowsOwed = none := owed_behind_laid hS hR O (l := 23) (by omega) fm
  unfold S.noneWaits
  show (match m.rowsOwed with | none => true | some n => n == 0) = true
  rw [(headFrontQ_rest hq).2.2.1, e0']

/-- **`FinBehind.waits` behind the quiet front.** -/
theorem fin_waits_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) : t.noneWaits = true := by
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  unfold S.noneWaits
  rw [(finishFrontQ_rest he).2.2.1, owed_behind_cleared hS hR O f₀]

theorem head_carried_free (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) :
    (∀ v ∈ (headFrontOf s a T).f.rows.c.tensors, v.vars =
        ((headFrontOf s a T).st.codes.base.getD (headFrontOf s a T).f.rows.code default).logEll) ∧
      ((headFrontOf s a T).f.rows.d.getD 0 #[]).size ≤
        ((headFrontOf s a T).st.codes.mask.getD (headFrontOf s a T).f.rows.maskCode default).ell ∧
      ((headFrontOf s a T).f.rows.d.getD 1 #[]).size ≤
        ((headFrontOf s a T).st.codes.mask.getD (headFrontOf s a T).f.rows.maskCode
          default).ell := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  show (∀ v ∈ a.fr.rows.c.tensors, v.vars =
      (s.st.codes.base.getD a.fr.rows.code default).logEll) ∧
    (a.fr.rows.d.getD 0 #[]).size ≤ (s.st.codes.mask.getD a.fr.rows.maskCode default).ell ∧
    (a.fr.rows.d.getD 1 #[]).size ≤ (s.st.codes.mask.getD a.fr.rows.maskCode default).ell
  rw [hf]
  exact carried_of_close hx hg

theorem fin_carried_free (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) :
    (∀ v ∈ (finFrontOf t a Q).f.rows.c.tensors, v.vars =
        ((finFrontOf t a Q).st.codes.base.getD (finFrontOf t a Q).f.rows.code default).logEll) ∧
      ((finFrontOf t a Q).f.rows.d.getD 0 #[]).size ≤
        ((finFrontOf t a Q).st.codes.mask.getD (finFrontOf t a Q).f.rows.maskCode default).ell ∧
      ((finFrontOf t a Q).f.rows.d.getD 1 #[]).size ≤
        ((finFrontOf t a Q).st.codes.mask.getD (finFrontOf t a Q).f.rows.maskCode default).ell := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  show (∀ v ∈ a.fr.rows.c.tensors, v.vars =
      (t.st.codes.base.getD a.fr.rows.code default).logEll) ∧
    (a.fr.rows.d.getD 0 #[]).size ≤ (t.st.codes.mask.getD a.fr.rows.maskCode default).ell ∧
    (a.fr.rows.d.getD 1 #[]).size ≤ (t.st.codes.mask.getD a.fr.rows.maskCode default).ell
  rw [hf]
  exact carried_of_close hx hg

/-- **`ReadFits.placed` and `stated` at the head's front.** -/
theorem head_book_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget)
    (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    (∀ o ∈ (idsOf (inFront P9 (headFrontOf s a T) s.book y rL cols)).toList,
        o < (inFront P9 (headFrontOf s a T) s.book y rL cols).book.place.size) ∧
      ∀ o ∈ (idsOf (inFront P9 (headFrontOf s a T) s.book y rL cols)).toList,
        o < (inFront P9 (headFrontOf s a T) s.book y rL cols).st.oracles.size := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  have hlen : 339 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have hb := Meaning.K2.bookHas_reached O (reach_raw hr) hlen
  have H := stated_of_close hx hg
  rw [← hf] at H
  exact ⟨fun o ho => by
    show o < s.book.place.size
    rw [hb]
    exact H o ho, fun o ho => H o ho⟩

/-- **The like at the front behind the last segment.** -/
theorem fin_book_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup)
    (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    (∀ o ∈ (idsOf (inFront P9 (finFrontOf t a Q) t.book y rL cols)).toList,
        o < (inFront P9 (finFrontOf t a Q) t.book y rL cols).book.place.size) ∧
      ∀ o ∈ (idsOf (inFront P9 (finFrontOf t a Q) t.book y rL cols)).toList,
        o < (inFront P9 (finFrontOf t a Q) t.book y rL cols).st.oracles.size := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length :=
    le_of_eq (Meaning.K2.front_len hS hR O).symm
  have hb := Meaning.K2.bookHas_reached O (reach_raw hr) hlen
  have H := stated_of_close hx hg
  rw [← hf] at H
  exact ⟨fun o ho => by
    show o < t.book.place.size
    rw [(finishFrontQ_rest he).1, hb, ← finishFrontQ_size he]
    exact H o ho, fun o ho => H o ho⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.owed_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_waits_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_waits_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.carried_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_carried_free
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_carried_free
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_book_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_book_reached
