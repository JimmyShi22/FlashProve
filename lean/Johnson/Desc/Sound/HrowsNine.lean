-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/HrowsNine.lean: **nine_paid's PREMISE hrows AT THE FILLING OF THE SHARED TABLE's MEANING (mgI, Johnson/Desc/K14/Law/LedgerOne.lean): THREE CLASSES OF ROWS ON G_omega RIDE BACK OVER THE TEST ON G_u AND PAST ITS EXTRACTOR.** Statements and proofs.


THE TWO STEPS. (i) Back over the yes: from the record behind the test to the record in front. (ii) Past the extractor: from the witness handed to block 9's extractor to the witness that it returns: that extractor lays o_u's message
alone, and the three classes read o_omega's and o_sp's.
  msgs_same        a member's messages as read off two witnesses that agree at its seat's two components are one (the inner step of pin_congr, Johnson/Desc/Sound/World.lean, cut out).
  rg_past_nine     the filling's reader of words (rgOf) gives the same words of the two witnesses at the number of a member that sits at the tenant of a message which block 9 does not lay.
  foldOmega_nine   (fold_omega) := RowsO gl 0 1: (i) by RowsBack.lean's allSay_onGu (says_extends; G_omega's rows to the letter) · (ii) by says_agree (a row that has passed the tests reads its group's members'
                   words alone) and membX 9 (G_omega's members are sU, sU + 1).
  sample_nine      a message's own sample's rows := the letter Mg₀'s: (i) by the premise on that letter SampleRides · (ii) by a SECOND premise on the letter, named here: SampleOwn: it reads of the witness the message's own
                   component alone, AT A RECORD IN ORDER (fenced).
  **hrows_nine**   nine_paid's hrows, to the letter, at Mg := mgI ….
WHAT IT LEAVES, EACH NAMED, WITH WHOSE IT IS: hIn: the statement in front of block 9 is in order (Means.InOrder): an invariant of the walk up to the border 9: other files' to show · hG: the statement behind the test has GROWN out of
the one in front (Grows): SampleRides asks it: H2K.Out.k12_grows (Johnson/Desc/K12/Law/GrowsTest.lean: from the yes alone) and over it Seat.tests_grow (declared nowhere in this library) say it; neither lies in the base that this file was built over: so it
stays a premise here · SampleRides · SampleOwn: on the letter Mg₀ · the two members at the two numbers · apartAt twice.
Limits. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.NineAt
import Johnson.Desc.K12.Coin.RowsBack
import Johnson.Desc.K14.Law.LedgerOne
import Johnson.Desc.Means.ItemsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open Iop Prob _root_.Run
open OnBytes.Means (Words InOrder AllSay says_agree)
open VerifiableInference.Desc (Block FileDescription Strs Wit Grows)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Desc.K14.Law (mgI rgOf RowsO SampleRides rowsOn)

/-- A member's messages as read off two witnesses that agree at its seat's two components. -/
theorem msgs_same (cs : Codes) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (x : Mem)
    (w w' : Wit Cells Tok MsgT)
    (e1 : w'.msg (arr (x.1.seat x.2).1 (x.1.seat x.2).2) = w.msg (arr (x.1.seat x.2).1 (x.1.seat x.2).2))
    (e2 : w'.pad (x.1.seat x.2).1 (x.1.seat x.2).2 = w.pad (x.1.seat x.2).1 (x.1.seat x.2).2) :
    msgsOf cs x.1.l x.1.seat arr w' x.2 = msgsOf cs x.1.l x.1.seat arr w x.2 := by
  funext j
  rcases j with q | q
  · show w'.tab cs (x.1.l.get x.2).1 (arr (x.1.seat x.2).1 (x.1.seat x.2).2) (x.1.seat x.2).1
      (x.1.seat x.2).2 false q.1.val q.2.val = w.tab cs (x.1.l.get x.2).1
        (arr (x.1.seat x.2).1 (x.1.seat x.2).2) (x.1.seat x.2).1 (x.1.seat x.2).2 false q.1.val q.2.val
    unfold Wit.tab
    rw [e1, e2]
  · show w'.tab cs (x.1.l.get x.2).1 (arr (x.1.seat x.2).1 (x.1.seat x.2).2) (x.1.seat x.2).1
      (x.1.seat x.2).2 true q.1.val q.2.val = w.tab cs (x.1.l.get x.2).1
        (arr (x.1.seat x.2).1 (x.1.seat x.2).2) (x.1.seat x.2).1 (x.1.seat x.2).2 true q.1.val q.2.val
    unfold Wit.tab
    rw [e1, e2]

/-- The letter for a message's own sample's rows reads of the witness the message's own component alone, AT A RECORD WHOSE STATEMENT IS IN ORDER. (Asked at every record it is FALSE at a filling by "the
sample's rows as they lie in the record say their claims", for this reason: at an arbitrary record a sample row may name any message.) -/
def SampleOwn {P₁ Cells Tok : Type} (N : NumbersS) (arr : ℕ → ℕ → ℕ)
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) : Prop :=
  ∀ (m : Msg2) (s : St) (w w' : Wit Cells Tok MsgT), InOrder s.st → sameAt N arr (.msg m) w' w →
    Mg₀.row (.sample m) s w → Mg₀.row (.sample m) s w'

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells) (N : NumbersS)
  (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (Q : Par) (uR : St → St) (omW : Wit Cells Tok MsgT → ℕ → GE) (e' n : ℕ) (num : Msg2 → ℕ)

/-- **The reader of words past block 9's extractor.** -/
theorem rg_past_nine (ν : Msg2) (hnl : Comp.msg ν ∉ laysAtS true 9)
    (hap : apartAt N arr true 9 (.msg ν) = true) (o : ℕ) (x : Mem) (hm : mem o = some x)
    (hs : SitsAt x (N.tenant ν).1 (N.tenant ν).2) (v : ActV St Fr) (w : Wit Cells Tok MsgT)
    (part : Part) (i : ℕ) :
    rgOf cs arr mem rd (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 v w) o part i =
      rgOf cs arr mem rd w o part i := by
  have h : sameAt N arr (.msg ν) (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 v w) w :=
    extSSame cs Xi St Cells Tok G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true 9 (.msg ν) hnl hap v.1
      (strsOfAct Fr v) w
  have e : x.1.seat x.2 = ((N.tenant ν).1, (N.tenant ν).2) := hs
  unfold rgOf
  rw [hm]
  show rd x (msgsOf cs x.1.l x.1.seat arr _ x.2) part i = rd x (msgsOf cs x.1.l x.1.seat arr w x.2) part i
  rw [msgs_same cs arr x w _ (by rw [e]; exact h.1) (by rw [e]; exact h.2)]

variable (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
  (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
  (hsO : (withOmega P.S).size = 2)
  (hIn : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a → InOrder a.1.2.st)
  (xO xS : Mem) (hmO : mem sentU.size = some xO) (hmS : mem (sentU.size + 1) = some xS)
  (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
  (hapO : apartAt N arr true 9 (.msg .oOmega) = true)
  (hapS : apartAt N arr true 9 (.msg .oSp) = true)

include hb he ha1 hIn hmO hmS sO sS hapO hapS in
/-- **(fold_omega).** -/
theorem foldOmega_nine (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (w : Wit Cells Tok MsgT)
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a)
    (hout : x.ior.red.out a τ = some b)
    (h : RowsO OnBytes.Model.Reading.gl 0 1 b.1.2 (rgOf cs arr mem rd w)) :
    RowsO OnBytes.Model.Reading.gl 0 1 a.1.2 (rgOf cs arr mem rd
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w)) := by
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  obtain ⟨hne, _, hmem, _, _, _⟩ :=
    (membX789 _ _ 9 (.inr (.inr rfl))).1 ((sharedX_parts P sentU layU layO 9 _).1 hX).2.2.1
  have hI := hIn a ha
  have hloc := (onGu_leaves π he ha1 _ _ rs gs hd).2.2.2.1
  unfold memOf at hmem
  obtain ⟨GO, hGO, hmm⟩ := Option.map_eq_some_iff.1 hmem
  have lt : a.1.2.loc.gOmega < a.1.2.st.groups.size := (Array.getElem?_eq_some_iff.1 hGO).1
  unfold RowsO at h ⊢
  rw [hloc] at h
  have h1 := (allSay_onGu OnBytes.Model.Reading.gl π he ha1 _ _ rs gs hd hI _ lt hne 0 1 _).1 h
  intro r hr
  have hr' : r ∈ rowsOn a.1.2 a.1.2.loc.gOmega := List.mem_of_mem_drop (List.mem_of_mem_take hr)
  unfold rowsOn at hr'
  rw [hGO] at hr'
  refine (says_agree OnBytes.Model.Reading.gl (hI.rows _ GO hGO r hr') fun o ho part i => ?_).2
    (h1 r hr)
  rw [hmm] at ho
  have ho' : o = sentU.size ∨ o = sentU.size + 1 := by simpa using ho
  rcases ho' with rfl | rfl
  · exact rg_past_nine cs G arr ms decT₂ c₀ N oNo mem rd .oOmega (by decide) hapO _ xO hmO sO _ w part i
  · exact rg_past_nine cs G arr ms decT₂ c₀ N oNo mem rd .oSp (by decide) hapS _ xS hmS sS _ w part i

include hb he ha1 hsU hsO hIn in
/-- **A message's own sample's rows.** -/
theorem sample_nine (hsr : SampleRides Mg₀ num) (hso : SampleOwn N arr Mg₀)
    (hG : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → Grows a.1.2.st b.1.2.st)
    (m : Msg2) (hm : num m = sentU.size ∨ num m = sentU.size + 1)
    (hnl : Comp.msg m ∉ laysAtS true 9) (hap : apartAt N arr true 9 (.msg m) = true)
    (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (w : Wit Cells Tok MsgT)
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a)
    (hout : x.ior.red.out a τ = some b) (h : Mg₀.row (.sample m) b.1.2 w) :
    Mg₀.row (.sample m) a.1.2
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w) := by
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  have hmk := (membX_nine _ _ ((sharedX_parts P sentU layU layO 9 _).1 hX).2.2.1).2
  have lt := x_numbers P sentU layU layO 9 (.inl rfl) _ hX hsU hsO (num m) (.inr hm)
  have e := (onGu_leaves π he ha1 _ _ rs gs hd).2.1 (num m) lt (by
    rw [hmk]
    intro e
    have e' : 1 = num m := Option.some.inj e
    rcases hm with h | h <;> omega)
  exact hso m _ w _ (hIn a ha)
    (extSSame cs Xi St Cells Tok G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true 9 (.msg m) hnl hap _ _ w)
    (hsr m a.1.2 b.1.2 w (hG a τ b ha hout) e h)

include hb he ha1 hsU hsO hIn hmO hmS sO sS hapO hapS in
/-- **nine_paid's hrows, AT mgI.** -/
theorem hrows_nine (hsr : SampleRides Mg₀ num) (hso : SampleOwn N arr Mg₀)
    (hG : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → Grows a.1.2.st b.1.2.st)
    (hnO : num .oOmega = sentU.size) (hnS : num .oSp = sentU.size + 1) :
    ∀ i ∈ [ItemS.row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega], ∀ a τ b w,
      onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂
        (mgI cs arr Mg₀ mem rd Q uR omW e' n)) f l i 10 ((actQ N f l 10).2 b) w →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂
        (mgI cs arr Mg₀ mem rd Q uR omW e' n)) f l i 9 ((actQ N f l 9).2 a)
        (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w) := by
  intro i hi a τ b w ha hout h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact sample_nine cs G arr ms decT₂ c₀ N Mg₀ Pm₀ Oc oNo P sentU layU layO f l num π x hb he ha1 hsU
      hsO hIn hsr hso hG .oOmega (.inl hnO) (by decide) hapO a b τ w ha hout h
  · exact sample_nine cs G arr ms decT₂ c₀ N Mg₀ Pm₀ Oc oNo P sentU layU layO f l num π x hb he ha1 hsU
      hsO hIn hsr hso hG .oSp (.inr hnS) (by decide) hapS a b τ w ha hout h
  · exact foldOmega_nine cs G arr ms decT₂ c₀ N Pm₀ Oc oNo P sentU layU layO f l mem rd π x hb he ha1
      hIn xO xS hmO hmS sO sS hapO hapS a b τ w ha hout h

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.msgs_same
#print axioms Desc.K14.Law.Fence.rg_past_nine
#print axioms Desc.K14.Law.Fence.foldOmega_nine
#print axioms Desc.K14.Law.Fence.sample_nine
#print axioms Desc.K14.Law.Fence.hrows_nine
