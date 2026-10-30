-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamWordSh.lean: **MemberFacts' SEVENTH CLAUSE (THE WORD) AT THE SHARED CHAIN's TWO PROXIMITY TESTS, AT ms := msSh · N.tenant := tenantSh t₁ layU layO, MEMBER BY MEMBER OF THE KIND's DATA.** Statements; each proof is calls: word_seat (SeamWordSeats.lean) · sits_nine | sits_ten
(K12/Coin/MemberSits.lean) · seatIs_nine_X | seatIs_ten_X (K12/Coin/SeatIsAtLaw.lean) · memSh's lemmas (SeamNumbersSh.lean).
  **word_nine | word_ten**   inside the promise at 9 | 10, at whatever the record behind the seat's door in fixes, for the data's member j: (j = 0 → s1 at memSh .oU | .oOmega) ∧ (j = 1 → s1 at memSh .oSp): to the letter of MemberFacts' (7), at no := noAt t₁ t₂ 1.
LEFT AS PREMISES: SeatFits at the two sendings (the test seatsFitB has its law seatsFit_of_B) · the depth's premise (depth_at_desc) · SentBefore at the border (sb_sh, SeamTreesSh.lean) · the entries (heU, heS) · what seatIs_*_X asks of the description and the plan
(the shared chain's told oracles are the kind's chain's · the first chain tells t₁ trees · the two layouts are layTrees' · a split · masks ahead).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamWordSeats
import Johnson.Desc.Sound.SeamNumbersSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (strOf layOf)
open H2K.First (Seat1 Plain)

variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (S : LinShape) (rU rO rSp t₁ t₂ : ℕ)
  (ch : Model.Verify.Chains) (tests : List (Block St Unit))
  (last : List (Block St Unit) → Block St Unit)
  (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
    VerifiableInference.Desc.oraclesOf (chainOf ch P tests last).blocksInOrder)
  (hlo : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁)
  (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
  (hlO : layTrees P.codes (withOmega P.S) = some layO)
  (hS : P.S.sharedSplitNeeded = true) (hm : P.S.masksAhead = true)
  (hsU : sentU.size = 2) (hsO : (withOmega P.S).size = 2)
  (hN : N.tenant = tenantSh t₁ layU layO)
  (hd : ∀ j o, G.oracleAt j = some o → ∀ e ∈ Fr.all, e.no = j → e.a ≤ o.logLength)
include hG hlo hU hlU hlO hS hm hsU hsO hN hd

/-- **AT THE TEST ON G_u.** -/
theorem word_nine (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ oNo P sentU layU layO) Oc true f l 9
      a)
    (y : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hB : ∀ m, SentBefore N f l 9 y m)
    (hFU : SeatFits G cs (sendingU S rU t₁ layU layO).l (sendingU S rU t₁ layU layO).seat)
    (hFO : SeatFits G cs (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU layO).seat)
    (π : P12) (t : T12) (ht : inGu a.1.2 = .ok t) (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a₀ rest G0 Ly D)
    (j : Fin D.mems.length)
    (heU : j.val = 0 → (memSh S rU rO rSp t₁ layU layO .oU).1.l.get
      (memSh S rU rO rSp t₁ layU layO .oU).2 = ((D.mems.get j).sh, rU))
    (heS : j.val = 1 → (memSh S rU rO rSp t₁ layU layO .oSp).1.l.get
      (memSh S rU rO rSp t₁ layU layO .oSp).2 = ((D.mems.get j).sh, rSp)) :
    (j.val = 0 → HEq (strOf cs (D.mems.get j).sh rU (layOf (D.mems.get j))
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).1
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).2)
      (wordsOf G cs (memSh S rU rO rSp t₁ layU layO .oU).1.l
        (memSh S rU rO rSp t₁ layU layO .oU).1.seat (strsOfAct Fr ((actQ N f l 9).2 a))
        (memSh S rU rO rSp t₁ layU layO .oU).2)) ∧
    (j.val = 1 → HEq (strOf cs (D.mems.get j).sh rSp (layOf (D.mems.get j))
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).1
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).2)
      (wordsOf G cs (memSh S rU rO rSp t₁ layU layO .oSp).1.l
        (memSh S rU rO rSp t₁ layU layO .oSp).1.seat (strsOfAct Fr ((actQ N f l 9).2 a))
        (memSh S rU rO rSp t₁ layU layO .oSp).2)) := by
  have hX := x_of_on cs G _ N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  obtain ⟨_, hq⟩ := sits_nine P sentU layU layO t₁ t₂ a.1.2 (by omega) (by omega) hX π t ht a₀ rest G0
    Ly D hf
  obtain ⟨_, hT⟩ := seatIs_nine_X G ch P tests last sentU layU layO t₁ t₂ hG hlo hU hlU hlO hS hm a.1.2
    hX π t ht a₀ rest G0 Ly D hf
  have p9 := promsAt_tests.1
  constructor
  · intro e
    rcases hq j with ⟨_, _, hs⟩ | ⟨e', _, _⟩
    · rcases hT j with ⟨_, _, hTj⟩ | ⟨e', _, _⟩
      · refine word_seat cs G _ N Pm₀ Oc oNo P sentU layU layO f l 9 .oU (by rw [p9]; simp) a ha _
          (memSh_mem S rU rO rSp t₁ layU layO .oU)
          (by rw [hN]; exact memSh_sits S rU rO rSp t₁ layU layO .oU) y (hB _) t₁ t₂ D.book _
          (by rw [hN]; exact hs) sentU [[0], []] layU 0 hTj ?_ hFU (fun o ho => hd _ o ho) _ rU (heU e)
        exact (congrArg Prod.snd hs).symm
      · omega
    · omega
  · intro e
    rcases hq j with ⟨e', _, _⟩ | ⟨_, _, hs⟩
    · omega
    · rcases hT j with ⟨e', _, _⟩ | ⟨_, _, hTj⟩
      · omega
      · refine word_seat cs G _ N Pm₀ Oc oNo P sentU layU layO f l 9 .oSp (by rw [p9]; simp) a ha _
          (memSh_mem S rU rO rSp t₁ layU layO .oSp)
          (by rw [hN]; exact memSh_sits S rU rO rSp t₁ layU layO .oSp) y (hB _) t₁ t₂ D.book _
          (by rw [hN]; exact hs) (withOmega P.S) [[1], [1, 0]] layO 1 hTj ?_ hFO
          (fun o ho => hd _ o ho) _ rSp (heS e)
        exact (congrArg Prod.snd hs).symm

/-- **AT THE TEST ON G_omega.** The data's first member is o_omega, its second o_sp. -/
theorem word_ten (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ oNo P sentU layU layO) Oc true f l 10
      a)
    (y : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hB : ∀ m, SentBefore N f l 10 y m)
    (hFO : SeatFits G cs (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU layO).seat)
    (π : P12) (t : T12) (ht : inGomega a.1.2 = .ok t) (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a₀ rest G0 Ly D)
    (j : Fin D.mems.length)
    (heU : j.val = 0 → (memSh S rU rO rSp t₁ layU layO .oOmega).1.l.get
      (memSh S rU rO rSp t₁ layU layO .oOmega).2 = ((D.mems.get j).sh, rO))
    (heS : j.val = 1 → (memSh S rU rO rSp t₁ layU layO .oSp).1.l.get
      (memSh S rU rO rSp t₁ layU layO .oSp).2 = ((D.mems.get j).sh, rSp)) :
    (j.val = 0 → HEq (strOf cs (D.mems.get j).sh rO (layOf (D.mems.get j))
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).1
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).2)
      (wordsOf G cs (memSh S rU rO rSp t₁ layU layO .oOmega).1.l
        (memSh S rU rO rSp t₁ layU layO .oOmega).1.seat (strsOfAct Fr ((actQ N f l 10).2 a))
        (memSh S rU rO rSp t₁ layU layO .oOmega).2)) ∧
    (j.val = 1 → HEq (strOf cs (D.mems.get j).sh rSp (layOf (D.mems.get j))
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).1
        (W0 Fr (noAt t₁ t₂ 1) D.book a.2 (D.mems.get j).t).2)
      (wordsOf G cs (memSh S rU rO rSp t₁ layU layO .oSp).1.l
        (memSh S rU rO rSp t₁ layU layO .oSp).1.seat (strsOfAct Fr ((actQ N f l 10).2 a))
        (memSh S rU rO rSp t₁ layU layO .oSp).2)) := by
  have hX := x_of_on cs G _ N Pm₀ Oc oNo P sentU layU layO f l 10 a ha
  obtain ⟨_, hq⟩ := sits_ten P sentU layU layO t₁ t₂ a.1.2 (by omega) hX π t ht a₀ rest G0
    Ly D hf
  obtain ⟨_, hT⟩ := seatIs_ten_X G ch P tests last sentU layU layO t₁ t₂ hG hlo hU hlU hlO hS a.1.2
    hX π t ht a₀ rest G0 Ly D hf
  have p9 := promsAt_tests.2.1
  constructor
  · intro e
    rcases hq j with ⟨_, _, hs⟩ | ⟨e', _, _⟩
    · rcases hT j with ⟨_, _, hTj⟩ | ⟨e', _, _⟩
      · refine word_seat cs G _ N Pm₀ Oc oNo P sentU layU layO f l 10 .oOmega (by rw [p9]; simp) a ha _
          (memSh_mem S rU rO rSp t₁ layU layO .oOmega)
          (by rw [hN]; exact memSh_sits S rU rO rSp t₁ layU layO .oOmega) y (hB _) t₁ t₂ D.book _
          (by rw [hN]; exact hs) (withOmega P.S) [[1], [1, 0]] layO 0 hTj ?_ hFO
          (fun o ho => hd _ o ho) _ rO (heU e)
        exact (congrArg Prod.snd hs).symm
      · omega
    · omega
  · intro e
    rcases hq j with ⟨e', _, _⟩ | ⟨_, _, hs⟩
    · omega
    · rcases hT j with ⟨e', _, _⟩ | ⟨_, _, hTj⟩
      · omega
      · refine word_seat cs G _ N Pm₀ Oc oNo P sentU layU layO f l 10 .oSp (by rw [p9]; simp) a ha _
          (memSh_mem S rU rO rSp t₁ layU layO .oSp)
          (by rw [hN]; exact memSh_sits S rU rO rSp t₁ layU layO .oSp) y (hB _) t₁ t₂ D.book _
          (by rw [hN]; exact hs) (withOmega P.S) [[1], [1, 0]] layO 1 hTj ?_ hFO
          (fun o ho => hd _ o ho) _ rSp (heS e)
        exact (congrArg Prod.snd hs).symm

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.word_nine
#print axioms Desc.K14.Law.Fence.word_ten
