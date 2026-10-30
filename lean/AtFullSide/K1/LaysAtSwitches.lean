-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/LaysAtSwitches.lean: the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean) lays the filling of the matrices at the segments 1 to 24: the form
LaysFilling (Honest/K5/Law/LaysFilling.lean) at the seat over the code switches' sendings.

LaysFilling at segment l says: each array of the segment that the filling of the matrices serves lies in a
seated message (reach, on public data), and wherever that filling answers an element at a main row and place
of message m of the segment, the Script's message with the plan's number of (l, m) holds it (lays).

  1  momentSeat_no, ownMsgOk, placeOk, ownMsgOk_gives   a seat's rank; a public test on a place of the code
     switch and on each of its own messages; what the test's yes gives
  2  placesOkW, linksW, lengthsW   three closed facts at the written plan, by evaluation in Lean's kernel
  3  ask_gives, entry_inl   what a yes of the filling's call that asks first gives; the filling of the
     matrices hands out elements of the base field alone
  4  switch_lays   THE STEP, general in the Script: at one own message of one switch
  5  laysFilling_switches   THE END: LaysFilling at firstScriptAt at every l from 1 to 24

THREE HYPOTHESES ARE NOT PAID HERE, each at every place of the code switch: hLent: the book lends the part its
own cut and every stretch that it carries · hClose: the public test closingOk · hPub: the public test publicOk
at the public instance of every input that Vd admits. With three more public tests, which are shown under the
head (serves_at_head, roomy_at_head, fits_at_head, Honest/K2/Law/PublicAtHead.lean), they are what the code
switch's authors' msgTxt_answers (Honest/K2/Law/LotsAnswer.lean) asks for the switch's text to answer. Where a
text answers nothing the Script holds 0, so without them the end is false, not empty.

Limits. The head h and the return hA are hypotheses. At the sizes Sz.ref alone. At Vd := fun _ => False the
field lays says nothing. It says what the Script's messages hold as a function of the readers of the input:
nothing on what the readers hold. Main rows alone. This file proves nothing about completeness, soundness or
hiding.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Desc.ProofFile.Honest.K5.Law.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.ProofFile.Honest.K1.PlaceSent
import Johnson.Desc.ProofFile.Honest.Law.LaysRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Params (ReqShape ReqMessage)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.Slice (toF ofF toF_ofF)
open P5J (AtMgA CellsM TS)
open P5T (seatsAllFull)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (placesW)

/-! ## 1 The public test -/

/-- Where a seat of one moment names a message, that message is the moment's member of the address's
rank. -/
theorem momentSeat_no {s : ReqShape} {sender : Addr} {l t fr : Nat} {a : MsgAddr} {l' m : Nat}
    (h : momentSeat s sender l t fr a = some (l', m)) : msgNo s l t (a.msg - fr) = some m := by
  unfold momentSeat at h
  split at h
  · obtain ⟨m', hm, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact hm
  · cases h

/-- **A public test on own message number i of the switch at p**: it stands in the sending; the switch is
its first sender; its seat in the list ps has the role "own message m of the link", m the link's i-th message
of moment 0; and it is announced with that message's shape. -/
def ownMsgOk (s : ReqShape) (ps : List P5T.PSeat) (p : K2.SwitchPlace) (i : Nat) : Bool :=
  decide (1 + p.sizes.kept.length + i < (K2.switchSent p.sizes p.others).size) &&
    K2.firstSender p (1 + p.sizes.kept.length + i) &&
    (msgNo s p.link 0 i).any fun m =>
      decide ((K2.switchSeatIn ps p.link (1 + p.sizes.kept.length + i)).map (·.role) =
        some (P5T.Role.own m)) &&
      ((s.link.getD p.link default).messages[m]?).any fun M =>
        decide (((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + i) default).shape =
          M.shape)

/-- How many messages of moment 0 link l has. -/
def momentZero (s : ReqShape) (l : Nat) : Nat :=
  ((s.link.getD l default).messages.zipIdx.filter fun m => m.1.moment == 0).length

/-- **A public test on a place of the code switch**: every message with a main row is sampled; the codes
are codes; each own message passes ownMsgOk. -/
def placeOk (s : ReqShape) (codes : OnBytes.Codes) (ps : List P5T.PSeat) (p : K2.SwitchPlace) : Bool :=
  K2.noWord (K2.switchSent p.sizes p.others) && decide (p.sizes.codes = codes) &&
    (List.range (momentZero s p.link)).all (ownMsgOk s ps p)

theorem ownMsgOk_gives {s : ReqShape} {ps : List P5T.PSeat} {p : K2.SwitchPlace} {i m : Nat}
    (h : ownMsgOk s ps p i = true) (hm : msgNo s p.link 0 i = some m) :
    1 + p.sizes.kept.length + i < (K2.switchSent p.sizes p.others).size ∧
      K2.firstSender p (1 + p.sizes.kept.length + i) = true ∧
      (K2.switchSeatIn ps p.link (1 + p.sizes.kept.length + i)).map (·.role) =
        some (P5T.Role.own m) ∧
      ∃ M, (s.link.getD p.link default).messages[m]? = some M ∧
        ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + i) default).shape =
          M.shape := by
  unfold ownMsgOk at h
  rw [hm] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_some] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  cases hM : (s.link.getD p.link default).messages[m]? with
  | none =>
    rw [hM] at h4
    cases h4
  | some M =>
    rw [hM] at h4
    simp only [Option.any_some, decide_eq_true_eq] at h4
    exact ⟨h1, h2, h3, M, rfl, h4⟩

theorem rank_lt {s : ReqShape} {l i m : Nat} (hm : msgNo s l 0 i = some m) : i < momentZero s l := by
  unfold msgNo at hm
  obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.1 hm
  exact (List.getElem?_eq_some_iff.1 hx).1

/-! ## 2 Closed facts at the written plan -/

/-- For a control: the role "own message k" bent to "own message k + 1". -/
def bentRole : P5T.Role → P5T.Role
  | .own k => .own (k + 1)
  | r => r

set_option maxRecDepth 1000000 in
/-- **The test passes at the 25 written places.** Three controls: it walks 46 own messages; at the empty
list of seats it fails at the first place; with each role "own message k" bent to "own message k + 1", all
seats in their places, it fails at the first place too: so the test reads which message a seat holds. -/
theorem placesOkW :
    (placesW.all (placeOk proofSizedFull.request proofSizedFull.codes seatsAllFull)) = true ∧
      ((placesW.map fun p => momentZero proofSizedFull.request p.link).sum = 46) ∧
      ((placesW.take 1).all (placeOk proofSizedFull.request proofSizedFull.codes [])) = false ∧
      ((placesW.take 1).all (placeOk proofSizedFull.request proofSizedFull.codes
        (seatsAllFull.map fun q => { q with role := bentRole q.role }))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Into each link from 1 to 24 a written switch leads.** A control: into link 0 none. -/
theorem linksW :
    ((List.range 24).all fun l => placesW.any fun p => p.link == l + 1) = true ∧
      (placesW.any fun p => p.link == 0) = false := by
  decide +kernel

/-- The written codes pass the programs' test on lengths. -/
theorem lengthsW : proofSizedFull.codes.lengthsOk = true := by
  decide +kernel

/-! ## 3 The filling's call -/

/-- What a yes of the call that asks first gives. -/
theorem ask_gives {D : RowData} {R : Readers} {hd : List Fmt.Drawn} {a : MsgAddr} {r j : Nat}
    {y : Cb.Gl.F ⊕ Cb.Gl.E} (h : D.ask R hd a r j = .ok (some y)) :
    D.lays a r j = true ∧ y = D.entry R (hd.take (D.heardAt a)) a r j := by
  unfold RowData.ask at h
  split at h
  · cases h
  · split at h
    · cases h
    · have h' : D.at_ R hd a r j = some y := Except.ok.inj h
      unfold RowData.at_ at h'
      by_cases hl : D.lays a r j = true
      · rw [if_pos hl] at h'
        exact ⟨hl, (Option.some.inj h').symm⟩
      · rw [if_neg hl] at h'
        cases h'

/-- The filling of the matrices hands out elements of the base field alone. -/
theorem entry_inl (S : Sz) (codes : OnBytes.Codes) (s : ReqShape) (lay : OnBytes.Params.ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (R : Readers)
    (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) :
    ∃ x : Cb.Gl.F, (firstData S codes s lay seat heard).entry R hd a r j = .inl x := by
  unfold firstData laidData cellsVals
  dsimp only
  repeat' split
  all_goals exact ⟨_, rfl⟩

/-! ## 4 The step -/

/-- **AT ONE OWN MESSAGE OF ONE SWITCH: THE SCRIPT's MESSAGE HOLDS WHAT THE SWITCHES' FILLING ANSWERS.**
General in the Script. hm: the Script holds the switch's text at the number num. hAns: the text answers.
The other hypotheses are on public data. -/
theorem switch_lays {Bk : ProverCoinCounts} {W₀ Rc Tr Cells' Tok' : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) Cells' Tok' MsgT)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat) (S : Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (num fx i l m : Nat) (M : ReqMessage)
    (hm : OwnMsgs Q Vd N num fx (K2.switchMsgTxt 0 (widerRows S Z G) readers closing p
      (1 + p.sizes.kept.length + i)))
    (hAns : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → ∀ r j,
      (K2.switchMsgTxt 0 (widerRows S Z G) readers closing p (1 + p.sizes.kept.length + i) k w hd
        false r j).isSome = true)
    (hw : K2.NoWord (K2.switchSent p.sizes p.others))
    (hn : 1 + p.sizes.kept.length + i < (K2.switchSent p.sizes p.others).size)
    (hseat : K2.switchSeat Z G (p.ownAddr i) = some (l, m))
    (hM : (G.first.shape.link.getD l default).messages[m]? = some M)
    (hsh : ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + i) default).shape =
      M.shape)
    (hcodes : p.sizes.codes = G.first.codes) (hlen : G.first.codes.lengthsOk = true)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (hv : Vd v)
    (hN : N ≤ hd.length) (row place : Nat) (y : Cb.Gl.F ⊕ Cb.Gl.E)
    (hask : (K2.switchData S Z G).ask (readers v) hd (p.ownAddr i) row place = .ok (some y)) :
    Q.msg num k v (hd.take (Q.fixedMsg num)) false row place = asE (some y) := by
  obtain ⟨hl, hy⟩ := ask_gives hask
  obtain ⟨hr, hj, hp, ha⟩ := lays_room G.first.codes G.first.shape G.first.layout (K2.switchSeat Z G)
    (fun _ => 0) (cellsVals S) hlen hseat hM hl
  obtain ⟨x, hx⟩ := entry_inl S G.first.codes G.first.shape G.first.layout (K2.switchSeat Z G)
    (fun _ => 0) (readers v) (hd.take ((K2.switchData S Z G).heardAt (p.ownAddr i))) (p.ownAddr i)
    row place
  have hyx : y = .inl x := hy.trans hx
  have hat : (widerRows S Z G v.x).at_ (readers v) [] (p.ownAddr i) row place = some (.inl x) := by
    have e1 : (widerRows S Z G v.x).at_ (readers v) [] (p.ownAddr i) row place =
        (K2.switchData S Z G).at_ (readers v) [] (p.ownAddr i) row place :=
      K2.with_own S (lotData S) Z G v.x (readers v) [] (p.ownAddr i) row place (by rw [hseat]; rfl)
    rw [e1]
    unfold RowData.at_
    rw [if_pos hl]
    exact congrArg some hx
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 (hAns k v (hd.take fx) hv row place)
  rw [hm k v hd hv hN false row place y' hy', hyx]
  rw [← hsh] at hr ha
  rw [← hsh, ← hcodes] at hj hp
  by_cases h3 : (((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + i)
      default).shape.mainDeg == 3) = true
  · rw [K2.Law.msgTxt_main_e_of 0 (widerRows S Z G) readers closing p k v (hd.take fx) hw hn h3 hr hj
      ha hp hy']
    show K2.asRow _ ((widerRows S Z G v.x).at_ (readers v) [] (p.ownAddr i) row place) = _
    rw [hat]
    rfl
  · rw [K2.Law.msgTxt_main_f_of 0 (widerRows S Z G) readers closing p k v (hd.take fx) hw hn
      (Bool.eq_false_iff.2 h3) hr hj ha hp hy']
    show algebraMap Cb.Gl.F Cb.Gl.E (K2.asRow _ ((widerRows S Z G v.x).at_ (readers v) []
      (p.ownAddr i) row place)).c0 = _
    rw [hat]
    show algebraMap Cb.Gl.F Cb.Gl.E (toF (ofF x)) = _
    rw [toF_ofF]
    exact (K5.asE_inl x).symm

/-! ## 5 The end -/

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- hLent, hClose AND hPub ARE HYPOTHESES, PAID NOWHERE HERE. **THE CLOSED SCRIPT LAYS THE FILLING OF THE
MATRICES AT EVERY SEGMENT FROM 1 TO 24**, at the seat over the code switches' sendings, at "no challenge has
been heard", at the filling's own readers, at every Vd and N. -/
theorem laysFilling_switches (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat)
    (hLent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (hClose : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (hPub : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB W₀, Vd w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p ((K2.segmentsOf A.Z A.G).take p.link)
        w.x = true)
    {l : Nat} (h1 : 1 ≤ l) (h25 : l < 25) :
    K5.LaysFilling h (firstScriptAt I Sz.ref Op A cF) Vd N (readersB I A.Z) (K2.switchSeat A.Z A.G)
      (fun _ => 0) l := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have eF : A.G.first = A.Z.first := by rw [eG]; exact O.first
  obtain ⟨f1, -, f3, -, -, f6⟩ :=
    (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1
  have c𝔇 : h.𝔇.sent.codes = proofSizedFull.codes := f1
  have s𝔇 : h.𝔇.sent.shape = proofSizedFull.request := f3
  have l𝔇 : h.𝔇.sent.layout = Johnson.G.layoutFull := f6
  have cG : A.G.first.codes = proofSizedFull.codes := by rw [eF]; exact f1
  have sG : A.G.first.shape = proofSizedFull.request := by rw [eF]; exact f3
  have lG : A.G.first.layout = Johnson.G.layoutFull := by rw [eF]; exact f6
  have hP : K2.switchPlaces A.Z A.G = placesW := by
    rw [eG]; exact K2.Law.places_at_head h.toAtMg O
  have hS : P5J.At.pseatsAll A.Z = seatsAllFull := K2.Law.pseatsAll_at_head h.toAtMg
  have hAns : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ (n : Nat) (k : Coins A.B) (w : LocB W₀)
      (hd : List Fmt.Drawn), Vd w → ∀ r j,
      (K2.switchMsgTxt 0 (widerRows Sz.ref A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) p n k w hd
        false r j).isSome = true := fun p hp n k w hd hw r j =>
    Option.isSome_iff_exists.2 (K2.Law.msgTxt_answers 0 (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
      A.G.first.layout (K2.segmentsOf A.Z A.G) p (hClose p hp) n k w hd false r j (hLent p hp k)
      (K2.Law.serves_at_head h.toAtMg O p (eG ▸ hp)) (K2.Law.roomy_at_head h.toAtMg O p (eG ▸ hp))
      (hPub p hp w hw) (K2.Law.fits_at_head h.toAtMg O p (eG ▸ hp)))
  refine ⟨?_, ?_⟩
  · intro As Ar hl hAr hz
    rw [l𝔇] at hl
    obtain ⟨M, hM, h0⟩ := K5.arrayMoment_zero hl hAr hz
    obtain ⟨kk, hk⟩ := K5.msgNo_of_moment hM
    rw [h0] at hk
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    obtain ⟨p, hp, e⟩ := List.any_eq_true.1
      (List.all_eq_true.1 linksW.1 l' (List.mem_range.2 (by omega)))
    have e' : p.link = l' + 1 := beq_iff_eq.1 e
    have hx : ((⟨p.place, 0⟩ : Addr), l' + 1, 1 + p.sizes.kept.length) ∈ K2.ownSeats A.Z A.G := by
      unfold K2.ownSeats
      rw [hP]
      exact List.mem_map.2 ⟨p, hp, by rw [e']⟩
    refine ⟨⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + kk⟩, ?_, Nat.zero_le _⟩
    unfold K2.switchSeat
    rw [sG]
    exact K5.seatBy_at (K5.ownSeats_apart O A.G) hx hk
  · intro k v hd hv hN Ad m hseat row place y hask
    rw [c𝔇, s𝔇, l𝔇, ← cG, ← sG, ← lG] at hask
    have hseat' := hseat
    unfold K2.switchSeat K2.seatBy at hseat'
    obtain ⟨z, hz, hzm⟩ := List.exists_of_findSome?_eq_some hseat'
    unfold K2.ownSeats at hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    obtain ⟨a1, a2, a3, -⟩ := momentSeat_says hzm
    have hno := momentSeat_no hzm
    have eAd : Ad = p.ownAddr (Ad.msg - (1 + p.sizes.kept.length)) := by
      obtain ⟨sd, ms⟩ := Ad
      show (⟨sd, ms⟩ : MsgAddr) =
        ⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + (ms - (1 + p.sizes.kept.length))⟩
      have b1 : sd = ⟨p.place, 0⟩ := a1
      have b2 : 1 + p.sizes.kept.length ≤ ms := a2
      rw [b1, Nat.add_sub_cancel' b2]
    have hpW : p ∈ placesW := hP ▸ hp
    have hok := List.all_eq_true.1 placesOkW.1 p hpW
    unfold placeOk at hok
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hw, hc⟩, hall⟩ := hok
    rw [sG] at hno
    obtain ⟨g1, g2, g3, M, g4, g5⟩ := ownMsgOk_gives
      (List.all_eq_true.1 hall _ (List.mem_range.2 (rank_lt hno))) hno
    have hnum : K2.switchNum A.Z p (1 + p.sizes.kept.length + (Ad.msg - (1 + p.sizes.kept.length))) =
        P5J.At.num A.Z p.link m :=
      K2.Law.ownNum_at_head h.toAtMg O p (eG ▸ hp) _ m g1 (by rw [hS]; exact g3)
    subst a3
    rw [← hnum]
    rw [eAd] at hseat hask
    exact switch_lays (firstScriptAt I Sz.ref Op A cF) Vd N Sz.ref A.Z A.G (readersB I A.Z)
      (closingB A.Z A.G) p _ _ _ p.link m M (ownMsgs_switch_first h hA Vd N hp g1 g2)
      (fun k w hd hw' r j => hAns p hp _ k w hd hw' r j) (K2.noWord_yes hw) g1 hseat
      (by rw [sG]; exact g4) g5 (hc.trans cG.symm) (by rw [cG]; exact lengthsW) k v hd hv hN row place
      y hask

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.placesOkW
#print axioms ProofFile.Honest.K1.linksW
#print axioms ProofFile.Honest.K1.lengthsW
#print axioms ProofFile.Honest.K1.switch_lays
#print axioms ProofFile.Honest.K1.laysFilling_switches
