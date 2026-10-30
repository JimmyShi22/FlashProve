-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHEvalDone.lean: the item claim 1 "Eval" at number 17, and the four rows of the key file's
first chain at the thread `T₁`, whole.

  `rowNo_lowBits`: a column's number read off its bits.
  `eval_item`: THE ITEM: the row that the text lays on W holds at the thread's witness.
  `first_members`: numbers 0, 1, 16 and 17: PlaysS, BehindS, ExchangeS, RidesPastS and AcceptedS, at
    every letter `Said` and every fall.

Limits. Conditional on `FirstPublic`, `WPublic`, `HeardOfFold`, `CoinsAtSlots`, and, as every debt, on the
thread in front. That the thread stands at any run is not said here. Nothing on any property.
-/
import E2E.FirstHEvalItem
import E2E.KeyOwedAgain

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Place noDigest)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem Source LaterPlaces start₁ sendW pieces
  TensorRowHolds matOf mkOf valOf RowHolds ownB shape₁_iff rowHolds_agree
  rowHolds_iff_says_of_rowIn tensorRowHolds_iff_k13 batt_row_psi)
open VerifiableInference.Desc.K1 (decideSend_iff)
open VerifiableInference.Desc.K13.Law (ρg Holds rows_ok OnLedger AgreeAt holds_congr rowOf_onLedger
  onLedger_of_fit batt_ok lowBits maskOf)
open Johnson.Prover.Send (held held_old held_new)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁)
open Johnson.RunOne.KeyRows23 (core₁_own)
open AtPublicFiles.KeyThread (D one₀ rowsFirst form_behind₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced sentAt groupsW)
open AtPublicFiles.KeyValues (keyPoints oneOf battAt matrixEntryOf firstW)
open AtPublicFiles.Key (wJob eval_iff_held evalIn_of_rows maskOf_held w_sent)
open AtPublicFiles.KeyBook (rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob rowsLaid_part)

/-- A column's number, read off its bits. -/
theorem rowNo_lowBits (k e : Nat) (h : e < 2 ^ k) : Sz.rowNo (lowBits k e) = e := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · exact testBit_rowNo (lowBits k e) ⟨i, hi⟩
  · have hk : k ≤ i := Nat.le_of_not_lt hi
    have h1 : Sz.rowNo (lowBits k e) < 2 ^ i :=
      Nat.lt_of_lt_of_le (rowNo_lt _) (Nat.pow_le_pow_right (by decide) hk)
    have h2 : e < 2 ^ i := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

set_option maxHeartbeats 2000000 in
/-- **THE ITEM.** -/
theorem eval_item (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    {blk : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl} (hb : (Th Xs N Pl K f Q w₀ rc x).bs[17]? = some blk)
    {k : Coins Bk} {s s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (In1 W₀ Rc) X'} {cols : List OpenedColumn}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 17 k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s') :
    (Th Xs N Pl K f Q w₀ rc x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1) := by
  intro ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  have h := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain ⟨bw, hwb⟩ := w_there hs scope
  have e17 := (member_back hs scope hwb).2
  obtain ⟨blk₁, hb₁, hsh, -⟩ := h.member
  obtain rfl : bw.asBare = blk := Option.some.inj (e17.symm.trans hb)
  obtain rfl : bw.asBare = blk₁ := Option.some.inj (e17.symm.trans hb₁)
  have hF₁₈ := form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope (by decide) e17 hT hS
  obtain ⟨c, r₁, r₂, gs, hc, hdec, -, hin, hheard⟩ := step_send (Th Xs N Pl K f Q w₀ rc x) bw.asBare
    K.w K.own₀ (fun z : FirstState => z.d.st) hsh h.half h.fits rfl h.data
    (h.number s hT.2.2.1.1) hd hS
  have hw' : sendW (oneOf Xs) pieces (sentAt Xs.Y.D.1) (groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hwb
  obtain ⟨msgW, l, ids, d', d, o, hds, hdd, hlin, hrw, hlin', hsd⟩ := w_text hw' hdec
  have hn := h.number s hT.2.2.1.1
  have hidx := (ties_at (b := 17) (by decide) hT.2.2.1.1).2
  obtain ⟨t, rows, out, msg, pre, rest, eseen, hpre, hH, hlay, hfits, hbt, es⟩ :=
    back_of_stand hs scope hp hF hT
  have hlinS : s.lin = some { claim := memberClaim out.1 } := by
    rw [es]
  have hl : l = { claim := memberClaim out.1 } := Option.some.inj (hlin.symm.trans hlinS)
  subst hl
  have hidxT : t.idx = 0 := by
    rw [es] at hidx
    exact hidx
  have hval : m.st.input = ⟨w₀, rc, x, ()⟩ := hT.2.2.2.2.2.2.1
  have hseen : m.seen.map (·.drawn) = m.st.heard := hT.2.2.2.2.1.1
  have hlen : m.st.heard.length = roundsTo (D Xs N Pl).first.blocksInOrder 17 := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e.trans (Nat.zero_add _)
  -- the numbers
  obtain ⟨hJ, -⟩ := keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hwb
  have hJw : wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces
      (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N) = some K.w := by
    rw [hp.w]
    exact hJ
  obtain ⟨-, hsent, hfirst, -⟩ := w_sent _ _ _ _ _ _ _ _ _ hJw
  have hcod := (ties_at (b := 18) (by decide) hF₁₈.1).1
  obtain ⟨d₃, r, G, -, hw0, -, -, -, -, hcc⟩ := rows_ok hrw
  have hcodes : d.st.codes = (oneOf Xs).codes := by
    rw [← hcc, ← hsd]
    exact hcod
  obtain ⟨-, eids, -⟩ := (decideSend_iff _ _ _ _ _ _ _).1 hds
  have hfw : o.1.w = firstW Xs := by
    rw [eids, Array.getElem?_map] at hw0
    obtain ⟨z, hz, e⟩ := Option.map_eq_some_iff.1 hw0
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.1 hz
    have hz0 : z = 0 := by
      rw [← hget]
      simp
    rw [← e, hz0, Nat.zero_add, ← hfirst]
    exact hn
  obtain ⟨rE, -, hrE, hEvalIn, G', hG', hmem⟩ := evalIn_of_rows hrw (by
    rw [hcodes]
    exact hw.bits)
  rw [hcodes, hfw] at hrE hEvalIn
  have hst' : s'.d.st = o.2.st := by
    rw [hsd]
  -- the own group
  have hown := core₁_own (plan₁ (one₀ Xs)) (readers₁ (one₀ Xs)) (book₁ (one₀ Xs)) 2 (slots₁ (one₀ Xs))
    4 s' (by decide) ((shape₁_iff _ _ _ _ _ _ _).1 hF₁₈.1).2
  unfold ownB at hown
  split at hown
  · rename_i iI iV g e0 e2 e3
    simp only [Bool.and_eq_true, beq_iff_eq] at hown
    have e3' : s'.lin.map (·.own) = some g := e3
    rw [hlin', Option.map_some] at e3'
    obtain rfl : o.1.own = g := Option.some.inj e3'
    have hgAny := hown.2
    have hgAny' : (o.2.st.groups[o.1.own]?).any (fun G => G.members.toList == [iI, iV] &&
        G.rows.size == 1 && !G.inRun) = true := by
      rw [← hst']
      exact hgAny
    rw [hG', Option.any_some] at hgAny'
    simp only [Bool.and_eq_true, beq_iff_eq] at hgAny'
    obtain ⟨⟨hmembers, hsize⟩, -⟩ := hgAny'
    have hi0 : iI = 0 := Option.some.inj e0.symm
    have hv : iV = firstW Xs := by
      have e : (plan₁ (one₀ Xs)).orc 2 = some (firstW Xs) := by
        rw [← hfirst]
        exact h.orc
      exact Option.some.inj (e2.symm.trans e)
    subst hi0
    subst hv
    have hrows0 : G'.rows[0]? = some rE := by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
      have hjl : j < G'.rows.toList.length := (List.getElem?_eq_some_iff.1 hj).1
      have : j = 0 := by
        simp only [Array.length_toList, hsize] at hjl
        omega
      subst this
      simpa using hj
    have hinG : RowIn s'.d.st G' rE := (order_of hF₁₈).rows o.1.own G' (by
      rw [hst']
      exact hG') rE hmem
    -- the witness
    have hwit : (Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input (y.2.st.heard ++ ds') =
        (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ (ds ++ ds')) := by
      rw [hin, hheard, List.append_assoc]
    let v := (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ (ds ++ ds'))
    let val := valOf (plan₁ (one₀ Xs)) readH v
    let mat := matOf (plan₁ (one₀ Xs)) readH v
    let mk := mkOf (plan₁ (one₀ Xs)) readH v
    let w₁ : Words GE := fun q pt j => readE (val q pt j)
    let V := K.w.rows c m.shown m.st 0
    have hmatE : ∀ a b, mat a b = OnBytes.Slice.ofF ((f m.st.input.w₀).entry a b) := by
      intro a b
      exact matAt_cells (one₀ Xs).lin (f m.st.input.w₀) a b
    -- the row in front
    have hopen : KItem.pile ∈ (Th Xs N Pl K f Q w₀ rc x).opened 17 := by
      show KItem.pile ∈ ProofFile.Honest.fwdOpen (start₁ 2) rowsFirst 17
      decide
    obtain ⟨x₀, hx₀, hTR⟩ := hT.2.2.2.1 (ds ++ ds') _ hopen
    have ex₀ : x₀ = out.1 := by
      have e : (some (VerifiableInference.Desc.Key.rowOfLinClaim (memberClaim out.1)) :
          Option TensorRow) = some x₀ := by
        rw [← hx₀]
        show _ = s.lin.map fun L => VerifiableInference.Desc.Key.rowOfLinClaim L.claim
        rw [hlinS]
        rfl
      rw [row_of_member] at e
      exact (Option.some.inj e).symm
    subst ex₀
    have hk13 := (tensorRowHolds_iff_k13 (plan₁ (one₀ Xs)).m mat mk out.1
      (batt_row_psi hbt)).1 hTR
    obtain ⟨r', rs', xx, t', hdd', oo, -, -, hfit', -, -, -, -, hrun, -, hout⟩ := batt_ok hbt
    have hOn : OnLedger 0 out.1 := by
      have e := rowOf_onLedger hfit' (onLedger_of_fit hfits) hrun
      rw [hout]
      rw [hidxT] at e
      exact e
    have hpos : 0 < firstW Xs := by
      rw [hp.firstIsPlans]
      omega
    let matL := (VerifiableInference.Desc.Key.witOf (plan₁ (one₀ Xs)).m mat mk).mat
    have hSays : Says ρg s'.d.st rE (held w₁ (firstW Xs) K.w.P V) := by
      refine (eval_iff_held (matrixEntryOf f) (oneOf Xs) pieces (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs)
        rideW (keyPoints Xs N) (battAt Xs N) K.w hJw hw.answers hw.maskRows hw.mainDeg c m.shown m.st
        0 w₁ matL ?_ hw.bits hw.room out.1 ?_ rE hrE s'.d.st ?_).2 ?_
      · intro a e he
        show readE (OnBytes.ofF (mat a.val (Sz.rowNo (lowBits _ e)))) = _
        have hrow : Sz.rowNo (lowBits (plan₁ (one₀ Xs)).m.kCol e) = e := rowNo_lowBits _ _ he
        rw [hrow, hmatE, OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]
        rfl
      · rw [Nat.sub_zero, List.take_length]
        have e := hH []
        rw [List.append_nil] at e
        exact weights_of_back hw eseen hpre hseen e hlay hbt
      · rw [hst']
        exact hEvalIn
      · have hA : AgreeAt 0 (VerifiableInference.Desc.Key.witOf (plan₁ (one₀ Xs)).m mat mk)
            (VerifiableInference.Desc.K13.Law.witOf matL (held w₁ (firstW Xs) K.w.P V)) := by
          refine ⟨rfl, fun j => ?_⟩
          show readE (mk ⟨0, j⟩) = maskOf (held w₁ (firstW Xs) K.w.P V) ⟨0, j⟩
          rw [maskOf_held w₁ (firstW Xs) K.w.P V ⟨0, j⟩ hpos]
          rfl
        exact (holds_congr ρg hOn hA).1 hk13
    let held₁ := held w₁ (firstW Xs) K.w.P V
    let val₀ : Nat → OnBytes.Part → Nat → OnBytes.E := fun q pt j => OnBytes.E.ofTriple (ofE (held₁ q pt j))
    have h₀ : RowHolds (fun a b => rdE.val a = rdE.val b) s'.d.st val₀ rE := by
      refine (rowHolds_iff_says_of_rowIn rdE s'.d.st _ val₀ rE hinG).2 ?_
      have e : (fun q pt j => rdE.val (val₀ q pt j)) = held₁ := by
        funext q pt j
        exact toE_ofE _
      rw [e]
      exact hSays
    have hV : V = ProofFile.Honest.K1.rowsLaid K.w K.own₀ c m.st.input m.st.heard := by
      have q := rowsLaid_part K.w K.own₀ h.data c m.shown m.st 0
      rw [Nat.sub_zero, List.take_length] at q
      exact q.symm
    have hagree : ∀ q ∈ G'.members.toList, ∀ pt j, rdE.val (val₀ q pt j) = rdE.val (val q pt j) := by
      intro q hq pt j
      rw [hmembers] at hq
      have e₀ : rdE.val (val₀ q pt j) = held₁ q pt j := toE_ofE _
      rw [e₀]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact held_old w₁ (firstW Xs) K.w.P V 0 pt j fun e => absurd e.1 (Nat.not_le.2 hpos)
      · obtain rfl := List.mem_singleton.1 hq
        have e₁ : held₁ (firstW Xs) pt j = (V 0).word (Johnson.Prover.Send.shapeAt K.w.P 0) pt j :=
          held_new w₁ (firstW Xs) K.w.P V 0 hsent pt j
        have e₂ : readE (val K.w.first pt j) = v.msg 2 pt j := val_first h v pt j
        have e₃ := wit_msg h hc m.st.heard hlen (ds ++ ds')
        rw [hfirst] at e₂
        refine e₁.trans (Eq.trans ?_ e₂.symm)
        have e₄ : v = (Fl Xs N Pl K f Q x).wit k w₀ rc (m.st.heard ++ (ds ++ ds')) [] := by
          show (Fl Xs N Pl K f Q x).wit k m.st.input.w₀ m.st.input.rc _ [] = _
          rw [hval]
        rw [e₄, e₃, hV, hval]
        exact (held_new _ _ K.w.P _ 0 hsent pt j).symm
    show ∃ z, ((readers₁ (one₀ Xs)).eval s') = some z ∧
      RowHolds readH.same s'.d.st (valOf (plan₁ (one₀ Xs)) readH
        ((Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input (y.2.st.heard ++ ds'))) z
    rw [hwit]
    refine ⟨rE, ?_, (rowHolds_agree rdE hinG val₀ val hagree).1 h₀⟩
    show s'.lin.bind (fun L => (s'.d.st.groups[L.own]?).bind fun G => G.rows[0]?) = some rE
    rw [hlin', Option.bind_some, hst', hG', Option.bind_some]
    exact hrows0
  · exact absurd hown (by simp)

/-- **What the batching's row owes.** -/
theorem exchange_batt (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hF : HeardOfFold Xs N Pl)
    (hC : CoinsAtSlots Xs N Pl K f Q w₀ rc x) : Exchange (Th Xs N Pl K f Q w₀ rc x) 16 := by
  intro blk hb k s m E ds y cols s' hT hd hS
  obtain ⟨blk₀, hb₀, -, -, -, hst, -⟩ :=
    batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain rfl : blk = blk₀ := Option.some.inj (hb.symm.trans hb₀)
  have hP := pile_item hs scope hp (fun _ _ _ _ hT' tail => heard_at_stand hF hT' tail) hC hb hT hd hS
  obtain ⟨-, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hS.2
  have hA := AtPublicFiles.KeyThread.owed_again (Th Xs N Pl K f Q w₀ rc x) hT hS [KItem.pin 0] (by
                intro i hi
                obtain rfl := List.mem_singleton.1 hi
                show KItem.pin 0 ∈ ProofFile.Honest.fwdOpen (start₁ 2) rowsFirst 16
                decide)
    (fun i hi v hm => by
      obtain rfl := List.mem_singleton.1 hi
      exact ride_pin (hst hdec) hm)
  show (Th Xs N Pl K f Q w₀ rc x).Items (rowsFirst 16).owes k s' y.2 (E.add y.1)
  have ho : (rowsFirst 16).owes = [.pile, .pinT, .pin 0] := by decide
  rw [ho]
  intro ds' i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hP ds' _ (List.mem_singleton.2 rfl)
  rcases List.mem_cons.1 hi with rfl | hi
  · exact pinT_item ds' _ (List.mem_singleton.2 rfl)
  obtain rfl := List.mem_singleton.1 hi
  exact hA ds' _ (List.mem_singleton.2 rfl)

/-- **Numbers 0, 1, 16 and 17, whole, at every letter `Said` and every fall.** -/
theorem first_members (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    (hC : CoinsAtSlots Xs N Pl K f Q w₀ rc x)
    (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [0, 1, 16, 17], PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
      BehindS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
      RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
      AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact rows_idx hs scope hp Said fall
  · exact rows_msg hs scope hp Said fall
  · exact ⟨playsS_of _ _ (plays_batt hs scope hp), behindS_of _ _ (behind_batt hs scope hp),
      exchangeS_of _ _ (exchange_batt hs scope hp hF hC), ridesPastS_of _ _ rides_batt,
      acceptedS_of _ _ (accepted_batt hs scope hp fall)⟩
  · have h := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
    exact ⟨playsS_of _ _ (seat_plays h), behindS_of _ _ (behind_w hs scope hp),
      exchangeS_of _ _ (exchange_w hs scope hp fun _ hb _ _ _ _ _ _ _ _ hT hd hS =>
        eval_item hs scope hp hw hF hb hT hd hS),
      ridesPastS_of _ _ rides_w, acceptedS_of _ _ (accepted_send hs scope h (by decide) (by decide) fall)⟩

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.rowNo_lowBits
#print axioms AtPublicFiles.FirstH.eval_item
#print axioms AtPublicFiles.FirstH.exchange_batt
#print axioms AtPublicFiles.FirstH.first_members
