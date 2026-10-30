-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Built in X24 on lane 142, a working ride over laws.14's working ground, no seal, no names check.
/-
E2E/FirstHWIs.lean: at the end of the first chain, W's words at the thread's witness are gᵀM, at the g of
the claim that the state holds: `w_is_at_stand`. For the door's (Dot) (E2E/KeyDotMeets.lean).

  `fold_cut`: a fold that leaves a rest is the same fold over what it read.
  `w_cut`: the sender's purse can be cut, at the key file's book.
  `w_is_at_stand`: the statement.

Limits. Conditional on `FirstPublic`, `WPublic`, `HeardOfFold` and on the stand at 19. The matrix by bits is a
letter under one premise (hmat). Nothing on any property.
-/
import E2E.FirstHEvalDone
import E2E.FirstHPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block OpenedColumn noDigest foldBlocks)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces pieces batchWhere valOf)
open VerifiableInference.Desc.K13.Law (WIs rows_ok lowBits)
open OnBytes (memberClaim)
open VerifiableInference.Desc.Keeps (emap_ok)
open Johnson.Prover.Send (held held_new)
open Johnson.RunOne.KeyRows1 (plan₁)
open AtPublicFiles.KeyThread (D one₀)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keysAt sentAt groupsW)
open AtPublicFiles.KeyValues (keyPoints oneOf battAt matrixEntryOf firstW)
open AtPublicFiles.Key (wJob wIs_held w_sent)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob rowsLaid rowsLaid_part lentCut dueR)

/-- **A fold that leaves a rest is the same fold over what it read.** -/
theorem fold_cut {S Cl : Type} (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (t : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
    foldBlocks ft l s rs cols = .ok (t, r, c) → ∀ pre, rs = pre ++ r →
      foldBlocks ft l s pre cols = .ok (t, [], c)
  | [], s, rs, cols, t, r, c, h, pre, e => by
    have e₀ : (s, rs, cols) = (t, r, c) := Except.ok.inj h
    obtain ⟨rfl, e₁⟩ := Prod.mk.inj e₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₁
    have hp : pre = [] := by
      have := congrArg List.length e
      rw [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    rfl
  | b :: l, s, rs, cols, t, r, c, h, pre, e => by
    obtain ⟨hlen, s', k, hstep, hrest⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    obtain ⟨p', e', -⟩ := fold_rest ft l s' _ _ t r c hrest
    have hL : b.rounds.length ≤ pre.length := by
      have h1 := congrArg List.length e
      have h2 := congrArg List.length e'
      rw [List.length_append] at h1 h2
      rw [List.length_drop] at h2
      rw [List.length_take] at hlen
      omega
    have ht : rs.take b.rounds.length = pre.take b.rounds.length := by
      rw [e, List.take_append_of_le_length hL]
    have hd : rs.drop b.rounds.length = pre.drop b.rounds.length ++ r := by
      rw [e, List.drop_append_of_le_length hL]
    rw [ht] at hlen hstep
    exact VerifiableInference.Desc.foldBlocks_cons_ok.2
      ⟨hlen, s', k, hstep, fold_cut ft l s' _ _ t r c hrest _ hd⟩

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : PublicFiles}

/-- **The sender's purse can be cut.** -/
theorem w_cut {J : SendJob (In1 W₀ Rc) X'} (hK : fullPub = some K₀) (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (hJ : wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces (groupsW Xs.Y.D.1 Xs.Y.told.1)
      (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N) = some J)
    (hp : J.P.place = AtPublicFiles.KeyBook.wPlace) (k : Coins (keyBook K₀)) :
    ∃ c, lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c := by
  have h6 := AtPublicFiles.AtFiles.Full.six_sourced hs scope
  have hst := AtPublicFiles.KeyBook.wJob_stated (V := Unit) (X := X') K₀ hK (oneOf Xs)
    ⟨h6.codes, h6.indexMasks, h6.ranges, h6.lin⟩ pieces (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs)
    (matrixEntryOf f) rideW AtPublicFiles.KeyBook.rides_full.2.2 (keyPoints Xs N) (battAt Xs N) J hJ
  have e1 : dueR J.P J.ride = dueAt (keyBook K₀).first ⟨AtPublicFiles.KeyBook.wPlace, 0⟩ :=
    congrArg (·.1) hst
  have e2 : ((k.look 0) ⟨AtPublicFiles.KeyBook.wPlace, 0⟩).1 =
      dueAt (keyBook K₀).first ⟨AtPublicFiles.KeyBook.wPlace, 0⟩ :=
    AtPublicFiles.KeyBook.look_due k 0 _
  unfold lentCut
  rw [hp]
  refine AtPublicFiles.KeyBook.cut_some _ _ _ ?_
  rw [e1, e2]
  exact ⟨Nat.le_of_eq (Nat.zero_add _), Nat.le_of_eq (Nat.zero_add _)⟩

/-- **W's words at the thread's witness are gᵀM, at the claim's g.** -/
theorem w_is_at_stand (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    {k : Coins (keyBook K₀)} {e₁ : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 19 k e₁ m E) (ds : List Fmt.Drawn)
    (mat : Fin (oneOf Xs).lin.matrixRows → (Fin (oneOf Xs).lin.kCol → Bool) → GE)
    (hmat : ∀ i e, e < 2 ^ (oneOf Xs).lin.kCol →
      mat i (lowBits (oneOf Xs).lin.kCol e) = algebraMap GF GE (matrixEntryOf f m.st.input i.val e)) :
    ∃ l : OnBytes.LinFirst, e₁.lin = some l ∧
      WIs mat (fun q pt j => readE (valOf (plan₁ (one₀ Xs)) readH
        ((Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ ds)) q pt j))
        l.claim.g (firstW Xs) (linLayW (oneOf Xs).codes (oneOf Xs).lin) := by
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hT.2.2.2.2.1
  have hb₀ : s₀ = (D Xs N Pl).start₁ m.st.input.x := hbeg
  subst hb₀
  have hval : m.st.input = ⟨w₀, rc, x, ()⟩ := hT.2.2.2.2.2.2.1
  have h := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain ⟨bw, hwb⟩ := w_there hs scope
  have e17 := (member_back hs scope hwb).2
  have e18 := seal_at hs scope hwb
  obtain ⟨blk, hb, hr, -, -, -, hdecide⟩ :=
    batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  -- the fold, cut at 16
  let bW : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl := bw.asBare
  have etake : (D Xs N Pl).first.blocksInOrder.take 19 = (D Xs N Pl).first.blocksInOrder.take 16 ++
      [blk, bW, (D Xs N Pl).first.last.asBare] := by
    have a : (D Xs N Pl).first.blocksInOrder.take 17 = (D Xs N Pl).first.blocksInOrder.take 16 ++ [blk] :=
      take_succ_some (show (D Xs N Pl).first.blocksInOrder[16]? = some blk from hb)
    have b : (D Xs N Pl).first.blocksInOrder.take 18 = (D Xs N Pl).first.blocksInOrder.take 17 ++ [bW] :=
      take_succ_some e17
    have c : (D Xs N Pl).first.blocksInOrder.take 19 =
        (D Xs N Pl).first.blocksInOrder.take 18 ++ [(D Xs N Pl).first.last.asBare] := take_succ_some e18
    rw [c, b, a]
    simp
  have hfold' : foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 16 ++
      [blk, bW, (D Xs N Pl).first.last.asBare])
      ((D Xs N Pl).start₁ m.st.input.x) m.seen cols = .ok (e₁, [], []) := by
    have e := hfold
    rw [show (Th Xs N Pl K f Q w₀ rc x).bs.take 19 = _ from etake] at e
    exact e
  obtain ⟨t, rest, c, h1, h2⟩ := Johnson.Desc.First.Walk.Tied.fold_split 0 _ _ _ _ _ _ hfold'
  obtain ⟨s₁, k₁, hl₁, hstep₁, h3⟩ := VerifiableInference.Desc.foldBlocks_cons 0 blk _ t rest c _ h2
  obtain ⟨s₂, k₂, hl₂, hstep₂, h4⟩ := VerifiableInference.Desc.foldBlocks_cons 0 bw.asBare _ s₁ _ _ _ h3
  obtain ⟨s₃, k₃, -, hstep₃, h5⟩ := VerifiableInference.Desc.foldBlocks_cons 0 _ _ s₂ _ _ _ h4
  have e₅ : s₃ = e₁ := (Prod.mk.inj (Except.ok.inj h5)).1
  subst e₅
  -- the batching
  obtain ⟨hfit₁, gs₁, hdec₁⟩ := VerifiableInference.Desc.K1.step_ok _ blk t s₁ _ _ _ hstep₁
  have hlenrs : ((rest.take blk.rounds.length).map noDigest).length =
      (VerifiableInference.Desc.K13.battRounds (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1))).length := by
    have e : blk.rounds.length =
        (VerifiableInference.Desc.K13.battRounds (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1))).length := by
      rw [hr, hp.batt]
      rfl
    rw [List.length_map]
    exact hl₁.trans e
  obtain ⟨rows, out, msg, hlay, -, -, hbt, rfl⟩ := seat_rounds_said keysAt (oneOf Xs) pieces
    (sentAt Xs.Y.D.1) t _ _ gs₁ hlenrs ((hdecide _ _ _).symm.trans hdec₁)
  -- W's sending
  obtain ⟨-, gs₂, hdec₂⟩ := VerifiableInference.Desc.K1.step_ok _ bw.asBare _ s₂ _ _ _ hstep₂
  have hw' : VerifiableInference.Desc.Key.sendW (oneOf Xs) pieces (sentAt Xs.Y.D.1)
      (groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hwb
  obtain ⟨hJ, -⟩ := keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hwb
  have hJw : wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces
      (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N) = some K.w := by
    rw [hp.w]
    exact hJ
  obtain ⟨hsh₁, hsent, hfirst, -⟩ := w_sent _ _ _ _ _ _ _ _ _ hJw
  obtain ⟨blk₁, hb₁, hshw, -⟩ := h.member
  obtain rfl : bw.asBare = blk₁ := Option.some.inj (e17.symm.trans hb₁)
  have hr₂ : ((rest.drop blk.rounds.length).take bw.asBare.rounds.length).length = 2 := by
    rw [hl₂, hshw.2.1]
    rfl
  obtain ⟨r₁, r₂, er⟩ := List.length_eq_two.1
    (show (((rest.drop blk.rounds.length).take bw.asBare.rounds.length).map noDigest).length = 2 by
      rw [List.length_map]
      exact hr₂)
  rw [er] at hdec₂
  obtain ⟨msgW, l, ids, d', d, o, -, -, hlin, hrw, hlin', -⟩ := w_text hw' hdec₂
  obtain ⟨-, -, -, hoc, -⟩ := rows_ok hrw
  -- the seal leaves the state
  obtain ⟨-, gs₃, hdec₃⟩ := VerifiableInference.Desc.K1.step_ok _ _ s₂ _ _ _ _ hstep₃
  obtain ⟨-, -, hE⟩ := emap_ok (show Except.map _ _ = _ from hdec₃)
  obtain rfl : s₂ = _ := hE
  -- the weights
  obtain ⟨pre, epre, hpre⟩ := fold_rest 0 _ _ _ _ _ _ _ h1
  have hcut := fold_cut 0 _ _ _ _ _ _ _ h1 pre epre
  have hH := hF m.st.input.x pre cols t [] c hcut ((rest.take blk.rounds.length).map (·.drawn))
  rw [← List.map_append] at hH
  have hg := weights_of_back hw (seen := pre ++ rest.take blk.rounds.length) rfl hpre rfl hH hlay hbt
  -- the words
  have hl₀ : l = { claim := memberClaim out.1 } := (Option.some.inj hlin).symm
  subst hl₀
  have hA : ((pre ++ rest.take blk.rounds.length).map (·.drawn)).length =
      roundsTo (D Xs N Pl).first.blocksInOrder 17 := by
    have a := take_succ_some (show (D Xs N Pl).first.blocksInOrder[16]? = some blk from hb)
    unfold roundsTo declsTo
    rw [a, List.flatMap_append, List.length_append, List.length_map, List.length_append, hl₁, hpre]
    simp
  have hh : m.st.heard = (pre ++ rest.take blk.rounds.length).map (·.drawn) ++
      (rest.drop blk.rounds.length).map (·.drawn) := by
    rw [← hseen, epre, ← List.map_append, List.append_assoc, List.take_append_drop]
  obtain ⟨cc, hcc⟩ := w_cut (f := f) hK hs scope hJw hp.places.w k
  have hm := wit_msg h hcc _ hA ((rest.drop blk.rounds.length).map (·.drawn) ++ ds)
  let t₀ : State (In1 W₀ Rc) X' :=
    ⟨m.st.input, (pre ++ rest.take blk.rounds.length).map (·.drawn), m.st.own⟩
  have hI := wIs_held (matrixEntryOf f) (oneOf Xs) pieces (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW
    (keyPoints Xs N) (battAt Xs N) K.w hJw hw.answers hw.maskRows hw.mainDeg cc m.shown t₀ 0
    (fun _ _ _ => 0) mat hmat hw.bits hw.room
  have hrows := rowsLaid_part K.w K.own₀ h.data cc m.shown t₀ 0
  rw [Nat.sub_zero, List.take_length] at hrows
  refine ⟨o.1, hlin', fun e he => ?_⟩
  have hv : (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ ds) =
      (Fl Xs N Pl K f Q x).wit k w₀ rc ((pre ++ rest.take blk.rounds.length).map (·.drawn) ++
        ((rest.drop blk.rounds.length).map (·.drawn) ++ ds)) [] := by
    show (Fl Xs N Pl K f Q x).wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ ds) [] = _
    rw [hval, hh, List.append_assoc]
  have e₂ := val_first h ((Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ ds)) OnBytes.Part.main
    ((linLayW (oneOf Xs).codes (oneOf Xs).lin).index e)
  rw [hfirst] at e₂
  refine Eq.trans e₂ ?_
  rw [hv, hm]
  show held (fun _ _ _ => 0) K.w.first K.w.P
    (rowsLaid K.w K.own₀ cc (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) _) K.w.first OnBytes.Part.main
    ((linLayW (oneOf Xs).codes (oneOf Xs).lin).index e) = _
  rw [hfirst, ← hval, hrows, hoc]
  have hgg : (memberClaim out.1).g = out.1.g := rfl
  rw [hgg, hg]
  have hI' := hI e he
  rw [Nat.sub_zero, List.take_length] at hI'
  exact hI'

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.fold_cut
#print axioms AtPublicFiles.FirstH.w_cut
#print axioms AtPublicFiles.FirstH.w_is_at_stand
