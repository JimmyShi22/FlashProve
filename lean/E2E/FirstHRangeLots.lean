-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHRangeLots.lean: the two ties at `T₁`.

  `stand15`: at a stand at border 15 the group under test has message 1 alone, and message 1 has the
    sending's shape.
  `purse_of`: the sender's purse can be cut.
  `tb_is_sent`: `TbIsSent`, at every run.
  `wit_is_job`: `WitIsJob`, at every stand at border 15 and every lending to the test.

Limits. `MsgZero` and `CarryFits` are premises here; E2E/FirstHRangeClosed.lean pays them in scope. Nothing
on any property.
-/
import E2E.FirstHRangeTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces valOf pieces)
open VerifiableInference.Desc.Ground.Sh (stSh grp_get orc_get)
open Johnson.Prover.Send (shapeAt held)
open Johnson.RunOne.KeyRows1 (plan₁)
open AtPublicFiles.KeyThread (D one₀ laid₁ sentRanges rangesTestJob TbIsSent WitIsJob purse_cut)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (T15 shape15_of_thr core15 loc15 oneF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups multiplicitiesSending oneOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob dueR stepsOf dueMsg ce lentCut)
open ProofFile.Honest.K12 (restCoins restPart firstPart)
open ProofFile.Honest.K12.Light (lendRow_snd)

set_option synthInstance.maxHeartbeats 400000 in
theorem idx_one : (#[1] : Array Nat).idxOf? 1 = some 0 := by
  first
    | decide +kernel
    | (simp [Array.idxOf?, List.finIdxOf?_cons]; done)
    | (simp [Array.idxOf?, List.finIdxOf?_cons]; exact ⟨_, rfl, rfl⟩)

/-- Rounds in front grow with the border. -/
theorem roundsTo_le {S Cl : Type} (bs : List (Block S Cl)) {a b : Nat} (h : a ≤ b) :
    roundsTo bs a ≤ roundsTo bs b := by
  have e : bs.take a = (bs.take b).take a := by
    rw [List.take_take, Nat.min_eq_left h]
  unfold roundsTo declsTo
  rw [e]
  generalize bs.take b = l
  conv => rhs; rw [← List.take_append_drop a l]
  rw [List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : PublicFiles}

/-- **At a stand at border 15.** -/
theorem stand15 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K₀)} {s : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 15 k s m E) :
    (∀ G, s.d.st.groups[s.grp]? = some G → G.members = #[1]) ∧ ∃ y : OnBytes.Oracle,
      s.d.st.oracles[1]? = some y ∧
        y.shape = ((Wf.messageOf oneF.ranges).getD 0 default).shape := by
  have hsh := shape15_of_thr hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
    (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have h1 : stSh s.d.st = T15.1.st := congrArg (·.st) (congrArg Prod.fst hsh)
  have h2 : s.grp = 0 := (congrArg (·.2.grp) hsh).trans loc15.1
  have hok := t15_ok
  unfold T15Ok at hok
  rw [Bool.and_eq_true] at hok
  constructor
  · intro G hG
    have e : T15.1.st.groups[0]? = some (VerifiableInference.Desc.Ground.Sh.grpSh G) := by
      rw [← h1, grp_get, ← h2, hG]
      rfl
    have a := hok.1
    rw [e] at a
    simp only [Option.any_some, beq_iff_eq] at a
    have b : G.members.toList = [1] := a
    have c := congrArg List.toArray b
    simpa using c
  · have a := hok.2
    cases ho : T15.1.st.oracles[1]? with
    | none =>
      rw [ho] at a
      cases a
    | some z =>
      rw [ho] at a
      simp only [Option.any_some, beq_iff_eq] at a
      have e : (s.d.st.oracles[1]?).map VerifiableInference.Desc.Ground.Sh.orcSh = some z := by
        rw [← orc_get, h1, ho]
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨y, hy, a⟩

/-- **The sender's purse can be cut.** -/
theorem purse_of {J : SendJob (In1 W₀ Rc) X'} (hJ : J = multiplicitiesSending f Xs) (hK : fullPub = some K₀)
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (k : Coins (keyBook K₀)) :
    ∃ c, lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c := by
  subst hJ
  exact purse_cut Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 hK hs scope k

/-- **The thread's table is the sending's.** -/
theorem tb_is_sent (hp : FirstPublic (Pl := Pl) Xs N K f) (k : Coins (keyBook K₀))
    (m : Mid (In1 W₀ Rc) X') :
    TbIsSent Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 (Fl Xs N Pl K f Q x) w₀ rc x
      (keyProver K).first (tbH Xs N Pl K f Q) k m := by
  intro c₁ hc
  have ht : (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P.trees.length = 1 := by
    have e := hp.treesMsg
    rw [hp.msg] at e
    exact e
  exact tree_term hp.msg K.own₀ k m.st.input _ ht c₁ hc

/-- **Message 0 of the multiplicities' sending**: no coin in its main rows, and nothing rides on it. -/
structure MsgZero (J : SendJob (In1 W₀ Rc) X') : Prop where
  word : (stepsOf J.P.codes (shapeAt J.P 0) (J.ride 0)).word = 0
  pad : (stepsOf J.P.codes (shapeAt J.P 0) (J.ride 0)).pad = 0
  ride : J.ride 0 = none

/-- **The test reads the witness that the filling holds.** -/
theorem wit_is_job (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hz : MsgZero K.msg)
    (hshape : shapeAt K.msg.P 0 = ((Wf.messageOf oneF.ranges).getD 0 default).shape)
    (hcf : CarryFits (keyBook K₀) ⟨(rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place, 1⟩
      ⟨K.msg.P.place, 0⟩ (dueMsg K.msg.P.codes (shapeAt K.msg.P 0) (K.msg.ride 0))
      (dueR K.msg.P K.msg.ride) = true)
    {k : Coins (keyBook K₀)} {s : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 15 k s m E)
    (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0) :
      Part (In1 W₀ Rc) (In1 W₀ Rc) X'), restPart (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place
      [(firstPart (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0) :
        Part (In1 W₀ Rc) (In1 W₀ Rc) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)] 0 = .ok c) :
    WitIsJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 (Fl Xs N Pl K f Q x) k s m
      (restCoins (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0) c.2.1) := by
  have hv : m.st.input = ⟨w₀, rc, x, ()⟩ := hT.2.2.2.2.2.2.1
  have hseat := seat_msg (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  have hfirst : K.msg.first = 1 := by
    rw [hp.msg]
    rfl
  obtain ⟨own, hown⟩ := purse_of hp.msg hK hs scope k
  obtain ⟨hmem, y₀, hy₀, hsh₀⟩ := stand15 (K := K) (f := f) (Q := Q) hs scope hT
  have hlen : roundsTo (D Xs N Pl).first.blocksInOrder 1 ≤ m.st.heard.length := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    have e' : m.st.heard.length = roundsTo (D Xs N Pl).first.blocksInOrder 15 := e.trans (Nat.zero_add _)
    rw [e']
    exact roundsTo_le _ (by decide)
  refine ⟨rfl, fun G hG pt i _ => ?_⟩
  have hpre : (m.st.heard.take (roundsTo (D Xs N Pl).first.blocksInOrder 1)).length =
      roundsTo (D Xs N Pl).first.blocksInOrder 1 := by
    rw [List.length_take, Nat.min_eq_left hlen]
  have hm := wit_msg hseat hown _ hpre (m.st.heard.drop (roundsTo (D Xs N Pl).first.blocksInOrder 1))
  rw [List.take_append_drop] at hm
  have hw : (Fl Xs N Pl K f Q x).wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ []) [] =
      (Fl Xs N Pl K f Q x).wit k w₀ rc m.st.heard [] := by
    rw [List.append_nil, hv]
  have e₁ := val_first hseat ((Fl Xs N Pl K f Q x).wit k w₀ rc m.st.heard []) pt i
  rw [hfirst] at e₁
  show readE (valOf (plan₁ (one₀ Xs)) readH
    ((Fl Xs N Pl K f Q x).wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ []) []) 1 pt i) = _
  rw [hw, e₁, hm]
  -- the statement under test
  have hsh₁ : ((OnBytes.Slice.begun s.d.st s.grp G).oracles[1]?).map (·.shape) =
      some y₀.shape := by
    have e := close_shape G.members.toList s.d.st 1
    rw [hy₀] at e
    exact e
  obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hsh₁
  have hrest := lendRow_snd _ _ _ _ _ _ _ hc
  have hcut : ((k.look 0) ⟨K.msg.P.place, 0⟩).2.cut ⟨0, 0⟩ (dueR K.msg.P K.msg.ride) = some own := hown
  have hcap : (dueMsg K.msg.P.codes (shapeAt K.msg.P 0) (K.msg.ride 0)).e ≤
      (dueR K.msg.P K.msg.ride).e := by
    have h2 := hcf
    unfold CarryFits at h2
    split at h2
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact h2.2
    · cases h2
  have hmembers := hmem G hG
  show held (fun _ _ _ => 0) K.msg.first K.msg.P
    (ProofFile.Honest.K1.rowsLaid K.msg K.own₀ own (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) _) K.msg.first pt i = _
  rw [← hv]
  refine words_core hp.msg K.own₀ _ _ own _ _ _ _ y hfirst ?_ hy (by rw [hys, hsh₀, hshape]) ?_
    ⟨hz.word, hz.pad⟩ hz.ride hcap ?_ pt i
  · show (G.members).idxOf? 1 = some 0
    rw [hmembers]
    exact idx_one
  · have e := hseat.sent
    exact e
  · exact carried_read _ _ hrest hcf hcut

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.roundsTo_le
#print axioms AtPublicFiles.FirstH.stand15
#print axioms AtPublicFiles.FirstH.purse_of
#print axioms AtPublicFiles.FirstH.tb_is_sent
#print axioms AtPublicFiles.FirstH.wit_is_job
