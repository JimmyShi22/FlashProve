-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindClaims.lean: THE STEP "7.claims" OF AN ATTENTION SEGMENT, AS
Johnson/Desc/First/Batch/ClaimsAtS.lean MAKES IT
(claimsRuns: K3's own block with its caller's "planes"; K5's list runsO at the seat seatCO): EVERY
RUN OF THAT LIST IS BLIND TO THE REAL ADDING, AND SO THE STEP's FORM ("made first, then added") ENDS
WHERE "made and added" ENDS: NO PREMISE ON A RUN IS LEFT. No Mathlib. (A list made over another seat
of K5's wants that seat's SeatQuiet, and the like of runsO_blind.)
  `runsBy_mem`: a run of a list made by runsBy is stated by one of the blocks.
  `theOwn_blind`: every run that K3's own block states (K3.theOwn, with its runs) is Blind.
  `runsO_blind`: every run of K5's list with K3's "join" in it (Att/SeatO.lean: runsO), its forms
      as claims (Johnson/Desc/First/Batch/ClaimsAtS.lean: runOfForms), is Blind.
  `statesAtt_blind` · `claimsRuns_blind`: so is every run of the step's list.
  `claims_made_first`: **the step's law.** `claimsAt_law`: the same, of the block itself: just
      if, under three premises. `claimsAt_yes`: ONE WAY, WITHOUT THEM: a yes of the block
      is a yes of "made and added": what a road "a yes gives ..." wants.
Limits: laws on two programs' ends at one step of one sort of segment; `claimsAt_law` under three
premises that nobody pays yet. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.BlindAttO
import Johnson.Desc.First.Batch.ClaimsAtS
import Johnson.Desc.First.Batch.ObjectsLawAdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (seatCO parCOf ParC)

/-- The real adding. -/
abbrev realAdds : Adds S := addsOf atS atS_ok

theorem runsBy_mem {T : Type} (states : Nat → List (RunOf T)) : ∀ (cut : List (Nat × String))
    (runs : List (RunOf T)), runsBy states cut = some runs →
    ∀ r ∈ runs, ∃ b, r ∈ states b := by
  intro cut
  induction cut with
  | nil =>
    intro runs h r hr
    simp [runsBy, pure] at h
    subst h
    cases hr
  | cons o l ih =>
    intro runs h r hr
    unfold runsBy at h
    rw [List.mapM_cons] at h
    cases hf : (states o.1).find? (fun r => r.1 == o.2) with
    | none => simp [hf] at h
    | some x =>
      cases hl : l.mapM (fun o => (states o.1).find? fun r => r.1 == o.2) with
      | none => simp [hf, hl] at h
      | some rs =>
        simp [hf, hl, pure] at h
        subst h
        cases hr with
        | head => exact ⟨o.1, List.mem_of_find?_eq_some hf⟩
        | tail _ hr' => exact ih rs hl r hr'

/-! ## K3's own block -/

/-- "guests" where no guest is handed is guestsNone. -/
theorem guests_is (n : Nat) (s : S) :
    (named "K3 guests: a guest refuses"
      ((([] : List (First.Look.Guest S Claim)).mapM
        fun (g : First.Look.Guest S Claim) => g.form s).map fun l => (l, s)) :
        Except String (List Claim × S)) = guestsNone n s := rfl

/-- Every run that K3.block states with no guest, at either seat, is Blind. -/
theorem block_blind (digits : Bool) (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) :
    ∀ r ∈ (K3.block (if digits then K3.seatDigits ofForm else K3.seatCalls ofForm) piece laid
      before p []).claims, Blind realAdds r.2 := by
  intro r hr
  cases digits with
  | false =>
    have hr' : r ∈ [("objects", objectsCalls), ("guests", guestsNone)] := hr
    have : r = ("objects", objectsCalls) ∨ r = ("guests", guestsNone) := by
      simpa using hr'
    cases this with
    | inl h => rw [h]; exact objectsCalls_blind
    | inr h => rw [h]; exact guestsNone_blind
  | true =>
    have hr' : r ∈ [("objects", objectsDigits), ("guests", guestsNone)] := hr
    have : r = ("objects", objectsDigits) ∨ r = ("guests", guestsNone) := by
      simpa using hr'
    cases this with
    | inl h => rw [h]; exact objectsDigits_blind
    | inr h => rw [h]; exact guestsNone_blind

theorem theOwn_blind (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (b : Block S Claim) (h : K3.theOwn ofForm true X codes shape a = some b) :
    ∀ r ∈ b.claims, Blind realAdds r.2 := by
  unfold K3.theOwn at h
  split at h
  · simp at h
  · obtain ⟨i, _, h1⟩ := bind_some h
    obtain ⟨digits, _, h2⟩ := List.exists_of_findSome?_eq_some h1
    split at h2
    · simp at h2
    · obtain ⟨p, _, h3⟩ := bind_some h2
      obtain ⟨sent, _, h4⟩ := bind_some h3
      obtain ⟨laid, _, h5⟩ := bind_some h4
      obtain ⟨key, _, h6⟩ := map_some h5
      rw [← h6]
      exact block_blind digits a.piece laid sent p

/-! ## K5's list -/

theorem first_is (seat : First.Att.P.SeatC S) (c : ParC) :
    (runOfForms ("first", fun _ s => named "K5.first" (First.Att.P.firstK seat c s))).2 =
      firstAt seat c := by
  funext n s
  simp only [runOfForms, firstAt, readRun, asClaimsOf, First.Att.P.firstK]
  cases First.Att.P.inOf seat c s with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    cases hq : First.Att.P.Runs.firstRun i K <;>
      simp [hq, named, Except.map, bind, Option.bind, ofForm, pure]

theorem keys_is (seat : First.Att.P.SeatC S) (c : ParC) :
    (runOfForms ("keys", fun _ s => named "K5.keys" (First.Att.P.keysK seat c s))).2 =
      keysAt seat c := by
  funext n s
  simp only [runOfForms, keysAt, readRun, asClaimsOf, First.Att.P.keysK]
  cases First.Att.P.keysOfK seat c s <;> rfl

theorem second_is (seat : First.Att.P.SeatC S) (c : ParC) :
    (runOfForms ("second", fun _ s => named "K5.second" (First.Att.P.secondK seat c s))).2 =
      secondAt seat c := by
  funext n s
  simp only [runOfForms, secondAt, readRun, asClaimsOf, First.Att.P.secondK]
  cases First.Att.P.inOf seat c s with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    cases hq : First.Att.P.Runs.secondRun i K <;>
      simp [hq, named, Except.map, bind, Option.bind, ofForm, pure]

/-- "join" as K5's list holds it (forms; then as claims) is joinCalls. -/
theorem join_is (keys : S → Option (Array Aff)) :
    (runOfForms ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)).2 = joinCalls keys := by
  funext n s
  simp only [runOfForms, joinCalls, flRun, K3.joinRun, K3.seatCalls, bind, Except.bind]
  cases s.fork? with
  | none => rfl
  | some F =>
    simp only [named]
    cases s.lookHeard? with
    | none => rfl
    | some g =>
      dsimp only
      cases K3.unpaid F g.owedJoin with
      | false => rfl
      | true =>
        simp only [need, VerifiableInference.Desc.need, if_true]
        cases keys s with
        | none => rfl
        | some KF =>
          dsimp only
          cases First.Look.joinF g KF F [] <;> rfl

theorem runsO_blind (A : Attention.Plan) :
    ∀ r ∈ (First.Att.P.runsO A).map runOfForms, Blind realAdds r.2 := by
  intro r hr
  have : r = runOfForms ("first", fun _ s => named "K5.first"
        (First.Att.P.firstK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("keys", fun _ s => named "K5.keys"
        (First.Att.P.keysK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id)
        (First.Att.P.keysOfO A)) ∨
      r = runOfForms ("second", fun _ s => named "K5.second"
        (First.Att.P.secondK (seatCO (parCOf A)) (parCOf A) s)) := by
    simpa [First.Att.P.runsO, First.Att.P.runsK] using hr
  rcases this with h | h | h | h
  · rw [h, first_is]; exact firstAt_blind _ (seatCO_quiet _) _
  · rw [h, keys_is]; exact keysAt_blind _ (seatCO_quiet _) _
  · rw [h, join_is]; exact joinAttO_blind A
  · rw [h, second_is]; exact secondAt_blind _ (seatCO_quiet _) _

/-! ## the step's list -/

theorem k3CallsWith_blind (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (A : Attention.Plan) (b : Block S Claim) (h : k3CallsWith X codes shape i A = some b) :
    ∀ r ∈ b.claims, Blind realAdds r.2 := by
  unfold k3CallsWith at h
  obtain ⟨p, _, h1⟩ := bind_some h
  obtain ⟨b₀, hb₀, h2⟩ := map_some h1
  rw [← h2]
  intro r hr
  have : r ∈ b₀.claims ∨ r = ("planes", planesCalls p.lm (First.Att.P.readersOfO A)) := by
    simpa [K3.withCaller, planesCalls_is, ofForm] using hr
  cases this with
  | inl h' => exact theOwn_blind X codes shape _ b₀ hb₀ r h'
  | inr h' => rw [h']; exact planesAttO_blind p.lm A

theorem statesAtt_blind (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (A : Attention.Plan) (b : Nat) : ∀ r ∈ statesAtt X codes shape i A b, Blind realAdds r.2 := by
  intro r hr
  unfold statesAtt at hr
  split at hr
  · split at hr
    · cases hk : k3CallsWith X codes shape i A with
      | none => simp [hk] at hr
      | some x =>
        simp only [hk, Option.map, Option.getD] at hr
        exact k3CallsWith_blind X codes shape i A x hk r hr
    · cases hr
  · exact runsO_blind A r hr
  · cases hr

/-- **Every run of the real list of "7.claims" is Blind to the real adding.** -/
theorem claimsRuns_blind (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (runs : List (RunOf S)) (h : claimsRuns X codes shape i = some runs) :
    ∀ r ∈ runs, Blind realAdds r.2 := by
  unfold claimsRuns at h
  obtain ⟨A, _, h1⟩ := bind_some h
  intro r hr
  obtain ⟨b, hb⟩ := runsBy_mem _ _ _ h1 r hr
  exact statesAtt_blind X codes shape i A b r hb

/-- An adding does not turn the smallness test's window. -/
theorem k8Window_unturned (k : SegSort) (t t' : S) (cs : List Claim)
    (h : realAdds.add t cs = some t') : k8Window k t' = k8Window k t := by
  obtain ⟨p, _, hq⟩ := bind_some (show (atS.get? t).bind _ = some t' from h)
  obtain ⟨G, _, ht'⟩ := map_some hq
  rw [← ht']
  unfold k8Window
  rw [(set_heard t { p with F := G }).2]

/-- **THE STEP's LAW: "7.claims" AT A REAL ATTENTION SEGMENT: "made first, then added", with the
window asked behind each run, ends in v JUST IF "made and added" ends in v. NO PREMISE ON A RUN.**
t₀: the state behind the idle adding. -/
theorem claims_made_first (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (runs : List (RunOf S)) (h : claimsRuns X codes shape i = some runs) (t t₀ : S)
    (h0 : realAdds.add t [] = some t₀) (v : S) :
    madeThenAdded realAdds
        (runs.map (guarded (k8Window .attention) (cutAt .attention 0))) t = .ok v ↔
      madeAndAdded realAdds
        (runs.map (guarded (k8Window .attention) (cutAt .attention 0))) t₀ = .ok v := by
  refine made_first_iff realAdds _ ?_ t t₀ h0 v
  intro f hf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
  exact guarded_blind realAdds _ _ r (claimsRuns_blind X codes shape i runs h r hr)
    (k8Window_unturned .attention)

/-- The step's block decides as K9.adds over the gathering does: the step has no count in front and
reads nothing behind. -/
theorem stepIsAdds {Cl : Type} (i piece : Nat) (runs : List (RunOf S)) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (v : S) :
    (addsStep (Cl := Cl) atS ⟨1, i, piece, piece, 0, 0, 0⟩ "the attention segment's" []
      (k8Window .attention) (cutAt .attention 0) (id runs) pure).decide t rs gs = .ok v ↔
    (adds (Cl := Cl) atS ⟨1, i, piece, piece, 0, 0, 0⟩ piece "the attention segment's"
      (gather (k8Window .attention) (cutAt .attention 0) runs)).decide t rs gs = .ok v := by
  rw [addsStep_decide]
  simp only [countsHold, id, List.forM_nil, bind, Except.bind, pure, Except.pure]
  cases (adds (Cl := Cl) atS ⟨1, i, piece, piece, 0, 0, 0⟩ piece "the attention segment's"
    (gather (k8Window .attention) (cutAt .attention 0) runs)).decide t rs gs <;>
    first | exact Iff.rfl | simp [pure, Except.pure]

/-- **ONE WAY, OF THE BLOCK ITSELF, WITHOUT A PREMISE ON MARKS OR ON THE DRAW:** where the
block that Johnson/Desc/First/Batch/ClaimsAtS.lean makes for the step says yes and ends in v, "made
and added" over the step's own list ends in v. t₀: the state behind the idle adding: that it returns
is a premise. -/
theorem claimsAt_yes {Cl : Type} (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (i piece : Nat) (b : Block S Cl) (hb : claimsAtWith id X codes shape i piece = some b)
    (runs : List (RunOf S)) (hr : claimsRuns X codes shape i = some runs) (t t₀ : S)
    (hi : realAdds.add t [] = some t₀) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (v : S) (hy : b.decide t rs gs = .ok v) :
    madeAndAdded realAdds
      (runs.map (guarded (k8Window .attention) (cutAt .attention 0))) t₀ = .ok v := by
  unfold claimsAtWith at hb
  obtain ⟨A, _, h1⟩ := bind_some hb
  rw [hr] at h1
  have h2 : some _ = some b := h1
  injection h2 with h3
  rw [← h3] at hy
  exact (claims_made_first X codes shape i runs hr t t₀ hi v).1
    (adds_yes atS atS_ok ⟨1, i, piece, piece, 0, 0, 0⟩ piece "the attention segment's"
      (k8Window .attention) (cutAt .attention 0) runs t rs gs v
      ((stepIsAdds i piece runs t rs gs v).1 hy))

/-- **THE SAME, OF THE BLOCK ITSELF:** the block that Johnson/Desc/First/Batch/ClaimsAtS.lean makes
for the step says yes and ends in v JUST IF "made and added" over the step's own list ends in v:
behind "a segment is open" and "the draw has run", and where there is a mark behind the gathering.
-/
theorem claimsAt_law {Cl : Type} (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (i piece : Nat) (b : Block S Cl) (hb : claimsAtWith id X codes shape i piece = some b)
    (runs : List (RunOf S)) (hr : claimsRuns X codes shape i = some runs) (t t₀ : S) (s₀ : Part)
    (h0 : atS.get? t = some s₀) (hd : s₀.L.handed = true)
    (hi : realAdds.add t [] = some t₀)
    (hm : MarkedBehind atS (runs.map (guarded (k8Window .attention) (cutAt .attention 0))) t)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (v : S) :
    b.decide t rs gs = .ok v ↔
      madeAndAdded realAdds
        (runs.map (guarded (k8Window .attention) (cutAt .attention 0))) t₀ = .ok v := by
  unfold claimsAtWith at hb
  obtain ⟨A, _, h1⟩ := bind_some hb
  rw [hr] at h1
  have h2 : some _ = some b := h1
  injection h2 with h3
  rw [← h3, ← claims_made_first X codes shape i runs hr t t₀ hi v,
    ← adds_is_madeThen (Cl := Cl) atS atS_ok ⟨1, i, piece, piece, 0, 0, 0⟩ piece
      "the attention segment's" (k8Window .attention) (cutAt .attention 0) runs t rs gs s₀ h0 hd
      hm v]
  show (addsStep (Cl := Cl) atS ⟨1, i, piece, piece, 0, 0, 0⟩ "the attention segment's" []
    (k8Window .attention) (cutAt .attention 0) (id runs) pure).decide t rs gs = .ok v ↔ _
  rw [addsStep_decide]
  simp only [countsHold, id, List.forM_nil, bind, Except.bind, pure, Except.pure]
  cases (adds (Cl := Cl) atS ⟨1, i, piece, piece, 0, 0, 0⟩ piece "the attention segment's"
    (gather (k8Window .attention) (cutAt .attention 0) runs)).decide t rs gs <;>
    first | exact Iff.rfl | simp [pure, Except.pure]

end VerifiableInference.Desc.K9
