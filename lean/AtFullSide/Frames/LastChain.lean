-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Frames/LastChain.lean: what is proved at the last chain's two frame members, number 1 (the
taken trees' sources) and number 3 (the chain's end), at the term lastThread
(Honest/Thread/TheFirstThread.lean). Neither member has a round and neither turns the state.

With no premise:
  last_frames        these two are the chain's only members of the kind frame
  last_plays, last_exchange   PlaysS and ExchangeS at both
  last_rides_three   RidesPastS at 3: nothing stays open past it
  form_two, form_four   the form behind each member, where the invariant holds in front and the step
                     accepts (step_one, step_three, Johnson/Desc/Last/ShapeGives.lean)

Joins, which are NOT the five statements at these members: last_one and last_three pass on as
premises what the thread's letters parts.rides, parts.keeps and parts.meaning have to give (rides
and keeps behind the member; that a pin stays when rounds are added; that keeps leaves the item
rows) and the very condition of each step's acceptance (Tied at 1; shape₃, Older and Listed at 3).
These letters have no value here (a value of their type: `lastParts`,
Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean; at the run:
AtFullSide/Honest/TheLettersLast.lean), and that a reached state has these conditions is not shown
here.

Limits. Each statement assumes that the thread's invariant holds in front of the member; that it holds
at any border of any run is not shown.
-/
import Johnson.Desc.Last.ShapeGives
import Johnson.Desc.Last.ShapeAtTable
import Johnson.Desc.Last.ShapeRowZero
import Johnson.Desc.ProofFile.Honest.Thread.FrameMembers
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Frames
open VerifiableInference.Desc (Block Place KindName step_inv)
open VerifiableInference.Desc.Third (S₃ takenSources end₃)
open VerifiableInference.Desc.Last (ItemL lastPlaces shapeAt step_one step_three startLast)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.LastThread (lettersLast)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The last thread's block at number 1, and what it decides. -/
theorem last_block_one : ∃ blk, (lastThread h first reads parts w).bs[1]? = some blk ∧
    blk.rounds = [] ∧ blk.oracles = [] ∧
    ∀ s rs gs, blk.decide s rs gs = (takenSources (ownZ h.places)).decide s rs gs :=
  ⟨_, rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- The last thread's block at number 3, and what it decides. -/
theorem last_block_three : ∃ blk, (lastThread h first reads parts w).bs[3]? = some blk ∧
    blk.rounds = [] ∧ blk.oracles = [] ∧
    ∀ s rs gs, blk.decide s rs gs =
      (end₃ (Cl := Unit) []).decide s rs gs :=
  ⟨_, rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- What the form reads of the first chain's end. -/
def handLast (a : ProofFile.InstPub × P5J.TS) : Option VerifiableInference.Desc.Last.Handed :=
  VerifiableInference.Desc.Third.firstOfS a.2

/-- What the form reads of the shared chain's end. -/
def endedLast (e : Desc.K14.St) : Option VerifiableInference.Desc.Third.SharedOut :=
  (Desc.K14.ended e).map VerifiableInference.Desc.Third.sharedOfEnd

/-- **The shape at a border, from the form there.** -/
theorem shape_of_form {b : Nat} {k : Coins A.B} {s : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lastThread h first reads parts w).Form b k s m) :
    ∃ f o, handLast ((lastThread h first reads parts w).seat k m s).1.1 = some f ∧
      endedLast ((lastThread h first reads parts w).seat k m s).1.2 = some o ∧
      shapeAt (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds b f o s = true := by
  obtain ⟨h1, -⟩ := hF
  have h2 : (h.lastForm.shape b ((lastThread h first reads parts w).seat k m s).1.1
      ((lastThread h first reads parts w).seat k m s).1.2 s &&
    (!decide (lastPlaces.length ≤ b) || h.lastForm.nothingLeft s)) = true := h1
  rw [Bool.and_eq_true] at h2
  exact VerifiableInference.Desc.Last.shapeAt_of_fill _ _ handLast endedLast h2.1

/-- **The form at a border of the chain, from the shape at it.** -/
theorem form_behind {b : Nat} (hb : b < 4) {k : Coins A.B} {s : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {f : VerifiableInference.Desc.Last.Handed} {o : VerifiableInference.Desc.Third.SharedOut}
    (hh : handLast ((lastThread h first reads parts w).seat k m s).1.1 = some f)
    (he : endedLast ((lastThread h first reads parts w).seat k m s).1.2 = some o)
    (h3 : shapeAt (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds b f o s = true)
    (ho : OnBytes.Means.InOrder s.st) : (lastThread h first reads parts w).Form b k s m := by
  refine ⟨?_, ho⟩
  show (h.lastForm.shape b ((lastThread h first reads parts w).seat k m s).1.1
      ((lastThread h first reads parts w).seat k m s).1.2 s &&
    (!decide (lastPlaces.length ≤ b) || h.lastForm.nothingLeft s)) = true
  have e : (!decide (lastPlaces.length ≤ b)) = true := by
    have : ¬ lastPlaces.length ≤ b := by
      show ¬ 4 ≤ b
      omega
    simp [this]
  rw [e, Bool.true_or, Bool.and_true]
  show (match handLast ((lastThread h first reads parts w).seat k m s).1.1,
      endedLast ((lastThread h first reads parts w).seat k m s).1.2 with
    | some h', some o' => shapeAt (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds b h' o' s
    | _, _ => false) = true
  rw [hh, he]
  exact h3

/-- What keeps says at number 1: the letter at the member's place. -/
theorem keeps_one {s s' : S₃} (hk : parts.keeps ⟨3, none, 1, .frame⟩ s s') :
    (lastThread h first reads parts w).keeps 1 s s' := by
  intro p hp
  obtain rfl : (⟨3, none, 1, .frame⟩ : Place) = p := Option.some.inj hp
  show ProofFile.Honest.K14.kpSecond _ _ _ _ _
  unfold ProofFile.Honest.K14.kpSecond
  rw [if_neg (by decide)]
  exact hk

/-- What keeps says at number 3. -/
theorem keeps_three {s s' : S₃} (hk : parts.keeps ⟨3, none, 3, .frame⟩ s s') :
    (lastThread h first reads parts w).keeps 3 s s' := by
  intro p hp
  obtain rfl : (⟨3, none, 3, .frame⟩ : Place) = p := Option.some.inj hp
  show ProofFile.Honest.K14.kpSecond _ _ _ _ _
  unfold ProofFile.Honest.K14.kpSecond
  rw [if_neg (by decide)]
  exact hk

/-- **The last chain's members of the kind frame are numbers 1 and 3.** -/
theorem last_frames : (List.range lastPlaces.length).filter
    (fun b => (lastPlaces[b]?.map (·.kind)) == some KindName.frame) = [1, 3] := by
  decide

/-- **PlaysS at both members.** -/
theorem last_plays : PlaysS (lastThread h first reads parts w) Said 1 ∧
    PlaysS (lastThread h first reads parts w) Said 3 := by
  obtain ⟨_, b1, r1, o1, -⟩ := last_block_one h first reads parts w
  obtain ⟨_, b3, r3, o3, -⟩ := last_block_three h first reads parts w
  exact ⟨playsS_of _ _ (plays_quiet _ b1 r1 o1), playsS_of _ _ (plays_quiet _ b3 r3 o3)⟩

/-- **ExchangeS at both members**: their rows owe nothing. -/
theorem last_exchange : ExchangeS (lastThread h first reads parts w) Said 1 ∧
    ExchangeS (lastThread h first reads parts w) Said 3 :=
  ⟨exchangeS_nil _ _ rfl, exchangeS_nil _ _ rfl⟩

/-- **RidesPastS at number 3**: nothing is open past it. -/
theorem last_rides_three : RidesPastS (lastThread h first reads parts w) Said 3 := by
  intro k s m E s' ps i v _ _ hi hs _ _
  have e : ∀ j ∈ fwdOpen startLast LastRows.rows 3, j ∈ (LastRows.rows 3).shuts := by decide
  exact absurd (e i hi) hs

/-- **The form behind number 1.** -/
theorem form_two {k : Coins A.B} {s s' : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hform : (lastThread h first reads parts w).Form 1 k s m)
    {gs : List (List (Nat × List UInt64))}
    (hdec : (takenSources (ownZ h.places)).decide s [] gs = .ok s') :
    s' = s ∧ (lastThread h first reads parts w).Form 2 k s m := by
  obtain ⟨f, o, hf, hoo, h2⟩ := shape_of_form h first reads parts w hform
  have h3 := step_one (ownZ h.places) h2 [] gs hdec
  obtain ⟨e, -⟩ := (VerifiableInference.Desc.Third.Law.takenSources_exact (ownZ h.places) s [] gs
    s').1 hdec
  subst e
  exact ⟨rfl, form_behind h first reads parts w (by omega) hf hoo h3 hform.2⟩

/-- **The join at number 1.** Not the five statements: see the head of this file. -/
theorem last_one
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hRows : ∀ s s' v, (lastThread h first reads parts w).keeps 1 s s' →
      h.lastMeaning.rows s v → h.lastMeaning.rows s' v)
    (hnext : ∀ k s m E, ThrS (lastThread h first reads parts w) Said 1 k s m E →
      parts.rides 2 m.st.input s ∧ parts.keeps ⟨3, none, 1, .frame⟩ s s)
    (hTied : ∀ k s m E, ThrS (lastThread h first reads parts w) Said 1 k s m E →
      VerifiableInference.Desc.Third.Law.Tied (ownZ h.places) s)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    PlaysS (lastThread h first reads parts w) Said 1 ∧
      BehindS (lastThread h first reads parts w) Said 1 ∧
      ExchangeS (lastThread h first reads parts w) Said 1 ∧
      RidesPastS (lastThread h first reads parts w) Said 1 ∧
      AcceptedS (lastThread h first reads parts w) Said fall 1 := by
  obtain ⟨blk, hblk, hr, ho, hd⟩ := last_block_one h first reads parts w
  refine ⟨playsS_of _ _ (plays_quiet _ hblk hr ho), ?_, exchangeS_nil _ _ rfl, ?_, ?_⟩
  · refine behindS_quiet _ _ hblk hr fun k s m E s' hA hst => ?_
    obtain ⟨-, -, -, hdec⟩ := step_inv _ _ _ _ _ _ _ hst
    rw [hd] at hdec
    obtain ⟨e, hF⟩ := form_two h first reads parts w hA.1.2.2.1 hdec
    subst e
    exact ⟨hF, (hnext k _ m E hA).1, keeps_one h first reads parts w (hnext k _ m E hA).2⟩
  · intro k s m E s' ps i v _ hK hi hs _ hv
    have hi' : i ∈ [ItemL.pinI, .pinV, .pinO, .rows] := hi
    cases i with
    | ev => exact absurd hi' (show ItemL.ev ∉ [ItemL.pinI, .pinV, .pinO, .rows] by decide)
    | dot => exact absurd hi' (show ItemL.dot ∉ [ItemL.pinI, .pinV, .pinO, .rows] by decide)
    | pinV => exact hPin₁ _ _ _ _ _ _ _ hv
    | pinI => exact hPin₁ _ _ _ _ _ _ _ hv
    | pinO => exact hPin _ _ _ _ _ _ _ hv
    | rows => exact hRows _ _ _ hK hv
  · exact acceptedS_takenSources _ Said rfl hTied

/-- **The form behind the chain's end.** -/
theorem form_four {k : Coins A.B} {s : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {f : VerifiableInference.Desc.Last.Handed} {o : VerifiableInference.Desc.Third.SharedOut}
    (hh : handLast ((lastThread h first reads parts w).seat k m s).1.1 = some f)
    (he : endedLast ((lastThread h first reads parts w).seat k m s).1.2 = some o)
    (h4 : shapeAt (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds 4 f o s = true)
    (hn : (VerifiableInference.Desc.ChainEnd.untestedL s.st).all (·.2) = true)
    (ho : OnBytes.Means.InOrder s.st) : (lastThread h first reads parts w).Form 4 k s m := by
  refine ⟨?_, ho⟩
  show (h.lastForm.shape 4 ((lastThread h first reads parts w).seat k m s).1.1
      ((lastThread h first reads parts w).seat k m s).1.2 s &&
    (!decide (lastPlaces.length ≤ 4) || h.lastForm.nothingLeft s)) = true
  have e : h.lastForm.nothingLeft s = true := hn
  rw [e, Bool.or_true, Bool.and_true]
  show (match handLast ((lastThread h first reads parts w).seat k m s).1.1,
      endedLast ((lastThread h first reads parts w).seat k m s).1.2 with
    | some h', some o' => shapeAt (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds 4 h' o' s
    | _, _ => false) = true
  rw [hh, he]
  exact h4

/-- **The join at number 3.** Not the five statements: see the head of this file. -/
theorem last_three
    (hnext : ∀ k s m E, ThrS (lastThread h first reads parts w) Said 3 k s m E →
      parts.rides 4 m.st.input s ∧ parts.keeps ⟨3, none, 3, .frame⟩ s s)
    (S : OnBytes.Params.LinShape) (a n g t : Nat) (idx : List Nat)
    (hEnd : ∀ k s m E, ThrS (lastThread h first reads parts w) Said 3 k s m E →
      LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true ∧
        AtPublicFiles.AtFiles.Older n g s.st ∧ AtPublicFiles.AtFiles.Listed s.st)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    PlaysS (lastThread h first reads parts w) Said 3 ∧
      BehindS (lastThread h first reads parts w) Said 3 ∧
      ExchangeS (lastThread h first reads parts w) Said 3 ∧
      RidesPastS (lastThread h first reads parts w) Said 3 ∧
      AcceptedS (lastThread h first reads parts w) Said fall 3 := by
  obtain ⟨blk, hblk, hr, ho, hd⟩ := last_block_three h first reads parts w
  refine ⟨playsS_of _ _ (plays_quiet _ hblk hr ho), ?_, exchangeS_nil _ _ rfl, ?_, ?_⟩
  · refine behindS_quiet _ _ hblk hr fun k s m E s' hA hst => ?_
    obtain ⟨-, -, -, hdec⟩ := step_inv _ _ _ _ _ _ _ hst
    rw [hd] at hdec
    have hform := hA.1.2.2.1
    obtain ⟨f, o, hf, hoo, h2⟩ := shape_of_form h first reads parts w hform
    obtain ⟨h4, hn⟩ := step_three h2 ([] : List (Block S₃ Unit)) [] [] hdec
    obtain ⟨e, -⟩ := VerifiableInference.Desc.Last.end₃_yes ([] : List (Block S₃ Unit)) s s' [] [] hdec
    subst e
    exact ⟨form_four h first reads parts w hf hoo h4 hn hform.2, (hnext k _ m E hA).1,
      keeps_three h first reads parts w (hnext k _ m E hA).2⟩
  · exact last_rides_three h first reads parts w Said
  · exact acceptedS_end₃ _ Said rfl S a n g t idx hEnd

end AtFullSide.Frames

#print axioms AtFullSide.Frames.last_frames
#print axioms AtFullSide.Frames.last_plays
#print axioms AtFullSide.Frames.last_exchange
#print axioms AtFullSide.Frames.last_rides_three
#print axioms AtFullSide.Frames.form_two
#print axioms AtFullSide.Frames.last_one
#print axioms AtFullSide.Frames.last_three
