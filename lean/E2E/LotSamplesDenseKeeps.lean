-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotSamplesDenseKeeps.lean: the mark on sample rows (`stSamplesB`, no sample row has a written-out
factor) along two stretches of the key file's chains, from each block's own accept. Steps of the
verifier's: no prover is named.

  `quiet_sam`   the ground's eight plain functions keep the mark.
  `layRows_sam`, `decideSend_sam`   a sending keeps it: the rows that it admits are plain.
  `shared_members`, `shared_fold`   every member of the shared chain's flat list, and the fold.
  `first_back_members`, `first_back_fold`   the ranges' test and all that stands behind it on the
      first chain, and the fold.

The two folds ask that the proximity tests' places have `early = true` and `answers = 1`.
Limits. Nothing on whether a fold returns. Of rows, form alone. Open rows are not touched. The first
chain in front of the ranges' test is not here. Nothing on soundness, completeness or hiding.
-/
import E2E.KeyShapeRanges
import E2E.KeyShapeShared
import Johnson.Desc.ProofFile.Honest.K12.PlainAtEight
import Johnson.Desc.K12.Honest.Shape.TestMarksMore
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K14.Quiet
import Johnson.Desc.K12.Law.SitsKeyChains
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain.Lots.Walk
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Desc.K14
open VerifiableInference.Desc VerifiableInference.Desc.Ground VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Keeps
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts P12)
open VerifiableInference.Desc.Key (FirstState rangesTest enterRanges leaveRanges rangesParams
  batchTableRows sendW firstChainEnd batchLens layPile sendingSeat quietAt Pieces)
open ProofFile.Honest.Sh (k12_samples_mark)
open ProofFile.Honest.K12.Light (sampleRow_plain)
open H2K.JointK (keyFirstPost rngEntry keySharedPre keyGu keyOmega keySharedEnd keyShared_cut)

theorem dbindOk {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := ebind_ok h

theorem emapOk {α β : Type} {x : Except String α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

/-- The mark in front gives the mark behind. -/
def SamR (a b : Statement) : Prop := stSamplesB a = true → stSamplesB b = true

/-- The ground's eight plain functions keep it. -/
theorem quiet_sam : GroundQuiet SamR where
  refl := fun _ x => x
  trans := fun f g x => g (f x)
  newGroup := fun d d' c m n h x => newGroup_samples d d' c m n h x
  recv := fun ft d d' s i h x => recv_samples ft d d' s i h x
  join := fun d d' g o k h x => join_samples d d' g o k h x
  addRow := fun d d' g r h x => addRow_samples d d' g r h x
  takeMask := fun d d' o n h x => takeMask_samples d d' o n h x
  closeLedger := fun d d' o h x => closeLedger_samples d d' o h x
  spendAsMask := fun d d' o h x => spend_samples d d' o h x
  adopt := fun d d' s g i h x => adopt_samples d d' s g i h x

/-! ## 1 A sending -/

/-- The laying of the sample rows keeps the mark. -/
theorem layRows_sam {L : Type} {codes : Codes} {seeds : List (List E × E)} :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DState L),
      VerifiableInference.Desc.K1.layRows codes seeds l ys d = .ok d' →
        stSamplesB d.st = true → stSamplesB d'.st = true
  | [], ys, d, d', e, hp => by
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · cases e
      exact hp
    · cases e
  | (o, s) :: l, ys, d, d', e, hp => by
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · exact layRows_sam l ys d d' e hp
    · split at e
      · cases e
      · split at e
        · cases e
        · dsimp only at e
          obtain ⟨d₁, ha, e'⟩ := ebind_ok e
          refine layRows_sam l _ d₁ d' e'
            (admit_samples _ _ _ _ (named_ok ha) hp fun r hr => ?_)
          rw [List.toList_toArray] at hr
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
          exact rowPlainB_iff.2 (sampleRow_plain _ _ _ _ _ _)

/-- A sending's decision keeps the mark. -/
theorem decideSend_sam {L : Type} {P : VerifiableInference.Desc.K1.Par} {owed : Option ℕ}
    {d d' : DState L} {rs : List Fmt.RoundView} {ns : Array ℕ}
    (e : VerifiableInference.Desc.K1.decideSend P owed d rs = .ok (ns, d'))
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold VerifiableInference.Desc.K1.decideSend at e
  split at e
  · obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨x, hx, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨d₂, hl, e⟩ := ebind_ok e
    obtain ⟨ns', d₁⟩ := x
    have hr := named_ok hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact layRows_sam _ _ d₁ _ hl (recv_samples _ _ _ _ _ hr hp)
  · cases e

/-! ## 2 The shared chain -/

/-- A sending at the shared chain's state. -/
theorem sendAt_sam (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List ℕ)) (behind : St → Array ℕ → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → SamR d.st d'.st) :
    Decides (RelAt SamR) (sendAt P n Q inFront groups behind) := by
  intro s rs gs s' h hp
  unfold sendAt at h
  dsimp only [Block.inside] at h
  obtain ⟨t, h0, h1⟩ := ebind_ok h
  obtain ⟨t', h2, h3⟩ := ebind_ok h1
  cases h0
  have h2' : (VerifiableInference.Desc.K1.decideSend Q none
      ({ st := s.st, book := s.book, roots := s.roots, opened := s.opened, loc := #[] } :
        DState (Array ℕ)) rs).map
      (fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        VerifiableInference.Desc.K1.Owing (DState (Array ℕ)))) = .ok t' := h2
  obtain ⟨x, k1, k2⟩ := emapOk h2'
  subst k2
  exact hb _ _ _ (named_ok h3) (decideSend_sam (ns := x.1) (d' := x.2) k1 hp)

/-- Each of the eight. -/
theorem blocks_sam (P : P14) (l : List (Block St Unit)) (h : blocks P = some l) :
    ∀ b ∈ l, Decides (RelAt SamR) b := by
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := Desc.Plain.obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun d rs _ d' hd => linPoint_rel quiet_sam _ d d' rs (why_some hd)
  · exact sendAt_sam _ _ _ _ _ _ fun d ids d' k => behindU_rel quiet_sam _ d d' ids k
  · exact fun d rs _ d' hd => laysRec_rel quiet_sam _ d d' rs (why_some hd)
  · exact fun d rs gs d' hd => loc_rel quiet_sam _ d d' rs gs (why_some hd)
  · exact sendAt_sam _ _ _ _ _ _ fun d ids d' k => behindOmega_rel quiet_sam _ d d' ids k
  · exact fun d rs _ d' hd => joins_rel quiet_sam _ d d' rs (why_some hd)
  · exact fun d rs _ d' hd => linZeta_rel quiet_sam d d' rs (why_some hd)
  · exact fun d rs _ d' hd => split_rel quiet_sam _ d d' rs (why_some hd)

/-- The eight, or the one block that fails its test on the plan. -/
theorem blocksOr_sam (P : P14) : ∀ b ∈ blocksOr P, Decides (RelAt SamR) b := by
  unfold blocksOr
  cases h : blocks P with
  | some l => exact blocks_sam P l h
  | none =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · intro d _ _ d' hd x
      cases hd
      exact x
    · cases hb

/-- A block as a retyped chain holds it decides as the block does. -/
theorem dec_retype {S Cl Cl' : Type} {R : S → S → Prop} {b : Block S Cl} (h : Decides R b) :
    Decides R (b.retype (Cl' := Cl')) := fun s rs gs s' e => h s rs gs s' e

theorem dec_bare {S Cl : Type} {R : S → S → Prop} {b : Block S Cl} (h : Decides R b) :
    Decides R b.asBare := fun s rs gs s' e => h s rs gs s' e

/-- At a seat of a proximity test on the shared chain. -/
theorem seat_sam (g : Lin → ℕ) (mask : Lin → Option ℕ) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) :
    Decides (RelAt SamR) (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave) := by
  intro d rs gs d' h hp
  obtain ⟨tE, hk, rfl⟩ := AtPublicFiles.AtFiles.seat_inv g mask p d d' rs gs h
  exact k12_samples_mark p he ha _ tE rs gs hk hp

/-- **Every member of the shared chain's flat list keeps the mark**, where the two tests' places
meet the two conditions. -/
theorem shared_members (c : OnBytes.Model.Verify.Chains) (P : VerifiableInference.Desc.Key.LaterPlaces)
    (hU : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).answers = 1)
    (hO : ∀ nO, P.O = some nO → (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1) :
    ∀ b ∈ ((VerifiableInference.Desc.Key.sharedChain c P).retype
        (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder, Decides (RelAt SamR) b := by
  rw [keyShared_cut]
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with rfl | hb
    · intro d _ _ d' hd x
      cases hd
      exact x
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      exact dec_bare (dec_retype (blocksOr_sam _ b' hb'))
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact dec_bare (dec_retype (seat_sam _ _ _ hU.1 hU.2))
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨nO, hn, rfl⟩ := List.mem_map.1 hb
        have h' := hO nO (Option.mem_toList.1 hn)
        exact dec_bare (dec_retype (seat_sam _ _ _ h'.1 h'.2))
      · obtain rfl := List.mem_singleton.1 hb
        intro s rs gs s' h x
        obtain ⟨_, _, rfl⟩ := emapOk h
        exact x

/-! ## 3 The first chain behind the lookups' rows -/

/-- The statement at the first chain's record. -/
abbrev stF : FirstState → Statement := fun s => s.d.st

/-- The relation at the first chain's record. -/
abbrev RF : FirstState → FirstState → Prop := By SamR stF

theorem rf_trans (a b c : FirstState) (h : RF a b) (k : RF b c) : RF a c := fun x => k (h x)

/-- The ranges' test. -/
theorem rng_sam {Cl : Type} (one : OneTime) (N : H2U.PlaceNums)
    (he : (rangesParams N).early = true) (ha : (rangesParams N).answers = 1) :
    Decides RF (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl) := by
  intro s rs gs s' h hp
  obtain ⟨tE, hk, rfl⟩ := AtPublicFiles.AtFiles.ranges_inv one N s s' rs gs h
  exact k12_samples_mark _ he ha _ tE rs gs hk hp

/-- The lens of the batching reads the record's own statement. -/
theorem batchLens_st : VerifiableInference.Desc.K13.LensSt
    (batchLens (β := VerifiableInference.Desc.Key.LookupRecord)) stF where
  enter := by
    intro t t' h
    simp only [batchLens] at h
    split at h
    · cases h
    · cases h
      rfl
  get := by
    intro t p h
    simp only [batchLens] at h
    split at h
    · cases h
      rfl
    · cases h
  set := fun _ _ _ _ => rfl

/-- A change that leaves the statement keeps the mark. -/
theorem quiet_sam_at {Cl : Type} (n : String) (pl : Place)
    (f : FirstState → Except String FirstState) (hf : ∀ s s', f s = .ok s' → s'.d.st = s.d.st) :
    Decides RF (quietAt (Cl := Cl) n pl f) := by
  intro s _ _ s' h x
  have e : s'.d.st = s.d.st := hf s s' h
  show stSamplesB s'.d.st = true
  rw [e]
  exact x

/-- The rows on the table are laid: the statement stays. -/
theorem layPile_st (keysOf : VerifiableInference.Desc.Key.LookupRecord → List (List Lkp.Keys))
    (one : OneTime) (s s' : FirstState) (h : layPile keysOf one s = .ok s') : s'.d.st = s.d.st := by
  unfold layPile at h
  obtain ⟨_, _, h⟩ := dbindOk h
  dsimp only at h
  obtain ⟨_, _, h⟩ := dbindOk h
  obtain ⟨_, _, h⟩ := dbindOk h
  obtain ⟨_, _, h⟩ := dbindOk h
  obtain ⟨_, _, h⟩ := dbindOk h
  obtain ⟨_, _, h⟩ := dbindOk h
  cases h
  rfl

/-- The batching of the rows on the table. -/
theorem batch_sam {Cl : Type} (one : OneTime) (N : Pieces) (sent : ℕ) :
    Decides RF (batchTableRows (Cl := Cl) (·.keys) one N sent) := by
  unfold batchTableRows
  dsimp only
  refine andThen_decides _ rf_trans _ _ _ (andThen_decides _ rf_trans _ _ _
    (andThen_decides _ rf_trans _ _ _ (quiet_sam_at _ _ _ ?_) ?_) ?_) ?_
  · exact fun s s' h => layPile_st _ one s s' h
  · exact VerifiableInference.Desc.K13.frontB_keeps quiet_sam _ _ batchLens_st _
  · exact VerifiableInference.Desc.K13.battB_keeps quiet_sam _ _ batchLens_st _
  · exact VerifiableInference.Desc.K13.quietB_keeps quiet_sam _ _ batchLens_st _

/-- A sending's seat. -/
theorem seat1_sam {Cl : Type} (name : String) (P : VerifiableInference.Desc.K1.Par) :
    Decides RF (sendingSeat (Cl := Cl) name P : Block FirstState Cl) := by
  intro s rs gs s' e hp
  obtain ⟨y, hy, rfl⟩ := emapOk e
  obtain ⟨x, hx, rfl⟩ := emapOk hy
  obtain ⟨ns, d'⟩ := x
  exact decideSend_sam (d := VerifiableInference.Desc.Key.withLoc s.d #[]) hx hp

/-- W's sending. -/
theorem sendW_sam {Cl : Type} (one : OneTime) (N : Pieces) (sent : ℕ) (groups : List (List ℕ))
    {bw : Block FirstState Cl} (hw : sendW one N sent groups = some bw) : Decides RF bw := by
  unfold sendW at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  dsimp only
  refine andThen_decides _ rf_trans _ _ _ (andThen_decides _ rf_trans _ _ _
    (andThen_decides _ rf_trans _ _ _ (quiet_sam_at _ _ _ ?_) (seat1_sam _ _))
    (quiet_sam_at _ _ _ ?_)) ?_
  · intro s s' h
    obtain ⟨_, _, h⟩ := dbindOk h
    cases h
    rfl
  · intro s s' h
    cases h
    rfl
  · exact VerifiableInference.Desc.K13.rowsB_keeps quiet_sam _ _ batchLens_st _

/-- **Every member behind the lookups' rows keeps the mark**, where the ranges' test's place meets
the two conditions. -/
theorem first_back_members (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) (he : (rangesParams N).early = true)
    (ha : (rangesParams N).answers = 1) :
    ∀ b ∈ rngEntry one N :: keyFirstPost one D told set N, Decides RF b := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact dec_bare (rng_sam one N he ha)
  unfold keyFirstPost at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    refine dec_bare ?_
    have hc' : c ∈ batchTableRows (·.keys) one VerifiableInference.Desc.Key.pieces
          (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D)) ::
        (sendW one VerifiableInference.Desc.Key.pieces
          (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D))
          (VerifiableInference.Desc.Key.groupsTold told
            (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.lastSendRound D))
            (VerifiableInference.Desc.Key.rootsAt D (VerifiableInference.Desc.Key.lastSendRound D)))).toList := hc
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact batch_sam _ _ _
    · exact sendW_sam _ _ _ _ (Option.mem_toList.1 hc')
  · obtain rfl := List.mem_singleton.1 hb
    intro s rs gs s' h x
    obtain ⟨_, _, rfl⟩ := emapOk h
    exact x

/-! ## 4 The two folds -/

/-- Behind the lookups' rows the fold keeps the mark. -/
theorem first_back_fold (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) (he : (rangesParams N).early = true)
    (ha : (rangesParams N).answers = 1) (ft : ℕ) (s : FirstState) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : FirstState × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (rngEntry one N :: keyFirstPost one D told set N) s rs cols = .ok r)
    (hp : stSamplesB s.d.st = true) : stSamplesB r.1.d.st = true :=
  foldBlocks_keeps RF (fun _ x => x) rf_trans ft _ (first_back_members one D told set N he ha)
    s rs cols r h hp

/-- The shared chain's fold keeps the mark. -/
theorem shared_fold (c : OnBytes.Model.Verify.Chains) (P : VerifiableInference.Desc.Key.LaterPlaces)
    (hU : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).answers = 1)
    (hO : ∀ nO, P.O = some nO → (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1) (ft : ℕ) (s : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft ((VerifiableInference.Desc.Key.sharedChain c P).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder s rs cols = .ok r)
    (hp : stSamplesB s.st = true) : stSamplesB r.1.st = true :=
  foldBlocks_keeps (RelAt SamR) (fun _ x => x) (fun _ _ _ f g x => g (f x)) ft _
    (shared_members c P hU hO) s rs cols r h hp

end AtPublicFiles.KeyLastChain.Lots.Walk

#print axioms AtPublicFiles.KeyLastChain.Lots.Walk.first_back_fold
#print axioms AtPublicFiles.KeyLastChain.Lots.Walk.shared_fold
