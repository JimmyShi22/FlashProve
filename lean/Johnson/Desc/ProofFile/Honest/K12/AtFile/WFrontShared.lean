-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontShared.lean: along the shared chain's fold the statement
stays tidy, and every stored sample row stays Send.form at some seeds.

  decideSend_newGood    the new rows behind a sending are Send.form at some seeds
  SharedGood, SharedStays   the codes' lengths are powers of two, the statement is tidy, the rows are
                        such rows; the relation "if in front, then behind"
  groundQuiet_shared    the ground's functions that ask nothing of their caller keep it
  sendOwn_shared        a sending
  seat_shared           a proximity test in its seat
  SendKeeps, sendAt_steps, blocks_steps, blocksOr_steps, steps_like, steps_carried, carried_steps
                        for any relation that those keep: every block of the chain as a file holds it
  carried_shared        so for SharedStays
  carried_fold_shared   the fold over that list
  sharedGood_first      the chain's first record

The admitting of a sample and the beginning of a test lie outside GroundQuiet: they occur in the
sendings and in the proximity tests, where they are met by name. The copying from another statement
lies outside it too and is not called on this chain.

Limits.
- The blocks' tests on the plan are a premise of carried_fold_shared.
- Nothing on whether a row holds of any words. Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.K14.Quiet
import Johnson.Desc.K14.FlatList
import Johnson.Desc.K14.Honest.FlatSteps
import Johnson.Desc.K12.Law.RowsAcross
import Johnson.Desc.K12.Law.RunCodes
import Johnson.Desc.K12.Coin.TidyThrough
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.K13.Law.RowsKept
import Johnson.Desc.K1.Law.RowsKeptPlan
import Johnson.Desc.Tidy.Stay
import Johnson.Top.H0.K2Hands.RowsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
section Sending
open OnBytes OnBytes.Params OnBytes.Model _root_.Desc.Plain
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.K1

/-- **Behind an accept of the kind's decision the new rows are Send.form at some seeds**, at any
rounds. -/
theorem decideSend_newGood {L : Type} (P : VerifiableInference.Desc.K1.Par)
    (hB : planOkOwn P = true) (owed : Option Nat)
    (d d' : DState L) (rs : List Fmt.RoundView) (hl : d.st.codes.lengthsOk = true)
    (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    NewInv QGood d.st.oracles.size d'.st := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    have hl' : P.codes.lengthsOk = true := by
      rw [← hc]
      exact hl
    intro o x ho hx hs
    have hcod : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes :=
      (kept_behind P d _ _).1.trans hc
    obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
    have hx' : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)).toArray[d.st.oracles.size + k]? = some x := hx
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at hx'
    have hx2 : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[k]? =
        some x := by simpa using hx'
    have hk : k < (shapesOf P).length := by
      have := (List.getElem?_eq_some_iff.1 hx2).1
      rwa [outs_length] at this
    obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf k hk
    obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys' = x :=
      Option.some.inj (hget.symm.trans hx2)
    have hk' : (shapesOf P)[k].answers ≠ 0 := by
      intro h0
      apply hs
      simp [wr, h0, fresh]
    have hkS : sampledAt P ⟨k, hk⟩ := hk'
    have hsh : Blk.shapeOk P.codes (shapesOf P)[k] = true := plan_shape P hB ⟨k, hk⟩
    have hpad : (Msg.of P.codes (shapesOf P)[k]).padFits = true := (plan_msg P hB ⟨k, hk⟩ hkS).2
    have hlenS : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
    have hle : (shapesOf P)[k].answers ≤ (seedsOf P r₁).length := by
      rw [hlenS]
      exact msgAt_answers_le P ⟨k, hk⟩
    have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k)
          (shapesOf P)[k] ys' := by simp [wr, hk']
    rw [hcod, hshape, hrows]
    refine ⟨(seedsOf P r₁).map fun sd => (⟨sd.1, sd.2⟩ : SampleSeed),
      rowsOf_size _ _ _ _ _ hle hy, fun i hi => ?_⟩
    obtain ⟨sd, hsd⟩ : ∃ sd, (seedsOf P r₁)[i]? = some sd :=
      ⟨(seedsOf P r₁)[i]'(Nat.lt_of_lt_of_le hi hle), List.getElem?_eq_getElem _⟩
    obtain ⟨y, hyi⟩ : ∃ y, ys'[i]? = some y :=
      ⟨ys'[i]'(Nat.lt_of_lt_of_le hi hy), List.getElem?_eq_getElem _⟩
    have hform := form_eq P.codes (shapesOf P)[k] (d.st.oracles.size + k) sd.1 sd.2 i y hl' hsh
      hpad
    obtain ⟨row, hrow, erow⟩ := Option.map_eq_some_iff.1 hform
    refine ⟨⟨sd.1, sd.2⟩, row, y, by simp [hsd], hrow, ?_⟩
    rw [rowsOf_get _ _ _ _ _ i hi sd y hsd hyi, erow]

end Sending

open OnBytes OnBytes.Params _root_.Desc.Plain
open OnBytes.Means (Tidy)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks noDigest roundsFit)
open VerifiableInference.Desc.Ground (GroundQuiet TidyStay groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.First.K2 (QGood RowsInv NewInv SameRows OldRows rowsInv_rows
  rowsInv_oldRows newInv_of_none newGroupP_rows joinP_rows addRowP_rows takeMaskP_rows
  closeLedgerP_rows spendAsMaskP_rows recvP_rows adoptP_rows)
open VerifiableInference.Desc.Keeps (Steps Decides steps_of_decides step_fit)
open Desc.K14 (St P14 RelAt sendAt blocks blocksOr frontBlock chainOf)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts P12)

/-- **What stays along the shared chain.** -/
def SharedGood (T : Statement) : Prop := T.codes.lengthsOk = true ∧ Tidy T ∧ RowsInv QGood T

/-- If it holds in front, it holds behind. -/
def SharedStays (A B : Statement) : Prop := SharedGood A → SharedGood B

theorem stays_of_same {A B : Statement} (hs : SameRows A B) (ht : TidyStay A B) :
    SharedStays A B := fun ⟨a, b, c⟩ => ⟨by rw [hs.1]; exact a, ht b, rowsInv_rows hs c⟩

theorem stays_of_old {A B : Statement} (ho : OldRows A B) (ht : TidyStay A B)
    (hn : A.codes.lengthsOk = true → NewInv QGood A.oracles.size B) : SharedStays A B :=
  fun ⟨a, b, c⟩ => ⟨by rw [ho.1]; exact a, ht b, rowsInv_oldRows ho (hn a) c⟩

/-- **The ground's quiet functions keep it.** -/
theorem groundQuiet_shared : GroundQuiet SharedStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun d d' a b n h => stays_of_same (newGroupP_rows d d' a b n h)
    (groundQuiet_tidy.newGroup _ _ _ _ _ h)
  recv := fun ft d d' s i h => stays_of_old (recvP_rows ft d d' s i h).1
    (groundQuiet_tidy.recv _ _ _ _ _ h) fun _ => newInv_of_none (recvP_rows ft d d' s i h).2
  join := fun d d' g o k h => stays_of_same (joinP_rows d d' g o k h)
    (groundQuiet_tidy.join _ _ _ _ _ h)
  addRow := fun d d' g r h => stays_of_same (addRowP_rows d d' g r h)
    (groundQuiet_tidy.addRow _ _ _ _ h)
  takeMask := fun d d' o n h => stays_of_same (takeMaskP_rows d d' o n h)
    (groundQuiet_tidy.takeMask _ _ _ _ h)
  closeLedger := fun d d' o h => stays_of_same (closeLedgerP_rows d d' o h)
    (groundQuiet_tidy.closeLedger _ _ _ h)
  spendAsMask := fun d d' o h => stays_of_same (spendAsMaskP_rows d d' o h)
    (groundQuiet_tidy.spendAsMask _ _ _ h)
  adopt := fun d d' s g i h => stays_of_old (adoptP_rows d d' s g i h).1
    (groundQuiet_tidy.adopt _ _ _ _ _ h) fun _ => newInv_of_none (adoptP_rows d d' s g i h).2

/-- **A sending keeps it**, at the sub-protocol's own test on its parameters. -/
theorem sendOwn_shared (Q : VerifiableInference.Desc.K1.Par)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (s s' : VerifiableInference.Desc.K1.Owing (DState (Array ℕ))) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds Q) rs = true)
    (h : (VerifiableInference.Desc.K1.sendOwn (Cl := Unit) Q).decide s (rs.map noDigest) gs =
      .ok s') : SharedStays s.held.st s'.held.st := by
  have ht := VerifiableInference.Desc.K1.sendOwn_rel (Cl := Unit) groundQuiet_tidy admitOn_tidy Q hB
    s s' rs gs hfit h
  obtain ⟨r₁, r₂, rfl⟩ := VerifiableInference.Desc.K1.fit_two _ _ rs hfit
  have h' : (VerifiableInference.Desc.K1.decideSend Q s.owed s.held [noDigest r₁, noDigest r₂]).map
      (fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        VerifiableInference.Desc.K1.Owing (DState (Array ℕ)))) = .ok s' := h
  obtain ⟨x, h1, h2⟩ := VerifiableInference.Desc.Keeps.emap_ok h'
  subst h2
  exact stays_of_old
    (VerifiableInference.Desc.First.K2.oldRows_of_old
      (VerifiableInference.Desc.K1.decideSend_old Q _ _ x.2 _ x.1 h1)) ht fun a =>
    decideSend_newGood Q hB _ _ x.2 _ a x.1 h1

/-- A relation that every sending keeps, at the sub-protocol's own test on its parameters. -/
def SendKeeps (R : Statement → Statement → Prop) : Prop :=
  ∀ (Q : VerifiableInference.Desc.K1.Par), VerifiableInference.Desc.K1.planOkOwn Q = true →
    ∀ (s s' : VerifiableInference.Desc.K1.Owing (DState (Array ℕ))) (rs : List Fmt.RoundView)
      (gs : List (List (ℕ × List UInt64))),
      roundsFit (VerifiableInference.Desc.K1.rounds Q) rs = true →
      (VerifiableInference.Desc.K1.sendOwn (Cl := Unit) Q).decide s (rs.map noDigest) gs = .ok s' →
      R s.held.st s'.held.st

/-- **A sending at the shared chain's record.** -/
theorem sendAt_steps {R : Statement → Statement → Prop} (H : GroundQuiet R) (hS : SendKeeps R)
    (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List ℕ)) (behind : St → Array ℕ → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → R d.st d'.st) :
    Steps (RelAt R) (sendAt P n Q inFront groups behind) := by
  intro hp ft s rs cols s' k hs
  obtain ⟨hfit, gs, h⟩ := step_fit ft _ s s' rs cols k hs
  have hB : VerifiableInference.Desc.K1.planOkOwn Q = true := by
    unfold sendAt at hp
    simp only [Block.inside, Bool.and_eq_true] at hp
    exact hp.1.1.1.1
  unfold sendAt at h
  dsimp only [Block.inside] at h
  obtain ⟨t, h0, h1⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain ⟨t', h2, h3⟩ := VerifiableInference.Desc.Keeps.ebind_ok h1
  cases h0
  have hq := hS Q hB _ _ rs _ hfit h2
  exact H.trans hq (hb _ _ _ (VerifiableInference.Desc.Keeps.named_ok h3))

/-- **The eight blocks.** -/
theorem blocks_steps {R : Statement → Statement → Prop} (H : GroundQuiet R) (hS : SendKeeps R)
    (P : P14) (l : List (Block St Unit)) (h : blocks P = some l) :
    ∀ b ∈ l, Steps (RelAt R) b := by
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := Desc.Plain.obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact steps_of_decides fun d rs _ d' hd => Desc.K14.linPoint_rel H _ d d' rs (Desc.K14.why_some hd)
  · exact sendAt_steps H hS _ _ _ _ _ _ fun d ids d' k => Desc.K14.behindU_rel H _ d d' ids k
  · exact steps_of_decides fun d rs _ d' hd => Desc.K14.laysRec_rel H _ d d' rs (Desc.K14.why_some hd)
  · exact steps_of_decides fun d rs gs d' hd => Desc.K14.loc_rel H _ d d' rs gs (Desc.K14.why_some hd)
  · exact sendAt_steps H hS _ _ _ _ _ _ fun d ids d' k => Desc.K14.behindOmega_rel H _ d d' ids k
  · exact steps_of_decides fun d rs _ d' hd => Desc.K14.joins_rel H _ d d' rs (Desc.K14.why_some hd)
  · exact steps_of_decides fun d rs _ d' hd => Desc.K14.linZeta_rel H d d' rs (Desc.K14.why_some hd)
  · exact steps_of_decides fun d rs _ d' hd => Desc.K14.split_rel H _ d d' rs (Desc.K14.why_some hd)

theorem blocksOr_steps {R : Statement → Statement → Prop} (H : GroundQuiet R) (hS : SendKeeps R)
    (P : P14) : ∀ b ∈ blocksOr P, Steps (RelAt R) b := by
  unfold blocksOr
  cases h : blocks P with
  | some l => exact blocks_steps H hS P l h
  | none =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · refine steps_of_decides fun d _ _ d' hd => ?_
      cases hd
      exact H.refl _
    · cases hb

/-- **A proximity test in its seat.** -/
theorem seat_shared (g : Desc.K14.Lin → ℕ) (mask : Desc.K14.Lin → Option ℕ) (p : P12) :
    Steps (RelAt SharedStays) (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave) := by
  intro hp ft s rs cols s' k hs
  obtain ⟨-, gs, h⟩ := step_fit ft _ s s' rs cols k hs
  have h' : ((VerifiableInference.Desc.K12.Seat.enter g mask s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest) gs).bind
        (VerifiableInference.Desc.K12.Seat.leave s)) = .ok s' := h
  obtain ⟨t, ht, h'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl'
  have hp' : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true := by
    simp only [Block.inside, Bool.and_eq_true] at hp
    exact hp.1.1
  intro ⟨a, b, c⟩
  refine ⟨?_, VerifiableInference.Desc.K12.Coin.k12_tidy p _ t' _ gs ht' a b,
    H2K.Out.k12_good p _ t' _ gs ht' c⟩
  have e := (H2K.Out.k12_run_codes p hp' _ t' _ gs ht').2
  show t'.st.codes.lengthsOk = true
  rw [e]
  exact a

/-- A block with the step of a block that keeps it, whose test on the plan asks as much. -/
theorem steps_like {R : Statement → Statement → Prop} {Cl₁ Cl₂ : Type} {x : Block St Cl₁}
    {b : Block St Cl₂} (he : ∀ ft s rs c, b.step ft s rs c = x.step ft s rs c)
    (hp : b.planOk = true → x.planOk = true) (h : Steps (RelAt R) x) : Steps (RelAt R) b :=
  fun hpb ft s rs c s' k hs => h (hp hpb) ft s rs c s' k (by rw [← he]; exact hs)

/-- A block of the chain carried to another type of claims and dressed for the flat list. -/
theorem steps_carried {R : Statement → Statement → Prop} {Cl : Type} {x : Block St Unit}
    (h : Steps (RelAt R) x) :
    Steps (RelAt R)
      ({ (x.retype (Cl' := Cl)) with planOk := (x.retype (Cl' := Cl)).planOk &&
        (x.retype (Cl' := Cl)).hasNoClaimsAndNothingAfter } : Block St Cl) :=
  steps_like (fun ft s rs c => Desc.K14.Honest.step_retype (Cl := Cl) x ft s rs c) (fun hp => by
    simp only [Block.retype, Bool.and_eq_true] at hp
    exact hp.1.1) h

/-- **Every block of the chain carried to another type of claims keeps R**, where the ground's quiet
functions, the sendings and the proximity tests in their seats do. -/
theorem carried_steps {R : Statement → Statement → Prop} {Cl : Type} (H : GroundQuiet R)
    (hS : SendKeeps R)
    (hK : ∀ (g : Desc.K14.Lin → ℕ) (mask : Desc.K14.Lin → Option ℕ) (p : P12),
      Steps (RelAt R) (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
        (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave))
    (c : OnBytes.Model.Verify.Chains) (P : P14) (N : H2U.Places4) :
    ∀ b ∈ ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder, Steps (RelAt R) b := by
  have hback : ∀ x ∈ blocksOr P ++ VerifiableInference.Desc.K12.Seat.tests N,
      Steps (RelAt R) x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact blocksOr_steps H hS P x hx
    · unfold VerifiableInference.Desc.K12.Seat.tests at hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain rfl := List.mem_singleton.1 hx
        exact hK _ _ _
      · obtain ⟨nO, -, rfl⟩ := List.mem_map.1 hx
        exact hK _ _ _
  have hlast : Steps (RelAt R) (VerifiableInference.Desc.K12.Seat.last
      (blocksOr P ++ VerifiableInference.Desc.K12.Seat.tests N)) :=
    steps_of_decides fun d rs gs d' hd => by
      have e := VerifiableInference.Desc.K13.Law.chainEnd_same (Cl := Unit) _ _ _ _ _ d d' rs gs hd
      subst e
      exact H.refl _
  intro b hb
  simp only [VerifiableInference.Desc.Chain.blocksInOrder, VerifiableInference.Desc.Chain.retype, chainOf,
    List.map_nil, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | ⟨y, ⟨x, hx, rfl⟩, rfl⟩ | rfl
  · exact steps_like (x := frontBlock c)
      (fun ft s rs cl => Desc.K14.Honest.step_retype (Cl := Cl) (frontBlock c) ft s rs cl)
      (fun hp => by
        simp only [Block.retype, Bool.and_eq_true] at hp
        exact hp.1.1.1) (Desc.K14.frontBlock_steps H c)
  · exact steps_carried (hback x (List.mem_append.2 hx))
  · exact steps_carried hlast

/-- **Every block of the chain carried to another type of claims keeps SharedGood.** -/
theorem carried_shared {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14) (N : H2U.Places4) :
    ∀ b ∈ ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder,
      Steps (RelAt SharedStays) b :=
  carried_steps groundQuiet_shared sendOwn_shared seat_shared c P N

/-- **Along the fold over the chain as a file holds it.** -/
theorem carried_fold_shared {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (N : H2U.Places4)
    (hp : ∀ b ∈ ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder, b.planOk = true) (ft : ℕ)
    (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder s rs cols = .ok r)
    (hs : SharedGood s.st) : SharedGood r.1.st :=
  VerifiableInference.Desc.Keeps.foldBlocks_steps (RelAt SharedStays) (fun _ h => h)
    (fun _ _ _ h k x => k (h x)) ft _ (carried_shared c P N) hp s rs cols r h hs

/-- The chain's first record has it, where the codes' lengths are powers of two. -/
theorem sharedGood_first (codes : Codes) (key : OnBytes.TableKey) (hl : codes.lengthsOk = true) :
    SharedGood (Desc.K14.first codes key).st :=
  ⟨hl, Tidy.start codes, fun o x hx => by
    have hx' : (#[] : Array OnBytes.Oracle)[o]? = some x := hx
    simp at hx'⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.decideSend_newGood
#print axioms ProofFile.Honest.K12.AtFile.groundQuiet_shared
#print axioms ProofFile.Honest.K12.AtFile.seat_shared
#print axioms ProofFile.Honest.K12.AtFile.carried_shared
#print axioms ProofFile.Honest.K12.AtFile.carried_fold_shared
#print axioms ProofFile.Honest.K12.AtFile.sharedGood_first
