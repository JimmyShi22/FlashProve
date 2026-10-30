-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

-- Mends of typing and elaboration, pack c60df67f; no statement turned by them but mem_weave's.
/-
E2E/OfflineRowsAtValue.lean: at the offline prover's own senders, in scope, at the written book.

  `offline_first_laid`, `offline_shared_laid`, `offline_second_laid`, `offline_rows_laid`   each half
      is laid
  `offline_parts`   the halves' numbers of parts

Conditional on `KeySourced` and scope, which hold where the public files' test says yes, and on
`LookupsStated` (E2E/OfflineLaying.lean): the two lookups' parts state what the book has for them; if
that premise is false at the written book, the statements over it are empty. `offline_parts` does not
take it.
Limits: those of E2E/OfflineLaying.lean. Nothing on any simulator or any property.
-/
import E2E.OfflineLaidAtValue
import Johnson.Desc.ProofFile.Honest.K12.MembersAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob proverSideOfProximityTest firstPart restPart jobKR)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces pieces)
open OnBytes.Slice (GF)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first keyProver_second sharedChainProverSidesInOrder)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull full_two chainPlaces Stated OneFull rideW
  rideMsg idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace locPlace
  omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace idxJob_stated
  msgJob_stated wJob_stated k13_stated k14_stated k14_sends_stated rides_full sendingPar_sent)
open AtPublicFiles.KeyValues (WitK oneOf batchedRowsSending keyBatt matrixEntryOf)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- The sending of W at the written shape. -/
theorem keyW_written (one : OneFull (oneOf Xs)) :
    ∃ J : K1.SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) Unit, batchedRowsSending f Xs N = J ∧
      J.P.place = wPlace ∧ J.ride = rideW ∧ J.P.codes = keyFull.codes ∧
      J.P.sent = (OnBytes.linMessageW keyFull.once.shape).getD #[] ∧
      ∃ gs fi pts a, AtPublicFiles.Key.wJob (matrixEntryOf f) (oneOf Xs) pieces gs fi rideW pts a = some J := by
  obtain ⟨w, hw⟩ : ∃ w, OnBytes.linMessageW keyFull.once.shape = some w :=
    Option.isSome_iff_exists.1 (by
      have h := shape_full.1
      cases hq : OnBytes.linMessageW keyFull.once.shape with
      | none => rw [hq] at h; cases h
      | some w => rfl)
  have hl : OnBytes.linMessageW (oneOf Xs).lin = some w := by rw [one.lin]; exact hw
  refine ⟨?J, ?a, ?b, ?c, ?d, ?e, ?gs, ?fi, ?pts, ?aa, ?f⟩
  case a =>
    unfold batchedRowsSending AtPublicFiles.Key.wJob
    rw [hl]
  case f =>
    unfold AtPublicFiles.Key.wJob
    rw [hl]
    rfl
  case b => rfl
  case c => rfl
  case d => exact one.codes
  case e =>
    rw [hw]
    exact sendingPar_sent _ _ _ _ _

/-- **The first chain's halves are laid.** -/
theorem offline_first_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hL : LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first)) :
    ∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).first,
      RowLaid (keyBook K₀) 0 h := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  have hl := of_atFull lookups_full hK
  rw [Bool.and_eq_true] at hl
  have hT := of_atFull tests_full hK
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := hT
  intro h hh
  rw [keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact send_laid hK (p := idxPlace) _ rfl (by decide) (by decide) (by decide)
      (idxJob_stated K₀ hK _ one _ _ _)
  · exact send_laid hK (p := msgPlace) _ rfl (by decide) (by decide) (by decide)
      (msgJob_stated K₀ hK _ one _ _ _ _ _ rides_full.2.1)
  · exact look_laid hK 0 935 (by decide) hl.1 _ _ _ _ rfl (face_of_one one 0) (by decide) hL.1
  · exact look_laid hK 1 920 (by decide) hl.2 _ _ _ _ rfl (face_of_one one 1) (by decide) hL.2
  · obtain ⟨s, t, r, e⟩ : ∃ s t r, jobKR.p.nums.stages = s :: t :: r := ⟨_, _, _, rfl⟩
    refine test_laid hK (Or.inl rfl) _ jobKR (AtPublicFiles.KeyThread.place_sourced hs scope) ?_ rfl
      s t r e t1 (by decide) (by decide)
    exact K12.members_KR (X := Unit) _ one.codes
      ((sendingPar_sent _ _ _ _ _).trans (by rw [one.ranges]))
      (funext fun _ => rfl) rfl (fun _ _ => K12.AtProof.idleT12)
  · have hk18 : (keyBatt Xs).lin.kCol = 18 := by
      show (oneOf Xs).lin.kCol = 18
      rw [one.lin]
      exact shape_full.2.2
    have hkK : (keyBatt Xs).lin.kCol = K₀.kCol := by
      rw [hk18]
      exact (beq_iff_eq.1 (of_atFull kCol_full hK)).symm
    have h2 := of_atFull full_two hK
    obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using h2)
    have hm : (K13.k13Sum (keyBatt Xs)).moves.length = 19 := by
      unfold K13.k13Sum
      rw [K3.sumPart_moves]
      show VerifiableInference.Desc.K3.roundsOf (K13.k13Shape (keyBatt Xs).lin.kCol) = 19
      rw [hk18]
      rfl
    refine row_of_table hK (Or.inl rfl) (p := battPlace) (c := [1, 19]) (n := 2) rfl ?_ rfl
      (by decide) (by decide) (by decide)
      (k13_stated hf (keyBatt Xs) rfl rfl hkK _ _)
    show [1, ((K13.k13Sum (keyBatt Xs)).lift _ _ _ _).moves.length] = [1, 19]
    rw [show ((K13.k13Sum (keyBatt Xs)).lift _ _ _ _).moves.length =
      (K13.k13Sum (keyBatt Xs)).moves.length from List.length_map _, hm]
  · obtain ⟨J, eJ, hp, hr, -, -, gs, fi, pts, a, hJ⟩ := keyW_written (W₀ := W₀) (Rc := Rc) Xs N f one
    show RowLaid (keyBook K₀) 0 (K1.proverSideOfSending (batchedRowsSending f Xs N))
    rw [eJ]
    exact send_laid hK J hp (by decide) (by decide) (by decide)
      (wJob_stated K₀ hK _ one _ _ _ _ _ rides_full.2.2 _ _ J hJ)

/-- **The shared chain's halves are laid.** -/
theorem offline_shared_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) :
    ∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).shared,
      RowLaid (keyBook K₀) 1 h := by
  have hpar : parKey Xs Pl = QK := par_sourced hs scope
  have hsp : (K14.planData (parKey Xs Pl)).S.sharedSplitNeeded = true := by
    rw [hpar]
    exact shape_full.2.1
  have h2 := of_atFull full_two hK
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using h2)
  have hT := of_atFull tests_full hK
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := hT
  have hPl : Pl = PF := later_sourced hs scope
  intro h hh
  rcases List.mem_append.1 hh with hw | hw
  · rcases mem_weave hw with ho | hd
    · have hst := k14_stated (Rc := Rc) (Ky := OnBytes.TableKey) (X := Unit) hf
        (K14.planData (parKey Xs Pl)) hsp f
      have hst' := hst h ho
      replace ho : h ∈ K14.proverSidesOfSharedRounds (K14.planData (parKey Xs Pl)) f := ho
      unfold K14.proverSidesOfSharedRounds at ho
      simp only [hsp, if_true, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := pointPlace) (c := [1]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := locPlace) (c := [1]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := zetaPlace) (c := [1]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := splitPlace) (c := [1]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
    · have hst := k14_sends_stated (Ky := OnBytes.TableKey) (X := Unit) K₀ hK
        ⟨parKey Xs Pl, 0⟩ (by show (parKey Xs Pl).codes = _; rw [hpar]; rfl)
        (by show (parKey Xs Pl).S = _; rw [hpar]; rfl) f
        (fun c => AtPublicFiles.KeyFile.randK14 (g c 0))
      have hst' := hst h hd
      unfold K14.proverSidesOfSharedSendings at hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := foldedPlace) (c := [2]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
      · exact row_of_table hK (Or.inr (Or.inl rfl)) (p := omegaPlace) (c := [2]) (n := 1) rfl rfl rfl
          (by decide) (by decide) (by decide) hst'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hPl
    rcases hw with rfl | rfl
    · obtain ⟨s, t, r, e⟩ : ∃ s t r, foldedAt.p.nums.stages = s :: t :: r := ⟨_, _, _, rfl⟩
      refine test_laid hK (Or.inr (Or.inl rfl)) _ foldedAt AtPublicFiles.KeyNineClosed.place_full ?_ rfl
        s t r e t2 (by decide) (by decide)
      show [K12.AtProof.msgOf K12.AtProof.senderU (K14.jobU ⟨parKey Xs PF, 0⟩) 0,
        K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨parKey Xs PF, 0⟩) 1] = _
      rw [hpar]
      exact folded_members_full
    · obtain ⟨s, t, r, e⟩ : ∃ s t r, omegaAt.p.nums.stages = s :: t :: r := ⟨_, _, _, rfl⟩
      refine guarded_laid hK (Or.inr (Or.inl rfl)) _ omegaAt omega_place_full ?_ rfl
        s t r e t3 (by decide) (by decide)
      show [K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨parKey Xs PF, 0⟩) 0,
        K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨parKey Xs PF, 0⟩) 1] = _
      rw [hpar]
      exact omega_members_full

/-- What a test's list of members has of Omega's sending does not read the round of the point. -/
theorem msgOf_omega_any (a : Addr) (A : K14.SendPub) (m k : Nat) :
    K12.AtProof.msgOf a (K14.jobOmega A) k = K12.AtProof.msgOf a (K14.jobOmega ⟨A.P, m⟩) k := by
  simp only [K12.AtProof.msgOf, K14.jobOmega]

/-- **The last chain's half is laid.** -/
theorem offline_second_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) :
    ∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).second,
      RowLaid (keyBook K₀) 2 h := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  have hpar : parKey Xs Pl = QK := par_sourced hs scope
  have hPl : Pl = PF := later_sourced hs scope
  have hT := of_atFull tests_full hK
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := hT
  obtain ⟨J, eJ, -, hr, hc, hsent, -⟩ := keyW_written (W₀ := W₀) (Rc := Rc) Xs N f one
  intro h hh
  rw [keyProver_second] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  subst hh
  subst hPl
  obtain ⟨s, t, r, e⟩ : ∃ s t r, ownAt.p.nums.stages = s :: t :: r := ⟨_, _, _, rfl⟩
  have hsize : J.P.sent.size = 2 := by
    rw [hsent]
    have h := shape_full.1
    cases hq : OnBytes.linMessageW keyFull.once.shape with
    | none => rw [hq] at h; cases h
    | some w =>
      rw [hq] at h
      exact Option.some.inj h
  refine guarded_laid hK (Or.inr (Or.inr rfl)) _ ownAt own_place_full ?_ ?_ s t r e t4
    (by decide) (by decide)
  · unfold AtPublicFiles.KeyLay.jobKWAt
    rw [AtPublicFiles.KeyLay.jobKW_members, msgOf_omega_any _ _ 0]
    have hI : (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.sent =
        #[keyFull.once.input] := by
      rw [← one.idx]
      exact sendingPar_sent _ _ _ _ _
    have hIc : (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.codes =
        keyFull.codes := one.codes
    show [K12.AtProof.msgK1 AtPublicFiles.KeyTest.sIdx (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P
        (fun _ => none)
        ((AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.sent.size - 1),
      K12.AtProof.msgK1 AtPublicFiles.KeyTest.sW (batchedRowsSending f Xs N).P (batchedRowsSending f Xs N).ride 0,
      K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨parKey Xs PF, 0⟩) 0] =
        AtPublicFiles.KeyTest.jobOwn.members
    rw [eJ, hr, hpar, ← own_members_full]
    unfold K12.AtProof.msgK1 ownMembersAt Johnson.Prover.Send.shapeAt
    rw [hI, hIc, hsent, hc]
    rfl
  · show some (AtPublicFiles.KeyTest.sW, (batchedRowsSending f Xs N).P.sent.size - 1) = _
    rw [eJ, hsize]
    rfl

/-- **THE STATEMENT: each half of the offline prover is laid, at the written book.** -/
theorem offline_rows_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hL : LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first)) :
    OfflineRowsLaid K' Xs N Pl f g inR d ent groups first K₀ :=
  ⟨offline_first_laid K' Xs N Pl f g inR d ent groups first hs scope hK hL,
    offline_shared_laid K' Xs N Pl f g inR d ent groups first hs scope hK,
    offline_second_laid K' Xs N Pl f g inR d ent groups first hs scope hK⟩

/-- **THE TEST OF EMPTINESS: the halves' numbers of parts.** -/
theorem offline_parts {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) :
    OfflineParts K' Xs N Pl f g inR d ent groups first := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  have hpar : parKey Xs Pl = QK := par_sourced hs scope
  have hsp : (K14.planData (parKey Xs Pl)).S.sharedSplitNeeded = true := by
    rw [hpar]
    exact shape_full.2.1
  have hl := of_atFull lookups_full hK
  rw [Bool.and_eq_true] at hl
  have l0 : (K3.stages (AtPublicFiles.KeyValues.faceAt Xs 0)).length = 935 := by
    have h := hl.1
    unfold lookupFits at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [face_of_one one 0]
    exact h.2
  have l1 : (K3.stages (AtPublicFiles.KeyValues.faceAt Xs 1)).length = 920 := by
    have h := hl.2
    unfold lookupFits at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [face_of_one one 1]
    exact h.2
  have c1 := congrArg (List.map Prod.snd)
    (first_counts (offlineValue K' Xs N Pl f g inR d ent groups first))
  have c2 := congrArg (List.map Prod.snd)
    (shared_counts (offlineValue K' Xs N Pl f g inR d ent groups first) hsp)
  rw [List.map_map] at c1 c2
  refine ⟨c1.trans ?_, c2.trans ?_, rfl⟩
  · show [1, 1, (K3.stages (AtPublicFiles.KeyValues.faceAt Xs 0)).length,
      (K3.stages (AtPublicFiles.KeyValues.faceAt Xs 1)).length, 2, 2, 1] = _
    rw [l0, l1]
  · rfl

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offline_first_laid
#print axioms AtPublicFiles.OfflineRows.offline_shared_laid
#print axioms AtPublicFiles.OfflineRows.offline_second_laid
#print axioms AtPublicFiles.OfflineRows.offline_rows_laid
#print axioms AtPublicFiles.OfflineRows.offline_parts
