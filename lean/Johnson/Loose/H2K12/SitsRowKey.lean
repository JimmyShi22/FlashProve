-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsKey
import Johnson.Desc.K12.Law.SitsOnly
import Johnson.Desc.K12.Law.PlacesNums
import Johnson.Desc.K12.Law.SharedPlaces
import Johnson.Desc.PlanPasses
import Johnson.Desc.Key.SlotIs
/-
Johnson/Loose/H2K12/SitsRowKey.lean: THE ROW K12_sits (in a list of this project that is not in this repository: «in every written description that seats this kind (the proof file's; the key file's too where it seats the kind): the entry of the description's list of blocks at each place of the kind … its yes gives that law's premise»): THE KEY FILE's HALF, AS ONE THEOREM IN THE ROW's OWN SHAPE: AT Key.descriptionFromSource X N P (Johnson/Desc/Key/Desc.lean), AT EVERY X · N · P, AT Key.descriptionFromPlan's | Key.descAt's RETURN, AND (OVER Johnson/Desc/Key/) AT Key.keyDataAndDecisionAtDigest's | Key.keyDataAndDecisionAtFixedDigest's RETURN, WHERE THE DESCRIPTION's TEST ON THE PLAN IS KEPT. The proof file's half: H2K12/SitsRow.lean. All that lies beneath is the library's: no file under Johnson/Loose/ is imported. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
WHICH ARM OF THE ROW: THE SECOND («or its yes gives that law's premise»): Sits E K enter leave (Johnson/Desc/K12/Law/Sits.lean): E declares K's rounds · E's test on the plan gives K's · a yes of E's step gives K's OWN STEP's YES behind the door. K := proximityTestKind guardedProximityTestParts π: the constant of k12_law | k12_law_of_step (Johnson/Desc/K12/Law/Top.lean). NOT the premise of the laws on a game (Leads). THE FIRST ARM IS NOT CLAIMED HERE.
  lookupLink_kinds · keyFirst_only | keyShared_only | keySecond_only   «NO OTHER ENTRY BEARS THE KIND», AT THE KEY FILE's THREE CHAINS: every entry of the flat list whose label bears .K12 IS the ranges' test's | G_u's or G_omega's | the own test's: by the makers' own texts (each block's place is a literal there); the shared chain's eight by blocksOr_kinds, the last chain by second_only (both: Johnson/Desc/K12/Law/SitsOnly.lean)
  RowK12Key X N P       five fields, as RowK12's: ranges · gu · omega · sharedOnly · own
  key_sits_row          RowK12Key X N P: NO PREMISE
  RowK12Key.every₁ | ₂ | ₃   every entry that bears the kind sits, chain by chain
  RowK12Key.plans | .nums    under (Key.descriptionFromSource X N P).planOk = true the constant passes its own test at all four places, and its numbers are N's | P.U's | nO's | P.W's: the empty place noP12 is shut out
  rngEntry_place | keyGu_place | keyOmega_place | ownEntry_place   THE FOUR ENTRIES DO BEAR THE KIND: ⟨1, none, 5, .K12⟩ · ⟨2, none, 9, .K12⟩ · ⟨2, none, 10, .K12⟩ · ⟨3, none, 2, .K12⟩: so every₁ | ₂ | ₃ are not idle
  key_sits_row_laidAt | _laidFixed   Key.keyDataAndDecisionAtDigest Z lay cfg = .ok (D, r) | Key.keyDataAndDecisionAtFixedDigest Z lay = .ok (D, r) ⇒ the base's own returns (laidAt_is | laidFixed_is, Johnson/Desc/Key/SlotIs.lean) ∧ (Key.descriptionFromSource X N P).planOk = true ∧ r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧ RowK12Key X N P ∧ the four tests on the plan ∧ the four equations on the numbers: THERE noP12 IS SHUT OUT
  key_sits_row_made | _at    (these two carry NO planOk: descriptionFromPlan | descAt ask none: there the empty place stays open) Key.descriptionFromPlan m = .ok F | Key.descAt Z lay cfg = .ok F ⇒ the base's own returns (descOfMade_is | descAt_is, Johnson/Desc/Key/SlotIs.lean) ∧ F = Key.descriptionFromSource X N P ∧ RowK12Key X N P. `descOfMade_is` and `descAt_is` are declared in Johnson/Desc/Key/SlotIs.lean; Johnson/Loose/H2K12/SitsRowKey.lean:248 and :257 call them.
IS IT EMPTY? ranges | gu | own say that the entry IS in the list; omega and sharedOnly are «for all» alone: omega is guarded by P.O = some nO: NOTHING HERE OPENS THAT GUARD (by report, hO_in_scope (Johnson/Top/Fire/Code/KeyPublicAtSeat.lean) pays it in scope: not here): the row's open end at this file. `hO_in_scope` (Johnson/Top/Fire/Code/KeyPublicAtSeat.lean) states ∃ nO, P.O = some nO, under hZ : VerifierAndGoals.InScope Zp = true, hP : ReadOf Zp.pol X₀, hm : madeAt X₀ Zp.lay cfg = .ok m, hX : sourceOf m = .ok X and hp : (Fk X N P).planOk = true.
WHAT STANDS AGAINST IT: OF k12_law_of_step's SEVEN PREMISES (he · ha · hU : SwitchUnfolds p · hR : SeatReads · hp · h0 : StartK … · h) Sits HANDS ON TWO: h (the step's yes) and hp (the test on the plan); he · ha follow from hp (early_of_planOk · answers_of_planOk); hU · hR · h0 ARE TOUCHED BY NOTHING HERE · .nums speaks of the field nums alone (idx · oracles · before · answers · early are the maker's too once noP12 is out: untyped) · «bears the kind» is by the entry's label (place.kind) · «no other entry» is no other VALUE: that the entry stands once in its list is not said · that Key.descriptionFromPlan returns anywhere is shown at no files · whether this description is what the verifier's key slot runs is another row's (seat_key_file) · IT CARRIES A YES, NO PRICE.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

/-! ## No other entry bears the kind -/

/-- No entry of a lookup's link bears the kind K12. -/
theorem lookupLink_kinds (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : Nat)
    (x : Key.Lookup) : ∀ E ∈ (Key.lookupLink one set i x).blocksInOrder, E.place.kind ≠ .K12 := by
  intro E hE hk
  have h : (Key.lookupLink one set i x).blocksInOrder.map (·.place.kind) =
      [.frame, .frame, .K3, .frame, .frame, .frame] := rfl
  have hm : E.place.kind ∈ (Key.lookupLink one set i x).blocksInOrder.map (·.place.kind) :=
    List.mem_map_of_mem hE
  rw [h, hk] at hm
  simp at hm

/-- The key file's first chain: the one entry of the kind K12 is the ranges' test's. -/
theorem keyFirst_only (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) :
    ∀ E ∈ (Key.firstChain one D told set N).blocksInOrder, E.place.kind = .K12 → E = rngEntry one N := by
  intro E hE hk
  rw [keyFirst_cut] at hE
  rcases List.mem_append.1 hE with hE | hE
  · exfalso
    unfold keyFirstPre at hE
    rcases List.mem_append.1 hE with hE | hE
    · rcases List.mem_append.1 hE with hE | hE
      · rcases List.mem_cons.1 hE with rfl | hE
        · cases hk
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hE
          have hb' : b ∈ [Key.sendOwnMessage one Key.pieces
              (Key.groupsTold told (Key.rootsBefore D 2) (Key.rootsAt D 2))] := hb
          obtain rfl := List.mem_singleton.1 hb'
          cases hk
      · obtain ⟨L, hL, hE⟩ := List.mem_flatMap.1 hE
        have hL' : L ∈ (Key.lookupsOf one).zipIdx.map fun x => Key.lookupLink one set x.2 x.1 := hL
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hL'
        exact lookupLink_kinds one set y.2 y.1 E hE hk
    · obtain rfl := List.mem_singleton.1 hE
      cases hk
  · rcases List.mem_cons.1 hE with rfl | hE
    · rfl
    · exfalso
      unfold keyFirstPost at hE
      rcases List.mem_append.1 hE with hE | hE
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hE
        have hb' : b ∈ [Key.batchTableRows (·.keys) one Key.pieces
              (Key.rootsBefore D (Key.batchRound D))] ++
            (Key.sendW one Key.pieces (Key.rootsBefore D (Key.batchRound D))
              (Key.groupsTold told (Key.rootsBefore D (Key.lastSendRound D))
                (Key.rootsAt D (Key.lastSendRound D)))).toList := hb
        rcases List.mem_append.1 hb' with hb' | hb'
        · obtain rfl := List.mem_singleton.1 hb'
          cases hk
        · unfold Key.sendW at hb'
          cases hm : OnBytes.linMessageW one.lin with
          | none => rw [hm] at hb'; simp at hb'
          | some msg =>
            rw [hm] at hb'
            obtain rfl := List.mem_singleton.1 hb'
            cases hk
      · obtain rfl := List.mem_singleton.1 hE
        cases hk

/-- The key file's shared chain: an entry of its flat list that bears the kind K12 is the test's on
G_u or, where the plan has one, the test's on G_omega. -/
theorem keyShared_only (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    ∀ E ∈ ((Key.sharedChain c P).retype (Cl' := Key.Claim)).blocksInOrder, E.place.kind = .K12 →
      E = keyGu P ∨ ∃ nO, P.O = some nO ∧ E = keyOmega nO := by
  intro E hE hk
  rw [keyShared_cut] at hE
  rcases List.mem_append.1 hE with hE | hE
  · exfalso
    unfold keySharedPre at hE
    rcases List.mem_cons.1 hE with rfl | hE
    · cases hk
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hE
      exact blocksOr_kinds _ b hb hk
  · rcases List.mem_cons.1 hE with rfl | hE
    · exact .inl rfl
    · rcases List.mem_append.1 hE with hE | hE
      · obtain ⟨nO, hn, rfl⟩ := List.mem_map.1 hE
        exact .inr ⟨nO, Option.mem_toList.1 hn, rfl⟩
      · obtain rfl := List.mem_singleton.1 hE
        cases hk

/-- The key file's last chain: an entry of its flat list that bears the kind K12 is the own test's. -/
theorem keySecond_only (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    ∀ E ∈ ((Key.thirdChain c P).retype (Cl' := Key.Claim)).blocksInOrder, E.place.kind = .K12 →
      E = ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') :=
  second_only Key.Claim (Key.thirdPar c) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')

/-! ## The four entries bear the kind -/

theorem rngEntry_place (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums) :
    (rngEntry one N).place = ⟨1, none, 5, .K12⟩ := by
  show (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Block T12 Key.Claim).place = _
  rw [place_of_k12]
  exact place_of_p12At _ _

theorem keyGu_place (P : Key.LaterPlaces) : (keyGu P).place = ⟨2, none, 9, .K12⟩ := by
  show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').place = _
  rw [place_of_k12]
  exact place_of_p12At _ _

theorem keyOmega_place (nO : H2U.PlaceNums) : (keyOmega nO).place = ⟨2, none, 10, .K12⟩ :=
  omegaEntry_place Key.Claim nO

theorem ownEntry_place (Cl' : Type) (x : H2U.PlaceNums) :
    (ownEntry Cl' (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ x) : Blk')).place =
      ⟨3, none, 2, .K12⟩ := by
  show ({ (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ x) : Blk').place with
    chain := 3, link := none, piece := 2 } : Place) = _
  rw [place_of_k12, place_of_p12At]

/-! ## The row -/

/-- The row at the key file's description. -/
structure RowK12Key (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) : Prop where
  ranges : rngEntry X.Y.k.oneTime N ∈ (Key.descriptionFromSource X N P).first.blocksInOrder ∧
    Sits (rngEntry X.Y.k.oneTime N) (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk')
      (Key.enterAndAsk (Key.enterRanges X.Y.k.oneTime) (Key.rangesParams N)) Key.leaveRanges ∧
    ∀ E ∈ (Key.descriptionFromSource X N P).first.blocksInOrder, E.place.kind = .K12 → E = rngEntry X.Y.k.oneTime N
  gu : keyGu P ∈ (Key.descriptionFromSource X N P).shared.blocksInOrder ∧
    Sits (keyGu P) (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk')
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave
  omega : ∀ nO, P.O = some nO → keyOmega nO ∈ (Key.descriptionFromSource X N P).shared.blocksInOrder ∧
    Sits (keyOmega nO) (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk') (Seat.enter (·.gOmega) fun _ => none)
      Seat.leave
  sharedOnly : ∀ E ∈ (Key.descriptionFromSource X N P).shared.blocksInOrder, E.place.kind = .K12 →
    E = keyGu P ∨ ∃ nO, P.O = some nO ∧ E = keyOmega nO
  own : ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ∈ (Key.descriptionFromSource X N P).second.blocksInOrder ∧
    Sits (ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')
      enterOwn leaveOwn ∧
    ∀ E ∈ (Key.descriptionFromSource X N P).second.blocksInOrder, E.place.kind = .K12 →
      E = ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')

/-- The key file's half of the row: no premise. -/
theorem key_sits_row (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    RowK12Key X N P where
  ranges := ⟨by
      show rngEntry X.Y.k.oneTime N ∈ (Key.firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).blocksInOrder
      rw [keyFirst_cut]
      exact List.mem_append_right _ List.mem_cons_self, rngEntry_sits X.Y.k.oneTime N,
    keyFirst_only X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N⟩
  gu := ⟨by
      show keyGu P ∈ ((Key.sharedChain X.chains P).retype (Cl' := Key.Claim)).blocksInOrder
      rw [keyShared_cut]
      exact List.mem_append_right _ List.mem_cons_self, keyGu_sits P⟩
  omega := fun nO hO => ⟨by
      show keyOmega nO ∈ ((Key.sharedChain X.chains P).retype (Cl' := Key.Claim)).blocksInOrder
      rw [keyShared_cut_omega X.chains P nO hO]
      exact List.mem_append_right _ List.mem_cons_self, omegaEntry_sits Key.Claim nO⟩
  sharedOnly := keyShared_only X.chains P
  own := ⟨by
      show ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ∈
        ((Key.thirdChain X.chains P).retype (Cl' := Key.Claim)).blocksInOrder
      rw [keySecond_cut]
      exact List.mem_append_right _ List.mem_cons_self,
    ownEntry_sits Key.Claim _, keySecond_only X.chains P⟩

section
variable {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- Every entry of the first chain that bears the kind sits. -/
theorem RowK12Key.every₁ (R : RowK12Key X N P) :
    ∀ E ∈ (Key.descriptionFromSource X N P).first.blocksInOrder, E.place.kind = .K12 →
      Sits E (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk')
        (Key.enterAndAsk (Key.enterRanges X.Y.k.oneTime) (Key.rangesParams N)) Key.leaveRanges := by
  intro E hE hk
  rw [R.ranges.2.2 E hE hk]
  exact R.ranges.2.1

/-- Every entry of the shared chain that bears the kind sits. -/
theorem RowK12Key.every₂ (R : RowK12Key X N P) :
    ∀ E ∈ (Key.descriptionFromSource X N P).shared.blocksInOrder, E.place.kind = .K12 →
      Sits E (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk')
        (Seat.enter (·.gU) (·.firstMask)) Seat.leave ∨
      ∃ nO, P.O = some nO ∧
        Sits E (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk') (Seat.enter (·.gOmega) fun _ => none)
          Seat.leave := by
  intro E hE hk
  rcases R.sharedOnly E hE hk with rfl | ⟨nO, hO, rfl⟩
  · exact .inl R.gu.2
  · exact .inr ⟨nO, hO, (R.omega nO hO).2⟩

/-- Every entry of the last chain that bears the kind sits. -/
theorem RowK12Key.every₃ (R : RowK12Key X N P) :
    ∀ E ∈ (Key.descriptionFromSource X N P).second.blocksInOrder, E.place.kind = .K12 →
      Sits E (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') enterOwn leaveOwn := by
  intro E hE hk
  rw [R.own.2.2 E hE hk]
  exact R.own.2.1

/-- Where the description passes its test on the plan the constant passes its own at all four
places. -/
theorem RowK12Key.plans (R : RowK12Key X N P) (hp : (Key.descriptionFromSource X N P).planOk = true) :
    (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk').planOk = true ∧
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').planOk = true ∧
      (∀ nO, P.O = some nO → (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true) ∧
      (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk').planOk = true := by
  obtain ⟨b1, b2, b3⟩ := VerifiableInference.Desc.Keeps.planOk_blocks _ hp
  exact ⟨R.ranges.2.1.plan (b1 _ R.ranges.1), R.gu.2.plan (b2 _ R.gu.1),
    fun nO hO => (R.omega nO hO).2.plan (b2 _ (R.omega nO hO).1), R.own.2.1.plan (b3 _ R.own.1)⟩

/-- And so its numbers are the maker's own: the empty place is shut out. -/
theorem RowK12Key.nums (R : RowK12Key X N P) (hp : (Key.descriptionFromSource X N P).planOk = true) :
    (Key.rangesParams N).nums = N.nums ∧ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums = P.U.nums ∧
      (∀ nO, P.O = some nO → (pGomega nO).nums = nO.nums) ∧ (pOwnK P).nums = P.W.nums := by
  obtain ⟨h1, h2, h3, h4⟩ := R.plans hp
  exact ⟨H2K.Made.nums_of_planOk Key.rangesPlace N h1,
    H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ P.U h2,
    fun nO hO => H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (h3 nO hO),
    H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ P.W h4⟩

end

/-- At the description made of the planner's answer and the sendings. -/
theorem key_sits_row_made (m : Johnson.G.OfPlan.Made) (F : FileDescription Key.Xi)
    (h : Key.descriptionFromPlan m = .ok F) :
    ∃ X N P, Key.sourceOf m = .ok X ∧ Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok P ∧
      F = Key.descriptionFromSource X N P ∧ RowK12Key X N P := by
  obtain ⟨X, N, P, hX, hN, hP, e⟩ := Key.descOfMade_is m F h
  exact ⟨X, N, P, hX, hN, hP, e, key_sits_row X N P⟩

/-- At the description made of the files. -/
theorem key_sits_row_at (Z : OnBytes.Model.Verify.Public) (lay cfg : ByteArray)
    (F : FileDescription Key.Xi) (h : Key.descAt Z lay cfg = .ok F) :
    ∃ m X N P, Key.madeAt Z lay cfg = .ok m ∧ Key.sourceOf m = .ok X ∧
      Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok P ∧ F = Key.descriptionFromSource X N P ∧
      RowK12Key X N P := by
  obtain ⟨m, X, N, P, hm, hX, hN, hP, e⟩ := Key.descAt_is Z lay cfg F h
  exact ⟨m, X, N, P, hm, hX, hN, hP, e, key_sits_row X N P⟩

/-- AT THE KEY FILE's PIECE AS IT IS LAID, at a digest that is handed in: the description's test on
the plan is kept, and with it the four tests and the four equations. -/
theorem key_sits_row_laidAt (Z : OnBytes.Model.Verify.Public) (lay cfg : ByteArray)
    (D : OnBytes.Maker.WholeD) (r : Key.KeyRun) (h : Key.keyDataAndDecisionAtDigest Z lay cfg = .ok (D, r)) :
    ∃ m X N P, Key.madeAt Z lay cfg = .ok m ∧ Key.sourceOf m = .ok X ∧
      Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok P ∧
      Key.descAt Z lay cfg = .ok (Key.descriptionFromSource X N P) ∧ (Key.descriptionFromSource X N P).planOk = true ∧
      r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧ RowK12Key X N P ∧
      ((proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk').planOk = true ∧
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').planOk = true ∧
        (∀ nO, P.O = some nO → (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true) ∧
        (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk').planOk = true) ∧
      ((Key.rangesParams N).nums = N.nums ∧ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums = P.U.nums ∧
        (∀ nO, P.O = some nO → (pGomega nO).nums = nO.nums) ∧ (pOwnK P).nums = P.W.nums) := by
  obtain ⟨m, X, N, P, hm, hX, hN, hP, hd, hp, _, _, _, _, hr⟩ := Key.laidAt_is Z lay cfg D r h
  exact ⟨m, X, N, P, hm, hX, hN, hP, hd, hp, hr, key_sits_row X N P, (key_sits_row X N P).plans hp,
    (key_sits_row X N P).nums hp⟩

/-- AT THE FIXED DIGEST: the value that Desc/Key/Slot.lean defines for the verifier's key slot. -/
theorem key_sits_row_laidFixed (Z : OnBytes.Model.Verify.Public) (lay : ByteArray)
    (D : OnBytes.Maker.WholeD) (r : Key.KeyRun) (h : Key.keyDataAndDecisionAtFixedDigest Z lay = .ok (D, r)) :
    ∃ m X N P, Key.madeAt Z lay Key.fixedDigest = .ok m ∧ Key.sourceOf m = .ok X ∧
      Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok P ∧
      Key.descAt Z lay Key.fixedDigest = .ok (Key.descriptionFromSource X N P) ∧ (Key.descriptionFromSource X N P).planOk = true ∧
      r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧ RowK12Key X N P ∧
      ((proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk').planOk = true ∧
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').planOk = true ∧
        (∀ nO, P.O = some nO → (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true) ∧
        (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk').planOk = true) ∧
      ((Key.rangesParams N).nums = N.nums ∧ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums = P.U.nums ∧
        (∀ nO, P.O = some nO → (pGomega nO).nums = nO.nums) ∧ (pOwnK P).nums = P.W.nums) :=
  key_sits_row_laidAt Z lay Key.fixedDigest D r h

end H2K.JointK

#print axioms H2K.JointK.lookupLink_kinds
#print axioms H2K.JointK.keyFirst_only
#print axioms H2K.JointK.keyShared_only
#print axioms H2K.JointK.keySecond_only
#print axioms H2K.JointK.key_sits_row
#print axioms H2K.JointK.RowK12Key.every₁
#print axioms H2K.JointK.RowK12Key.every₂
#print axioms H2K.JointK.RowK12Key.every₃
#print axioms H2K.JointK.RowK12Key.plans
#print axioms H2K.JointK.RowK12Key.nums
#print axioms H2K.JointK.key_sits_row_made
#print axioms H2K.JointK.key_sits_row_at
#print axioms H2K.JointK.rngEntry_place
#print axioms H2K.JointK.keyGu_place
#print axioms H2K.JointK.keyOmega_place
#print axioms H2K.JointK.ownEntry_place
#print axioms H2K.JointK.key_sits_row_laidAt
#print axioms H2K.JointK.key_sits_row_laidFixed
