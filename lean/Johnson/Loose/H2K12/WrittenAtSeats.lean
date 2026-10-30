-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.DeclAtSeats
import Johnson.Desc.K12.Law.WrittenOfDecl
import Johnson.Desc.K12.Law.PlacesNums
/-
Johnson/Loose/H2K12/WrittenAtSeats.lean: AT THE PROOF FILE's DESCRIPTION: THE WRITTEN ROUNDS OF A
PROXIMITY TEST's PLACE (H2K.Pub.writtenOf N.‹x›.nums) ARE THOSE OF A CLOSED PLACE N0, WHERE THE
DESCRIPTION's DECLARED ROUNDS, WRITTEN OUT (Johnson.G.OfPlan.writtenOf: ANOTHER FUNCTION OF THAT
NAME), ARE A LIST R ON WHICH CLOSED EQUATIONS HOLD. An assembly: the cuts of the declared rounds
(H2K12/DeclAtSeats.lean) · the counts of "BAT" (Law/SitsBats.lean) · «start» | «free»
(H2K12/FreeAtSeats.lean: plain_free) · the general step writtenOf_at_stretch | chains_of_written
(Law/WrittenOfG.lean | WrittenOfDecl.lean). BOOK-KEEPING
ON THE PLAN. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  entries_of_rounds · pre_length_closed · roots_closed | roots_whole     general tools: readers keep
      the entries · where the seat stands, as a number of the closed list · the roots in front, and
      a whole list's, off the closed list.
  seat_rounds          the kind's block's rounds at a place are roundsOfNums of the place's numbers,
      and begin with a round named "BAT".
  stretch_at_U | stretch_at_O     what a seat on the shared chain hands to a general step, at a
      letter R for the written lists: the chain's declared rounds as pre ++ (ds ++ post), taken by
      readers, are R's · ds is roundsOfNums of the place's numbers · pre's length is the closed
      number · «free» is the closed list's roots in front.
  written_at_U | written_at_O | written_at_W     the three later seats.
LEFT AS HYPOTHESES, ALL ON THE CLOSED SIDE OR NUMBERS AGAINST NUMBERS: h0 · ha · hc · h2 · h3 · h4 ·
hF; and hW, which ties the description to R. THE CONCLUSION IS AN EQUATION OF TWO RETURNS:
roundsOfNums answers on both sides (left: the seat's test on the plan; right: h0), but writtenOf
also lays the rounds out (layW), which may refuse: where it refuses on one side it refuses on the
other: that it answers is not said here. THE FIRST CHAIN's SEAT IS NOT HERE.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (batsR bats)

/-- Readers keep the entries. -/
theorem entries_of_rounds {e : List (List ByteArray × ByteArray)} {ds : List Fmt.DeclaredRound}
    {xs : List Fmt.Round} (h : ds.mapM (·.round e) = some xs) :
    xs.map (·.entry) = ds.map (·.entry) :=
  First.map_of_mapM (fun d : Fmt.DeclaredRound => d.round e) (fun x : Fmt.Round => x.entry)
    (fun d : Fmt.DeclaredRound => d.entry) (fun _ _ hb => (H2K.Pub.round_keeps hb).1) _ _ h

/-- Where the seat stands, as a number of the closed list. -/
theorem pre_length_closed {e : List (List ByteArray × ByteArray)} {pre post R : List Fmt.DeclaredRound}
    {r : Fmt.DeclaredRound} {xs : List Fmt.Round} {k a : Nat}
    (hx : (pre ++ ((r :: R) ++ post)).mapM (·.round e) = some xs)
    (hr : (r.entry.name == "BAT") = true) (hk : batsR pre = k)
    (ha : (H2U.batPlaces (xs.map (·.entry)))[k]? = some a) : pre.length = a := by
  rw [entries_of_rounds hx, List.map_append, List.cons_append, List.map_cons, ← hk] at ha
  have h := H2K.Made.batPlaces_at (pre.map (·.entry)) r.entry ((R ++ post).map (·.entry)) hr
  have e1 : some (pre.map (·.entry)).length = some a := h.symm.trans ha
  rw [List.length_map] at e1
  exact Option.some.inj e1

/-- The roots in front, off the closed list. -/
theorem roots_closed {e : List (List ByteArray × ByteArray)} {pre rest : List Fmt.DeclaredRound}
    {xs : List Fmt.Round} (hx : (pre ++ rest).mapM (·.round e) = some xs) :
    Johnson.G.OfPlan.rootsOf pre = ((xs.take pre.length).map (·.entry.roots)).sum := by
  have h := entries_of_rounds hx
  have h2 : (xs.take pre.length).map (·.entry) = pre.map (·.entry) := by
    rw [List.map_take, h, ← List.map_take, List.take_left]
  unfold Johnson.G.OfPlan.rootsOf
  have h3 := congrArg (List.map (·.roots)) h2
  rw [List.map_map, List.map_map] at h3
  exact congrArg List.sum h3.symm

/-- The whole list's roots: the like at «nothing behind». -/
theorem roots_whole {e : List (List ByteArray × ByteArray)} {ds : List Fmt.DeclaredRound}
    {xs : List Fmt.Round} (hx : ds.mapM (·.round e) = some xs) :
    Johnson.G.OfPlan.rootsOf ds = (xs.map (·.entry.roots)).sum := by
  have hl : xs.length = ds.length := by
    have := congrArg List.length (entries_of_rounds hx)
    simpa using this
  have h := roots_closed (pre := ds) (rest := []) (by rw [List.append_nil]; exact hx)
  rw [← hl, List.take_length] at h
  exact h

/-- The kind's block's rounds at a place. -/
theorem seat_rounds (place : Place) (x : H2U.PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Blk').planOk = true) :
    H2U.roundsOfNums x.nums = some (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Blk').rounds ∧
      ∃ r R, (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Blk').rounds = r :: R ∧
        (r.entry.name == "BAT") = true :=
  ⟨H2K.Made.nums_of_planOk place x hp ▸ VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ hp,
    k12_head guardedProximityTestParts _ hp⟩

/-- What G_u's seat hands to a general step. -/
theorem stretch_at_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks = .ok R)
    (aU : Nat) (ha : (H2U.batPlaces ((R.2.1.map (·.1)).map (·.entry)))[0]? = some aU) :
    ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds ++
          ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++
            [sharedEnd ProofFile.Cl (p14N Z N) N]).flatMap (·.rounds))).mapM (·.round []) =
        some (R.2.1.map (·.1)) ∧
      H2U.roundsOfNums N.U.nums = some (proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds ∧
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)).length = aU ∧
      N.U.nums.free = (((R.2.1.map (·.1)).take aU).map (·.entry.roots)).sum := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  have mU : guEntry ProofFile.Cl N ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    (descN_shared o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  have pU : (proximityTestKind guardedProximityTestParts (pGu N) : Blk').planOk = true := (guEntry_sits ProofFile.Cl N).plan (b2 _ mU)
  obtain ⟨hr0, r, R', er, hr⟩ := seat_rounds ⟨2, none, 9, .K12⟩ N.U pU
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [decl_atU] at hx
  have hl : ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)).length = aU := by
    have hx' := hx
    rw [show (proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds = r :: R' from er] at hx'
    exact pre_length_closed hx' hr (sharedPre_bats ProofFile.Cl _ _ N) ha
  have hfree := (plain_free o pol lay KL Z hZ mk N c hN hp).1.2
  rw [roots_closed hx, hl] at hfree
  exact ⟨hx, hr0, hl, hfree⟩

/-- What G_omega's seat hands to a general step. -/
theorem stretch_at_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks = .ok R)
    (aO : Nat) (ha : (H2U.batPlaces ((R.2.1.map (·.1)).map (·.entry)))[1]? = some aO) :
    ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds ++
          [sharedEnd ProofFile.Cl (p14N Z N) N].flatMap (·.rounds))).mapM (·.round []) =
        some (R.2.1.map (·.1)) ∧
      H2U.roundsOfNums nO.nums = some (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds ∧
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap
        (·.rounds)).length = aO ∧
      nO.nums.free = (((R.2.1.map (·.1)).take aO).map (·.entry.roots)).sum := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  have mU : guEntry ProofFile.Cl N ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    (descN_shared o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  have pU : (proximityTestKind guardedProximityTestParts (pGu N) : Blk').planOk = true := (guEntry_sits ProofFile.Cl N).plan (b2 _ mU)
  have hcut := shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO
  have mO : omegaEntry ProofFile.Cl nO ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    hcut ▸ List.mem_append_right _ List.mem_cons_self
  have pO : (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true :=
    (omegaEntry_sits ProofFile.Cl nO).plan (b2 _ mO)
  obtain ⟨hr0, r, R', er, hr⟩ := seat_rounds ⟨2, none, 10, .K12⟩ nO pO
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [decl_atO o mk Z N nO hO c] at hx
  have hl : ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap
      (·.rounds)).length = aO := by
    have hx' := hx
    rw [show (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds = r :: R' from er] at hx'
    exact pre_length_closed hx' hr (sharedPreO_bats ProofFile.Cl _ _ N pU) ha
  have hfree := ((plain_free o pol lay KL Z hZ mk N c hN hp).2.1 nO hO).2
  rw [roots_closed hx, hl] at hfree
  exact ⟨hx, hr0, hl, hfree⟩

/-- AT G_u's SEAT. -/
theorem written_at_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks = .ok R)
    (N0 : H2U.TestNums) (ds0 : List Fmt.DeclaredRound) (aU : Nat)
    (h0 : H2U.roundsOfNums N0 = some ds0)
    (ha : (H2U.batPlaces ((R.2.1.map (·.1)).map (·.entry)))[0]? = some aU)
    (hc : ds0.mapM (·.round []) = some (((R.2.1.map (·.1)).drop aU).take ds0.length))
    (h2 : N.U.nums.work = N0.work) (h3 : N.U.nums.stages = N0.stages)
    (h4 : N.U.nums.ownMask = N0.ownMask)
    (hF : N.U.nums.firstTree + (((R.2.1.map (·.1)).take aU).map (·.entry.roots)).sum =
      N0.firstTree + N0.free) :
    H2K.Pub.writtenOf N.U.nums = H2K.Pub.writtenOf N0 := by
  obtain ⟨hx, hr0, hl, hfree⟩ := stretch_at_U o pol lay KL Z hZ mk N c hN hp R hW aU ha
  exact H2K.Pub.writtenOf_at_stretch hx hr0 h0 (by rw [hl]; exact hc) h2 h3 h4
    (by rw [hfree]; exact hF)

/-- AT G_omega's SEAT, where the plan has that test. -/
theorem written_at_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks = .ok R)
    (N0 : H2U.TestNums) (ds0 : List Fmt.DeclaredRound) (aO : Nat)
    (h0 : H2U.roundsOfNums N0 = some ds0)
    (ha : (H2U.batPlaces ((R.2.1.map (·.1)).map (·.entry)))[1]? = some aO)
    (hc : ds0.mapM (·.round []) = some (((R.2.1.map (·.1)).drop aO).take ds0.length))
    (h2 : nO.nums.work = N0.work) (h3 : nO.nums.stages = N0.stages)
    (h4 : nO.nums.ownMask = N0.ownMask)
    (hF : nO.nums.firstTree + (((R.2.1.map (·.1)).take aO).map (·.entry.roots)).sum =
      N0.firstTree + N0.free) :
    H2K.Pub.writtenOf nO.nums = H2K.Pub.writtenOf N0 := by
  obtain ⟨hx, hr0, hl, hfree⟩ := stretch_at_O o pol lay KL Z hZ mk N nO hO c hN hp R hW aO ha
  exact H2K.Pub.writtenOf_at_stretch hx hr0 h0 (by rw [hl]; exact hc) h2 h3 h4
    (by rw [hfree]; exact hF)

/-- AT THE OWN TEST's SEAT: nothing is declared in front. e0: the closed side's «earlier». -/
theorem written_at_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks = .ok R)
    (N0 : H2U.TestNums) (ds0 : List Fmt.DeclaredRound) (e0 : List (List ByteArray × ByteArray))
    (h0 : H2U.roundsOfNums N0 = some ds0)
    (hc : ds0.mapM (·.round e0) = some ((R.2.2.map (·.1)).take ds0.length))
    (h2 : N.W.nums.work = N0.work) (h3 : N.W.nums.stages = N0.stages)
    (h4 : N.W.nums.ownMask = N0.ownMask)
    (hF : N.W.nums.firstTree = N0.firstTree + N0.free) :
    H2K.Pub.writtenOf N.W.nums = H2K.Pub.writtenOf N0 := by
  obtain ⟨_, _, b3⟩ := Keeps.planOk_blocks _ hp
  have mW : ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk') ∈
      (descN o mk guardedProximityTestParts Z N c).second.blocksInOrder :=
    (descN_second o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  have pW : (proximityTestKind guardedProximityTestParts (pOwn N) : Blk').planOk = true :=
    (ownEntry_sits ProofFile.Cl _).plan (b3 _ mW)
  obtain ⟨hr0, _⟩ := seat_rounds ⟨3, none, 2, .K12⟩ N.W pW
  have hx := (H2K.Pub.chains_of_written hW).2.2
  rw [decl_atW] at hx
  have hfree : N.W.nums.free = 0 := (plain_free o pol lay KL Z hZ mk N c hN hp).2.2.2
  exact H2K.Pub.writtenOf_at_stretch (pre := []) hx hr0 h0 hc h2 h3 h4
    (by rw [hfree, Nat.add_zero]; exact hF)

end H2K.JointK

#print axioms H2K.JointK.written_at_O
#print axioms H2K.JointK.written_at_W
#print axioms H2K.JointK.pre_length_closed
#print axioms H2K.JointK.roots_closed
#print axioms H2K.JointK.written_at_U
