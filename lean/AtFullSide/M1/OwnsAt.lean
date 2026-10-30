-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- every owner of an entry of the book has a part.
/-
AtFullSide/M1/OwnsAt.lean: Sides.owns as a test on the book and the prover's halves alone, and its yes at a return of the maker at the base filling.

  halfAddrs, ownsOfHalves      the addresses of the parts of a list of halves; the test
  addrsOf_halves, owns_of_halves  under AtHonest's three equations Sides.owns is that test
  ownersW                      the 80 owners of the written entries (owners_written: one walk of the book; ownersW_is: they are the 52 of K1's jobs, the 25 code
                               switches and three on the shared chain)
  owners_have_halves           at a return of the maker at onlineProverPartsInUse under the head, each of the 80 is the address of a part

No run is said to do anything. That the book at the return is rawAheadW is the premise hB here (ahead_at_ret has it). No property of the protocol is claimed.

-/
import AtFullSide.M1.OwnsWalk
import Johnson.M1.Ties
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfWAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.M1.Own
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K14 AtFullSide.K14
open OnBytes.SendSim.Seat (parsW lotPars lotJobs wJobs lotPars_eq lotHalves_eq)
open ProofFile.Honest.K2.Law (placesW)
open VerifiableInference.Desc (Place Chain)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- The addresses of the parts of a list of halves. -/
def halfAddrs {V W X : Type} (l : List (Placed V W X)) : List Addr :=
  l.flatMap fun g => (List.range g.parts.length).map fun j => ⟨g.place, j⟩

theorem addr_of_half {V W X : Type} {l : List (Placed V W X)} {g : Placed V W X} (hg : g ∈ l) {j : Nat}
    (hj : j < g.parts.length) : (⟨g.place, j⟩ : Addr) ∈ halfAddrs l :=
  List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩

theorem halfAddrs_append {V W X : Type} (a b : List (Placed V W X)) :
    halfAddrs (a ++ b) = halfAddrs a ++ halfAddrs b := List.flatMap_append ..

/-- **The addresses of a list of Lettered are its halves'.** -/
theorem addrsOf_halves {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (l : List (Lettered Bk S Cl V W Y Pb)) :
    addrsOf l = halfAddrs (l.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) := by
  unfold addrsOf halfAddrs
  rw [List.flatMap_map]
  refine List.flatMap_congr fun L _ => ?_
  simp

/-- **Sides.owns's test, on the book and the halves alone.** -/
def ownsOfHalves {V₁ W₁ Y₁ V₂ W₂ Y₂ V₃ W₃ Y₃ : Type} (Bk : ProverCoinCounts) (h₁ : List (Placed V₁ W₁ Y₁))
    (h₂ : List (Placed V₂ W₂ Y₂)) (h₃ : List (Placed V₃ W₃ Y₃)) : Bool :=
  Bk.ahead.all fun e => (halfAddrs h₁ ++ halfAddrs h₂ ++ halfAddrs h₃).contains e.owner

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The filling's lots, by their makers. -/
theorem lots_are (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots =
      (((widerFillOwn () (LongLots.plain OnBytes.secondHashFunction S O) I OnBytes.secondHashFunction S O).lots ++ [closeLotAt I S]) ++
        [proxLotAt I S]) ++ [wLotAt I OnBytes.secondHashFunction O] := rfl

/-- **EVERY OWNER IS THE ADDRESS OF A PART**, at a return of the maker at the base filling, under the head. -/
theorem owners_have_halves (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∀ a ∈ ownersW, a ∈ halfAddrs A.H.first ++ halfAddrs A.H.shared ++ halfAddrs A.H.second := by
  obtain ⟨hZ, hG, hF, -, -, -, -, h1, h2, -⟩ := atPure_ok hA
  obtain ⟨Z₁, Bs, base, c, Sh, Se, Op⟩ := IM.seat_open hF
  have eZ : Z₁ = A.Z := Except.ok.inj (Op.pub.symm.trans hZ)
  subst eZ
  have eG : Bs.G₀ = A.G := Option.some.inj (Op.blank.symm.trans hG)
  have hZp : A.Z = Zp := (atPure_at_laid h.laid hA).1
  subst hZp
  have inFirst : ∀ g, (∃ M ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots, g ∈ M.halves A.Z A.G) →
      g ∈ A.H.first := fun g ⟨M, hM, hg⟩ => by
    rw [h1]
    exact List.mem_flatMap.2 ⟨M, hM, hg⟩
  have inTen : ∀ M, M ∈ (widerFillOwn () (LongLots.plain OnBytes.secondHashFunction S O) I OnBytes.secondHashFunction S O).lots →
      M ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots := fun M hM => by
    rw [lots_are]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hM))
  rw [ownersW_is]
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · rcases List.mem_append.1 ha with ha | ha
    · -- K1's 52
      obtain ⟨P₀, hP, rfl⟩ := List.mem_map.1 ha
      rw [← Johnson.M1.pars_of_live hS hL Op] at hP
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hP
      rw [lotPars_eq (X := Unit) (K1.lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) A.Z Bs.G₀] at hy
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hy
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rcases List.mem_append.1 hJ with hJ | hJ
      · rw [eG] at hJ
        have hg : K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
            (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.x, ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩⟩ : PlaceIn ProofFile.Inst)) J ∈
            (HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k1).halves A.Z A.G := by
          show _ ∈ lotHalves _ (K1.lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) A.Z A.G
          rw [lotHalves_eq]
          exact List.mem_map_of_mem hJ
        exact addr_of_half (inFirst _ ⟨_, inTen _ List.mem_cons_self, hg⟩) (j := 0) Nat.zero_lt_one
      · unfold wJobs at hJ
        cases hm : OnBytes.linMessageW A.Z.first.lin with
        | none => rw [hm] at hJ; cases hJ
        | some msg =>
          rw [hm] at hJ
          obtain rfl := List.mem_singleton.1 hJ
          have hg : K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
              (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.x, ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩⟩ : PlaceIn ProofFile.Inst))
              (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 msg (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩)
                (K13.wDataAt O.pile A.Z A.G)) ∈ (wLotAt (X := Unit) I OnBytes.secondHashFunction O).halves A.Z A.G := by
            show _ ∈ wHalves _ (K1.lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt O.pile) A.Z A.G
            rw [OnBytes.SendSim.Seat.wHalves_eq]
            unfold wJobs
            rw [hm]
            exact List.mem_singleton.2 rfl
          refine addr_of_half (inFirst _ ⟨_, ?_, hg⟩) (j := 0) Nat.zero_lt_one
          rw [lots_are]
          exact List.mem_append_right _ List.mem_cons_self
    · -- the 25 switches
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      rw [← Johnson.M1.places_of_live hS hL Op, eG] at hp
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      have hh : ∃ f : K2.SwitchPlace → Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit,
          (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
            K2.switchLot D fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩).halves A.Z A.G =
            (K2.switchPlaces A.Z A.G).map f ∧ ∀ q, (f q).place = q.place ∧ (f q).parts.length = 1 :=
        ⟨_, rfl, fun _ => ⟨rfl, rfl⟩⟩
      obtain ⟨f, hf, hq⟩ := hh
      have hg : f p ∈ (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
          K2.switchLot D fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩).halves A.Z A.G := by
        rw [hf]
        exact List.mem_map_of_mem hp
      have := addr_of_half (inFirst _ ⟨_, inTen _ (List.mem_cons_of_mem _ List.mem_cons_self), hg⟩) (j := 0)
        (by rw [(hq p).2]; exact Nat.zero_lt_one)
      rw [(hq p).1] at this
      exact this
  · -- the three on the shared chain
    have h' := h.toAtMg
    have hsix := nowSharedBy_at_head h (I.weights A.Z)
    have inShared : ∀ g, (g ∈ proverSidesOfSharedRounds { S := (VerifiableInference.Desc.K1.qAt A.Z Np).S, atPoint := 0, atZeta := 6 } (I.weights A.Z) ++
          proverSidesOfSharedSendings { P := VerifiableInference.Desc.K1.qAt A.Z Np, atPoint := 0 } (I.weights A.Z)
            (randNow (VerifiableInference.Desc.K1.qAt A.Z Np)) ∨
          g ∈ ProofFile.Honest.K12.AtProof.halfO (I.weights A.Z) A.Z) → g ∈ A.H.shared := fun g hg => by
      rw [h2]
      show g ∈ ProofFile.Honest.K12.AtProof.sharedWithUO I A.Z
      rw [ProofFile.Honest.K12.AtProof.sharedWithUO_ok I hsix, sharedWithU_ok I hsix]
      rcases hg with hg | hg
      · exact List.mem_append_left _ (List.mem_append_left _ hg)
      · exact List.mem_append_right _ hg
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rcases List.mem_cons.1 ha with rfl | ha
    · exact addr_of_half (inShared _ (Or.inl (List.mem_append_right _ List.mem_cons_self))) (j := 0) Nat.zero_lt_one
    rcases List.mem_cons.1 ha with rfl | ha
    · exact addr_of_half (inShared _ (Or.inl (List.mem_append_right _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) (j := 0) Nat.zero_lt_one
    obtain rfl := List.mem_singleton.1 ha
    obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head h'
    obtain ⟨_, _, hw⟩ := ProofFile.Honest.K12.Light.facts_at_head h'
    have hb : ∃ b1 b2 b3 b4 b5 b6 b7 b8 : VerifiableInference.Desc.Block Desc.K14.St Unit,
        Desc.K14.blocks (VerifiableInference.Desc.K1.qAt A.Z Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
      unfold Desc.K14.blocks
      rw [hw]
      exact ⟨_, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := hb
    have e := ProofFile.Honest.K12.AtProof.halfO_at_head h' b1 b2 b3 b4 b5 b6 b7 b8 hb (I.weights A.Z) hO
    have hm := inShared _ (Or.inr (by rw [e]; exact List.mem_singleton.2 rfl))
    have hpl : pO.place = ⟨2, none, 10, .K12⟩ := by
      obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hO
      exact H2K.JointK.place_of_p12At _ _
    have := addr_of_half hm (j := 0) (show 0 < 2 by omega)
    exact Eq.mp (congrArg (fun p : Place => (⟨p, 0⟩ : Addr) ∈ halfAddrs A.H.shared) hpl) this

/-- **Sides.owns AT A RETURN.** hB is the written book's equation. -/
theorem owns_at_return (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (hB : A.B.ahead = rawAheadW) : ownsOfHalves A.B A.H.first A.H.shared A.H.second = true := by
  unfold ownsOfHalves
  rw [hB]
  refine List.all_eq_true.2 fun e he => ?_
  have m := List.contains_iff_mem.1 (List.all_eq_true.1 owners_written e he)
  exact List.contains_iff_mem.2 (owners_have_halves I S O h hS hL hA _ m)

/-- **UNDER AtHonest's THREE EQUATIONS Sides.owns IS THE TEST ON THE HALVES.** -/
theorem owns_of_halves {Xi W₁ Rc Ky Tr X₀ X : Type} {F : VerifiableInference.Desc.FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₁ Rc Ky Tr X₀ X) (H : Prover W₁ Rc Xi Ky Tr X₀ X)
    (e1 : H.first = G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (e2 : H.shared = G.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (e3 : H.second = G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩) :
    G.owns = ownsOfHalves Bk H.first H.shared H.second := by
  unfold Sides.owns ownsOfHalves
  rw [addrsOf_halves G.first, addrsOf_halves G.shared, addrsOf_halves G.second, e1, e2, e3]

end AtFullSide.M1.Own

#print axioms AtFullSide.M1.Own.addrsOf_halves
#print axioms AtFullSide.M1.Own.owners_have_halves
#print axioms AtFullSide.M1.Own.owns_at_return
#print axioms AtFullSide.M1.Own.owns_of_halves
