-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CalmAtBase.lean: the honest base filling has no first stop. Every part of its three chains'
sides has a first stop that never fires, so the prover that the maker returns there never stops by a first
stop, at any list of challenges: the public abort sets are empty.

  `smallLot_calm`, `term_calm`, `term_second_calm`, `term_shared_calm`   the sides of the filling
  `stopAt_calm`, `rowStopAt_calm`, `chainStopAt_calm`   a calm side does not stop where no input is given
  `badB_base`, `stop0B_base`   **at a return of the maker at the base filling both tests say no**

Limits. This is of first stops alone: second stops read the input and are not here. Nothing is claimed
on completeness, soundness or hiding.
-/
import Johnson.P1K8R.CalmK1K13
import Johnson.P1K8R.CalmK3K6
import Johnson.P1K8R.CalmK10K12W
import Johnson.P1K8R.CalmW
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import Johnson.Desc.ProofFile.Honest.K14.Six
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Kinds
import Johnson.Desc.ProofFile.Honest.Record

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block FileDescription)

section Stops
variable {V W X S Cl : Type}

theorem stopAt_calm {p : Part V W X} (h : Calm p) (loc ds : List Fmt.Drawn) :
    p.stopAt none loc ds = none := by
  unfold Part.stopAt
  refine List.findSome?_eq_none_iff.2 fun j _ => ?_
  rw [h.1]
  rfl

theorem rowStopAt_calm : ∀ (ps : List (Part V W X)), (∀ p ∈ ps, Calm p) →
    ∀ loc ds, rowStopAt (none : Option V) ps loc ds = none
  | [], _, _, _ => rfl
  | p :: ps, h, loc, ds => by
    have h1 := stopAt_calm (h p (List.mem_cons_self ..)) loc (ds.take p.moves.length)
    have h2 := rowStopAt_calm ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (loc ++ ds.take p.moves.length) (ds.drop p.moves.length)
    simp [rowStopAt, h1, h2]

/-- **A list of calm sides does not stop where no input is given.** -/
theorem chainStopAt_calm (hs : List (Placed V W X)) (h : ∀ x ∈ hs, HalfCalm x) :
    ∀ (bs : List (Block S Cl)) (loc ds : List Fmt.Drawn),
      chainStopAt (none : Option V) bs hs loc ds = none
  | [], _, _ => rfl
  | b :: bs, loc, ds => by
    have ih := chainStopAt_calm hs h bs (loc ++ ds.take b.rounds.length)
      (ds.drop b.rounds.length)
    unfold chainStopAt
    cases hf : hs.find? (fun g => g.place == b.place) with
    | none => simpa using ih
    | some g =>
      have hg := h g (List.mem_of_find?_eq_some hf)
      have hr := rowStopAt_calm g.parts hg loc (ds.take b.rounds.length)
      simpa [hr] using ih

end Stops

section Sides
variable {W₀ : Type}

/-- The smallness test's part has no first stop. -/
theorem smallLot_calm {Rc Xi Tr X : Type} (cells : Tr → Cells) (mats) :
    LotCalm (K8.smallLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells mats) := by
  intro Z G x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  intro p hp
  obtain rfl := List.mem_singleton.1 hp
  exact calm_stated (fun _ _ => rfl) rfl

/-- **Every lot of the filling is calm.** -/
theorem term_calm (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ L ∈ (onlineProverPartsInUse I o S O).lots, LotCalm L := by
  intro L hL
  have e : (onlineProverPartsInUse I o S O).lots =
      (ownPairsCP (LongLots.plain o S O) I S O).map (·.1) ++ [wLotAt I o O] := rfl
  rw [e] at hL
  rcases List.mem_append.1 hL with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    simp only [ownPairsCP, ownPairsC, FirstFill.ownPairs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k1_calm I o S O
    · exact k2_calm I S
    · exact k7_calm
    · exact k11_calm I o S O
    · exact k13_calm I o S O
    · exact k3_calm I o S O
    · exact k4_calm I
    · exact k5_calm O
    · exact k6_calm I o S O
    · exact smallLot_calm (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id
        (fun _ G _ l => K3.matsOwn G.W l)
    · exact K10K12.closeLotAt_calm I S
    · exact K10K12.proxLotAt_calm I S
  · obtain rfl := List.mem_singleton.1 h
    exact wLot_calm I o O

/-- The shared chain's own six halves. -/
theorem six_calm {Rc Ky X S Cl : Type} {P : Desc.K14.P14} {bs : List (Block S Cl)}
    {weights : W₀ → Weights} {rand : Rc → TableRand}
    {six : List (Placed Empty (Common W₀ Rc Ky) X)}
    (h : K14.sixOf P bs weights rand = .ok six) : ∀ x ∈ six, HalfCalm x := by
  unfold K14.sixOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [K14.halves_eq] at hx
        intro p hp
        rcases List.mem_append.1 hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;>
          · obtain rfl := List.mem_singleton.1 hp
            exact calm_stated (fun _ _ => rfl) rfl
        · split at hx
          · obtain rfl := List.mem_singleton.1 hx
            obtain rfl := List.mem_singleton.1 hp
            exact calm_stated (fun _ _ => rfl) rfl
          · cases hx
      · rw [K14.sendHalves_eq] at hx
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;>
        · obtain rfl := List.mem_singleton.1 hp
          exact calm_stated (fun _ _ => rfl) rfl

/-- **The shared chain's sides are calm.** -/
theorem term_shared_calm (I : WiderIn W₀) (Z : Pub) : ∀ x ∈ K12.AtProof.sharedWithUO I Z, HalfCalm x := by
  unfold K12.AtProof.sharedWithUO
  split
  · rename_i six hsix
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · have h1 : nowSharedBy (I.weights Z) Z = .ok six := hsix
        unfold nowSharedBy at h1
        obtain ⟨P, -, h1⟩ := bind_ok h1
        obtain ⟨s, -, h1⟩ := bind_ok h1
        exact six_calm h1 x hx
      · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx
        exact K10K12.testHalf_calm J
    · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx
      exact K10K12.halfNeeds_calm (K10K12.testHalf_calm J)
  · intro x hx
    cases hx

end Sides

section Base
variable {W₀ : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {I : WiderIn W₀}
  {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- What the maker lays in the first chain is calm. -/
theorem first_calm (hA : onlineProverFromPublicFiles o pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    ∀ x ∈ A.H.first, HalfCalm x := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok hA
  rw [hf]
  intro x hx
  obtain ⟨L, hL, hx⟩ := List.mem_flatMap.1 hx
  exact term_calm I o S O L hL A.Z A.G x hx

/-- **At a return of the maker at the base filling no first stop fires in the online chains.** -/
theorem badB_base (hA : onlineProverFromPublicFiles o pol lay KL (onlineProverPartsInUse I o S O) = .ok A) (F : FileDescription Inst)
    (ds : List Fmt.Drawn × List Fmt.Drawn) : badB F A.H ds = false := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  unfold badB
  rw [chainStopAt_calm _ (first_calm hA),
    chainStopAt_calm _ (by rw [hs]; exact K10K12.secondW_calm I o S O A.Z A.G)]
  rfl

/-- **Nor does the shared chain stop.** -/
theorem stop0B_base (hA : onlineProverFromPublicFiles o pol lay KL (onlineProverPartsInUse I o S O) = .ok A) (F : FileDescription Inst)
    (ds : List Fmt.Drawn) : stop0B F A.H ds = false := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  unfold stop0B
  rw [chainStopAt_calm _ (by rw [hs]; exact term_shared_calm I A.Z)]
  rfl

end Base

end P1K8

#print axioms P1K8.chainStopAt_calm
#print axioms P1K8.term_calm
#print axioms P1K8.term_shared_calm
#print axioms P1K8.badB_base
#print axioms P1K8.stop0B_base
