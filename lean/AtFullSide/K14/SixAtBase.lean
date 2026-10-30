-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/SixAtBase.lean: the linear claim's shared rounds (kind K14): WHAT TWO PROVERS HOLD IN
THE SHARED CHAIN, as an equation, and so the two fields `halves` and `sends` of K14Asks
(Johnson/Desc/ProofFile/Honest/K14/Asks.lean) at these provers.

The first prover is the one that the maker onlineProverFromPublicFiles returns at the filling onlineProverPartsInUse
(Honest/K1/Law/WSideAtFill.lean), at any type of index (I : WiderIn W₀). In the shared chain that
filling lays this kind's six sides and, behind them, the sides of the chain's two proximity tests
where their jobs are made. The second is the one that it returns at that filling read through a pair
of maps g, rd on the index and on the committer's randomness (OnlineProverParts.through, Honest/ThruK13.lean); g,
rd and the named member d' are letters.

  testSides           the sides of the two proximity tests of the shared chain, as the filling lays
                      them behind this kind's six
  testSides_places    they stand at two places that are none of the six, each at most once
  thru_places         so do they when read through
  shared_at_base      **the filling's list under the hypothesis at the full size**: this kind's own
                      sides, the two sendings' sides, the two tests' sides
  atPure_pub_at_head  the public part that onlineProverFromPublicFiles returns is the hypothesis's
  base_shared         **the list of the prover that onlineProverFromPublicFiles returns at the filling**
  thru_shared         **the list of the prover that onlineProverFromPublicFiles returns at the filling read through**: at
                      this kind's places lie this kind's own sides, at the readers composed with g
                      and rd
  halves_sends_at_base, halves_sends_through   **HalvesIn and SendsIn at these two provers**, at the
                      letters of the proof file's own description, whatever the open letters are

How it is used. base_shared with testSides_places gives the three premises hs, apart and off of
asks_among (Honest/K14/AsksAtShared.lean) and five_among (Honest/K14/FiveAmong.lean) at the first
prover: AtFullSide/K14/FiveAtBase.lean makes these calls. thru_shared with thru_places gives them at
the second; this head names no file that makes that call, and none that calls halves_sends_at_base
or halves_sends_through.

What is assumed. h: the library's hypothesis at the full size (P5J.AtMgA, Johnson/P5J/MgAtAll.lean),
at the format's second hash function. hA: that onlineProverFromPublicFiles returns A.

What is not claimed. That the premises hold. Whether the two tests' sides are there (each list may
be empty). Nothing on what a side plays. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's blocksInOrder list, numbered from 0. A side
is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import AtFullSide.K12.ReturnsAtFillW
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.K14.FiveAmong
import Johnson.Desc.ProofFile.Honest.K14.SixThru

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile (Pub Ground SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (AtMgA TS)
open Desc.K14 (St)

/-! ## 1 The places of the two tests' sides -/

/-- A list of at most one member has no value twice. -/
theorem nodup_short {α β : Type} (f : α → β) : ∀ l : List α, l.length ≤ 1 → (l.map f).Nodup
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | _ :: _ :: l, h => absurd h (by show ¬ (l.length + 1 + 1 ≤ 1); omega)

variable {W₀ W₀' Rc' : Type}

/-- **The sides of the shared chain's two proximity tests**, as the filling lays them: the test on
the folded row's group, then the test on Omega's group. -/
abbrev testSides (I : WiderIn W₀) (Zp : Pub) :
    List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
    halfO (I.weights Zp) Zp

/-- **They stand at places that differ from each other and from the six.** -/
theorem testSides_places (I : WiderIn W₀) (Zp : Pub) :
    ((testSides I Zp).map (·.place)).Nodup ∧ ∀ g ∈ testSides I Zp, g.place ∉ sixPlaces := by
  have hU := AtFullSide.K12.halfU_place (I.weights Zp)
    (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp
  have hO := AtFullSide.K12.halfO_place (I.weights Zp) Zp
  have lU : (halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp).length ≤
      1 := by
    unfold halfU
    cases realU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp <;> simp
  have lO : (halfO (I.weights Zp) Zp).length ≤ 1 := by
    unfold halfO
    cases realO (I.weights Zp) Zp <;> simp
  refine ⟨?_, fun g hg => ?_⟩
  · rw [List.map_append]
    refine List.pairwise_append.2 ⟨nodup_short _ _ lU, nodup_short _ _ lO, fun a ha b hb e => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    have e' : x.place = y.place := e
    rw [hU x hx, hO y hy] at e'
    exact absurd e' (by decide)
  · rcases List.mem_append.1 hg with hg | hg
    · rw [hU g hg]
      decide
    · rw [hO g hg]
      decide

/-- Reading a side through keeps its place: so the same holds of the two tests' sides read through.
-/
theorem thru_places (I : WiderIn W₀) (Zp : Pub) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) :
    (((testSides I Zp).map (Placed.thru id (Common.thru g rd))).map (·.place)).Nodup ∧
      ∀ y ∈ (testSides I Zp).map (Placed.thru id (Common.thru g rd)), y.place ∉ sixPlaces := by
  obtain ⟨nd, off⟩ := testSides_places I Zp
  refine ⟨?_, fun y hy => ?_⟩
  · rw [List.map_map]
    exact nd
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact off x hx

/-! ## 2 The list -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the filling lays in the shared chain, under the hypothesis at the full size.** -/
theorem shared_at_base {o : SecondHashFunctionArgument} (h : AtMgA o Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground) :
    (onlineProverPartsInUse I o' S O).shared Zp G =
      proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp) (randNow (qAt Zp Np)) ++ testSides I Zp := by
  show sharedWithUO I Zp = _
  rw [sharedWithUO_ok I (nowSharedBy_at_head h (I.weights Zp)),
    sharedWithU_ok I (nowSharedBy_at_head h (I.weights Zp))]
  exact List.append_assoc _ _ _

/-- The public part that onlineProverFromPublicFiles returns at the hypothesis's files is the hypothesis's. General in
the filling. -/
theorem atPure_pub_at_head {W Rc Tr X₀ X : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W Rc Tr X₀ X} {A : OnlineProverWithDescription W Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : A.Z = Zp :=
  Except.ok.inj ((atPure_ok hA).1.symm.trans h.laid.pub)

/-- **The shared chain's sides of the prover that onlineProverFromPublicFiles returns at the filling.** -/
theorem base_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) :
    A.H.shared =
      proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp) (randNow (qAt Zp Np)) ++ testSides I Zp := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  rw [hs, atPure_pub_at_head h hA]
  exact shared_at_base h I o' S O A.G

/-- **The shared chain's sides of the prover that onlineProverFromPublicFiles returns at the filling read through g and
rd**: this kind's own sides and the two sendings' sides at the readers composed with g and rd; then
the two tests' sides, read through. -/
theorem thru_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o' S O)) = .ok A) :
    A.H.shared =
      proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp ∘ g) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp ∘ g) (randNow (qAt Zp Np) ∘ rd) ++
        (testSides I Zp).map (Placed.thru id (Common.thru g rd)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  rw [hs, atPure_pub_at_head h hA]
  show ((onlineProverPartsInUse I o' S O).shared Zp A.G).map (Placed.thru id (Common.thru g rd)) = _
  rw [shared_at_base h I o' S O A.G, List.map_append, List.map_append, halves_thru,
    sendHalves_thru]

/-! ## 3 The two fields of K14Asks -/

section Fields
variable {Bk : ProverCoinCounts} {P₁ Wt : Type} (ℓ : WitLens Wt) (N : NumbersS)

/-- **HalvesIn and SendsIn at the prover that onlineProverFromPublicFiles returns at the filling**, at the letters of the
proof file's own description: whatever the open letters are. -/
theorem halves_sends_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (Mg : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt) (shape : Nat → St → Bool)
    (nothingLeft : St → Bool) (order : St → Prop)
    (wit : Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Place × Table)
    (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ IndexCommitterCoins TableKey → Prop)
    (Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop) (Kp : Place → St → St → Prop)
    (w : Common W₀ IndexCommitterCoins TableKey) :
    HalvesIn (qAt Zp Np)
        (othersOf ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂
          Vd Rd Kp w) Zp.p.chains (tests Np) last
          (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
        (planData (qAt Zp Np)) (I.weights Zp) ∧
      SendsIn (qAt Zp Np)
        (othersOf ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂
          Vd Rd Kp w) Zp.p.chains (tests Np) last
          (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
        (planData (qAt Zp Np)) (I.weights Zp) (randNow (qAt Zp Np)) :=
  halves_among rfl (base_shared h I o' S O hA) (testSides_places I Zp).1 (testSides_places I Zp).2

/-- **HalvesIn and SendsIn at the prover that onlineProverFromPublicFiles returns at the filling read through g and rd**,
at the readers composed with g and rd. -/
theorem halves_sends_through (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o' S O)) = .ok A)
    (Mg : Common W₀' Rc' TableKey → MeaningS St P₁ Wt) (shape : Nat → St → Bool)
    (nothingLeft : St → Bool) (order : St → Prop)
    (wit : Coins Bk → Common W₀' Rc' TableKey → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Bk → Common W₀' Rc' TableKey → List Fmt.Drawn → Place × Table)
    (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀' Rc' TableKey → Prop)
    (Rd : Nat → Common W₀' Rc' TableKey → St → Prop) (Kp : Place → St → St → Prop)
    (w : Common W₀' Rc' TableKey) :
    HalvesIn (qAt Zp Np)
        (othersOf ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂
          Vd Rd Kp w) Zp.p.chains (tests Np) last
          (holds2 (qAt Zp Np) (I.weights Zp ∘ g) (randNow (qAt Zp Np) ∘ rd)))
        (planData (qAt Zp Np)) (I.weights Zp ∘ g) ∧
      SendsIn (qAt Zp Np)
        (othersOf ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂
          Vd Rd Kp w) Zp.p.chains (tests Np) last
          (holds2 (qAt Zp Np) (I.weights Zp ∘ g) (randNow (qAt Zp Np) ∘ rd)))
        (planData (qAt Zp Np)) (I.weights Zp ∘ g) (randNow (qAt Zp Np) ∘ rd) :=
  halves_among rfl (thru_shared h I g rd d' o' S O hA) (thru_places I Zp g rd).1
    (thru_places I Zp g rd).2

end Fields

end AtFullSide.K14

#print axioms AtFullSide.K14.nodup_short
#print axioms AtFullSide.K14.testSides_places
#print axioms AtFullSide.K14.thru_places
#print axioms AtFullSide.K14.shared_at_base
#print axioms AtFullSide.K14.atPure_pub_at_head
#print axioms AtFullSide.K14.base_shared
#print axioms AtFullSide.K14.thru_shared
#print axioms AtFullSide.K14.halves_sends_at_base
#print axioms AtFullSide.K14.halves_sends_through
