-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtBase.lean: K14's SIX ROWS AT THE BASE FILLING, UNDER ONE HEAD: at the return of `baseMaker` (E2E/BaseMaker.lean), the filling that `onlineFilling` reads through: that it returns; that its shared sides begin with the six
rows' halves, over the matrix's reader and the stored randomness; and, of the same rows, at the same `On` and `bud`, in one statement: `Good`, `OnFromS` at every frame's sentence over the shared list, the body of bud₂; and the shared clause of `KindPays`
(Johnson/T3/OwedOfKinds.lean's, not the completeness' of Honest/Law/ReadyOfSides.lean) at every list of sides. Of the six rows four stand at K14's places and two, the sendings, at K1's.

  `baseRows`       the six rows at the base's readers
  `base_shared`    `baseFilling`'s shared field begins with their halves, and all that stands behind them is of kind K12
  `base_apart`, `base_named`, `base_fit_mem`, `base_fit`   the six places are apart; each has a side of the filling; a side there is the row's half
  `K14AtBase`      what is said, as one proposition
  `k14_at_base`    under the head at the files' own data, where the verifier's test on the files accepts
  `k14_at_base_named`, `k14_at_base_zFull`   **at either named set; at the stored files, under no premise**



Limits. FITS, EXACT AND FRESH AT SIX ROWS: not the kind's all. AT A := False: plays and acc are met for nothing. From AtFullSide/K14/BudAtNamed.lean, which the bud₂ clause carries: THAT A RUN ASKS FOR NO POSITION BEYOND WHAT THE FRAME's LIST treeAsks HOLDS IS NOT SAID; ONE REQUEST: nothing on the union of the positions that the requests of a batch read. The clauses are typed at St, ProofFile.Cl, F0T: a caller at returned.F carries them over the return's equation. The clause of `KindPays` asks that the sides' rows of that kind have a six-row's letters (`rows`). The six are the owners' half: every coin of the two sendings goes on to K12 as carried, and what
K12 shows is K12's. Nothing says what a run shows. The online return, and the crossing from this one to it, are not here. No property of the protocol is claimed: nothing on its soundness, completeness, binding or hiding.
-/
import E2E.BaseMaker
import AtFullSide.K14.Sim.Debts
import AtFullSide.K14.Sim.AtTerm
import AtFullSide.K12.ReturnsAtAnyIndex
import AtFullSide.Honest.TermMade
import AtFullSide.K14.BudAtNamed
import AtFullSide.K14.Sim.RestKinds
import Johnson.Desc.ProofFile.Honest.K14.FreshAtTestPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Block)
open Desc.K14 (St)
open ProofFile.Honest.K14
open ProofFile.Honest.K12.AtProof (halfU halfO sharedWithUO)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The six rows at the base's readers. -/
noncomputable def baseRows (Zp : ProofFile.Pub) (Np : H2U.Places4) :
    List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) :=
  simRows (simData Zp Np) (simPub Zp Np) (matrixInput.weights Zp) (randNow (qAt Zp Np))

/-- **`baseFilling`'s shared field begins with the six rows' halves.** -/
theorem base_shared (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : Ground) :
    ∃ rest, (baseFilling files).shared Zp G = (baseRows Zp Np).map (·.half) ++ rest ∧
      ∀ x ∈ rest, x.place.kind = .K12 := by
  have hs := simRows_now (Pb := TableKey) h (matrixInput.weights Zp)
  refine ⟨halfU (matrixInput.weights Zp)
      (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp ++
    halfO (matrixInput.weights Zp) Zp, ?_, ProofFile.Honest.K12.AtProof.rest_kind _ _ _⟩
  show sharedWithUO matrixInput Zp = _
  unfold sharedWithUO
  rw [hs]
  simp only [List.append_assoc]
  rfl

/-- The six places are apart. -/
theorem base_apart (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) :
    ((baseRows Zp Np).map (·.place)).Nodup := by
  unfold baseRows
  rw [simRows_places h]
  decide

/-- No row of the six stands at a place of kind K12. -/
theorem base_not_K12 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) (hr : r ∈ baseRows Zp Np) :
    r.place.kind ≠ .K12 := by
  have hm : r.place ∈ (baseRows Zp Np).map (·.place) := List.mem_map_of_mem hr
  unfold baseRows at hm
  rw [simRows_places h] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e <;> rw [e] <;> decide

/-- **Each row's place has a side of the filling.** -/
theorem base_named (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : Ground) :
    ∀ r ∈ baseRows Zp Np, ((baseFilling files).shared Zp G).any (fun x => x.place == r.place) = true := by
  intro r hr
  obtain ⟨rest, e, -⟩ := base_shared (files := files) h G
  rw [e]
  exact List.any_eq_true.2 ⟨r.half, List.mem_append_left _ (List.mem_map_of_mem hr), by simp [Unlettered.half]⟩

/-- **By membership: a side of the filling at a row's place is the row's half.** -/
theorem base_fit_mem (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ (baseFilling files).shared Zp G, ∀ r ∈ baseRows Zp Np, r.place = x.place → r.half = x := by
  intro x hx r hr hp
  obtain ⟨rest, e, k⟩ := base_shared (files := files) h G
  rw [e] at hx
  rcases List.mem_append.1 hx with g | g
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 g
    have e' : r = r' := List.inj_on_of_nodup_map (base_apart (files := files) h) hr hr' hp
    rw [e']
  · exact absurd (hp ▸ k x g) (base_not_K12 (files := files) h r hr)

/-- **The same through the search among the rows.** -/
theorem base_fit (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ (baseFilling files).shared Zp G, ∀ r,
      ((baseRows Zp Np).find? fun r => r.place == x.place) = some r → r.half = x := by
  intro x hx r hf
  have hr := List.mem_of_find?_eq_some hf
  have hp : (r.place == x.place) = true :=
    List.find?_some (p := fun r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey =>
      r.place == x.place) hf
  exact base_fit_mem (files := files) h G x hx r hr (beq_iff_eq.1 hp)

/-- **K14 at the base's return, in one statement.** `Tr`, `X` and the sides of the last clause are any. -/
def K14AtBase (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (x₀ : VerifiableInference.Desc.First.Look.Place) (returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit),
    P5J.AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) Zp Np cF x₀ ∧
    baseMaker files = .ok returned ∧ returned.Z = Zp ∧
    returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ OwnClear returned.B ∧
    (baseRows Zp Np).map (·.place) =
      [place 1, place 4, place 7, place 8, sendPlace 2, sendPlace 5] ∧
    (∃ rest, returned.H.shared = (baseRows Zp Np).map (·.half) ++ rest ∧
      ∀ x ∈ rest, x.place.kind = .K12) ∧
    -- which coins the field fresh speaks of at "send o_u" and the test on G_u's first part
    (∃ e₁, returned.B.spentBy ⟨sendPlace 2, 0⟩ ⟨⟨2, none, 9, .K12⟩, 0⟩ = [e₁] ∧
      e₁.start = ⟨0, 10808⟩ ∧ e₁.count = ⟨0, 15⟩) ∧
    (∃ x, returned.B.knownBy (orderOf returned.F) ⟨sendPlace 2, 0⟩ ⟨⟨2, none, 9, .K12⟩, 0⟩ = [x] ∧
      x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, 10808⟩) ∧
    -- Good
    (∀ (fs : List (Fall St)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
      (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey), r ∈ baseRows Zp Np →
      ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
        Good pre .shared σ returned.B (orderOf returned.F) 1 0 (fun _ _ _ _ => False)
          (fun _ _ _ _ => False) r.On r.bud) ∧
    -- OnFromS
    (∀ (T₂ : Thread returned.B St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey),
      T₂.bs = (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder →
      ∀ (S₂ : Nat → Coins returned.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
        (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey), r ∈ baseRows Zp Np →
      ∀ (L : Lettered returned.B St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey),
        L.place = r.place → L.row = r.row → L.On = r.On → ∀ (b : Nat) (blk : Block St ProofFile.Cl),
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[b]? = some blk → blk.place = L.place →
        ∀ len : Nat → Nat → Nat, OnFromS T₂ S₂ L b len) ∧
    -- bud₂
    (∀ (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey), r ∈ baseRows Zp Np →
      ∀ (L : Lettered returned.B St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey),
        L.place = r.place → L.row = r.row → L.bud = r.bud →
        ∀ τ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
          ∀ (pre t : List (Block St ProofFile.Cl)) (n : Nat),
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
          n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
          ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
          L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
            (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
              (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
                (·.2.length)).sum)) ∧
    -- the shared clause of KindPays
    (∀ (Tr X : Type) (G : Sides returned.F returned.B FullSizeMatrix IndexCommitterCoins TableKey Tr Unit X)
      (κ : VerifiableInference.Desc.KindName),
      (∀ L ∈ G.shared, L.place.kind = κ → ∃ r ∈ baseRows Zp Np,
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) →
      ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side returned.F.shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf returned.F 1) returned.F.shared.blocksInOrder L.place) .shared σ
          returned.B (orderOf returned.F) 1 0 A' B' L.On L.bud)

/-- **Under the head at the files' own data, where the verifier's test accepts.** -/
theorem k14_at_base
    (h : P5J.AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) Zp Np cF x₀)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) : K14AtBase files := by
  obtain ⟨A, hA, -, -, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest range_matrixInput
  obtain ⟨eZ, eF, hc, hall⟩ := six_at_atPure h hA
  obtain ⟨-, -, -, -, -, -, -, -, hS, -⟩ := atPure_ok hA
  obtain ⟨-, hU⟩ := fresh_u_at_test_part_head h _ _ _ _ _ _ A hA
  obtain ⟨⟨r, hr, hp⟩, hrows⟩ := hU FullSizeMatrix IndexCommitterCoins TableKey Unit (matrixInput.weights Zp) (randNow (qAt Zp Np))
  obtain ⟨⟨L, c1, c2, c3, c4⟩, -, hL⟩ := hrows r hr hp
  obtain ⟨hs, h2⟩ := hL L c1 c2 c3 c4
  obtain ⟨σ, hσ⟩ := hs []
  obtain ⟨hm, -, h3⟩ := h2 [] σ hσ
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hm
  obtain ⟨b1, b2, ⟨e₁, s1, -, -, s4, s5⟩, ⟨x, k1, k2, k3⟩, -⟩ := h3 u hu _ rfl
  rw [b1, b2] at s1 k1
  refine ⟨Zp, Np, cF, x₀, A, h, hA, eZ, eF, hc, simRows_places h _ _, ?_, ⟨e₁, s1, s4, s5⟩,
    ⟨x, k1, k2, k3⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨rest, e, k⟩ := base_shared (files := files) h A.G
    exact ⟨rest, by rw [hS, eZ]; exact e, k⟩
  · exact fun fs pre r hr => hall _ _ _ _ _ _ fs r pre hr
  · exact fun T₂ hbs S₂ r hr L c1 c2 c3 b blk hx hp len =>
      AtFullSide.K14.six_onFromS h T₂ hbs S₂ _ _ r hr L c1 c2 c3 b blk hx hp len
  · exact fun r hr L c1 c2 c4 =>
      AtFullSide.K14.six_bud_at_head h live _ _ _ _ A.B _ _ r hr L c1 c2 c4
  · exact fun Tr X G κ rows => kind_clause_at_return h hA _ _ G κ rows

/-- **At either named set, under no premise.** -/
theorem k14_at_base_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : K14AtBase files := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named files hZ
  exact k14_at_base h (AtFullSide.K14.live_named files hZ)

/-- **AT THE STORED FILES, UNDER NO PREMISE.** -/
theorem k14_at_base_zFull : K14AtBase VerifierAndGoals.storedPublicFiles := k14_at_base_named _ (Or.inl rfl)

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.base_shared
#print axioms ProofFile.Honest.Term.base_apart
#print axioms ProofFile.Honest.Term.base_named
#print axioms ProofFile.Honest.Term.base_fit_mem
#print axioms ProofFile.Honest.Term.base_fit
#print axioms ProofFile.Honest.Term.k14_at_base
#print axioms ProofFile.Honest.Term.k14_at_base_named
#print axioms ProofFile.Honest.Term.k14_at_base_zFull
