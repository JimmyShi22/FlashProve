-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/AtFill.lean: kind K13, the members' batching: which prover's side
a filling lays at the kind's place. At the filling `onlineProverPartsInUse`
(Honest/K1/Law/WSideAtFill.lean), and at that filling read through a reader of the index and a
reader of the stored tables' randomness (`OnlineProverParts.through`, Honest/ThruK13.lean): among the first
chain's sides, a side at a place of the kind K13 is the kind's own (`proverSideOfClaimCombination`, Part.lean of this
folder), the look-up by the place finds it, and it is the side of the one row of `k13SLot`
(RowsLot.lean of this folder). Two abbreviations; statements with their proofs. General in the
index's type, the readers and the open functions.

  `k13FillLot`   the filling's lot of the kind: `k13Lot` at the reader of the index that the filling
     lays at a public part, and at the open functions' filler of the pile
  `k13FillLot_mem`, `k13_only`   it is one of the filling's lots, and a side at a place of the kind
     comes from that lot alone
  `k13FillLot_thru_halves`   read through, it lays one side: the kind's, at the reader composed. The
     kind's parts do not read the stored tables' randomness, so that reader drops out
     (`k13Half_thru`, Honest/ThruK13.lean)
  `k13SLot_halves`, `k13FillLot_thru_rows`   the sides of the rows of `k13SLot`: that one side; so,
     lot by lot, what the filling's lot lays read through are the sides of these rows
  `k13_first_only`, `k13_first_found`   among the first chain's sides of the filling read through: a
     side at a place of the kind is the kind's side; the look-up by the kind's place finds it

  `atK13`, `filter_atK13_nil`, `filter_pairs_nil`, `filter_pairs_one`, `k13_filter_wider`,
     `k13_filter_through`   the same as an equation of lists: among the first chain's sides, in the
     filling's order, those at a place of the kind are just the sides of the rows of `k13SLot`: none
     twice and none beside. (Such equations kind by kind do not give the order between kinds; the
     equation lot by lot does.)

Words. A lot is a named list of prover's sides, made from the public part (`HLot`,
Honest/Frame.lean). A filling is the record of lots and readers from which `onlineProverFromPublicFiles`
(Honest/AtPure.lean) makes a prover (`OnlineProverParts`). The open functions are the record `OnlineProverArguments` of
functions that a filling takes as parameters; of them the kind reads `pile` alone.

Limits.
  * Equations of definitions and look-ups in lists. Nothing is said of what the side sends.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.RowsLot
import Johnson.Desc.ProofFile.Honest.K13.LotKind
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.K13 (whereOf)

variable {W₀ W₀' Rc' : Type}

/-- The filling's lot of the kind. -/
abbrev k13FillLot (I : WiderIn W₀) (O : OnlineProverArguments) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => k13Lot wt O.pile

/-- It is listed among the filling's ten lists, with its kind. -/
theorem k13FillLot_pair (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : (k13FillLot I O, KindName.K13) ∈ widerPairs I o Sz O := by
  unfold widerPairs
  exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- **It is one of the filling's lots.** -/
theorem k13FillLot_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : k13FillLot I O ∈ (onlineProverPartsInUse I o Sz O).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨_, k13FillLot_pair I o Sz O, rfl⟩)))

/-- **A side at a place of the kind K13 comes from that lot alone.** -/
theorem k13_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o Sz O).lots, ∀ x ∈ M.halves Zq G, x.place.kind = .K13 →
      M = k13FillLot I O := by
  intro M hM x hx hk
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk' := (FirstFill.widerKinds I o Sz O Zq G).all q hq x hx
    rw [List.inj_on_of_nodup_map widerPairs_nodup hq (k13FillLot_pair I o Sz O)
      (hk'.symm.trans hk)]
  · have h := closeLotAt_kinds I Sz Zq G x hx
    rw [hk] at h
    cases h
  · have h := proxLotAt_kinds I Sz Zq G x hx
    rw [hk] at h
    cases h
  · rw [wLotAt_halves] at hx
    cases hmsg : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hmsg] at hx
      cases hx
    | some msg =>
      rw [hmsg] at hx
      obtain rfl := List.mem_singleton.1 hx
      cases hk

/-- **Read through, the lot lays one side: the kind's, at the reader of the index composed.** -/
theorem k13FillLot_thru_halves (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (I : WiderIn W₀) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ((k13FillLot I O).thru (Local.thru g rd) (Local.thru g rd)).halves Zq G =
      [proverSideOfClaimCombination (I.weights Zq ∘ g) (O.pile Zq G) (whereOf Zq)] :=
  congrArg (fun h => [h]) (k13Half_thru g rd (I.weights Zq) (O.pile Zq G) (whereOf Zq)).symm

/-- **The sides of the rows of `k13SLot`: the kind's one side.** -/
theorem k13SLot_halves {W₁ Rc Xi Tr X Pb : Type} (weights : W₁ → Weights)
    (pile : Pub → Ground → PileOf Xi) (Zq : Pub) (G : Ground) :
    ((k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zq G).map (·.half) =
      [proverSideOfClaimCombination weights (pile Zq G) (whereOf Zq)] :=
  congrFun (congrFun (congrArg HLot.halves (k13SLot_toHLot (Pb := Pb) weights pile)) Zq) G

/-- **Lot by lot: the sides that the filling's lot of the kind lays, read through, are the sides of
the rows of `k13SLot`** at the reader of the index composed. This is the kind's share of an equation
of whole lists in the filling's order (`halves_of_lots`, Honest/Thread/Rows.lean); the lot's seat in
that order is `k13FillLot_pair`. -/
theorem k13FillLot_thru_rows {Pb : Type} (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (I : WiderIn W₀)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ((k13FillLot I O).thru (Local.thru g rd) (Local.thru g rd)).halves Zq G =
      ((k13SLot (Rc := Rc') (Tr := Cells) (X := Unit) (Pb := Pb) (I.weights Zq ∘ g) O.pile).rows Zq
        G).map (·.half) := by
  rw [k13FillLot_thru_halves, k13SLot_halves]

/-- **Among the first chain's sides of the filling read through, a side at a place of the kind is
the kind's side.** -/
theorem k13_first_only (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ x ∈ firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots,
      x.place.kind = .K13 → x = proverSideOfClaimCombination (I.weights Zq ∘ g) (O.pile Zq G) (whereOf Zq) := by
  intro x hx hk
  obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxM
  obtain rfl := k13_only I o Sz O Zq G M₀ hM₀ y hy hk
  have hs := List.mem_map_of_mem (f := Placed.thru (Local.thru g rd) (Local.thru g rd)) hy
  have hs' : y.thru (Local.thru g rd) (Local.thru g rd) ∈
      ((k13FillLot I O).thru (Local.thru g rd) (Local.thru g rd)).halves Zq G := hs
  rw [k13FillLot_thru_halves] at hs'
  exact List.mem_singleton.1 hs'

/-- **The look-up by the kind's place finds it.** -/
theorem k13_first_found (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    (firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots).find?
        (fun x => x.place == ⟨1, none, 3, .K13⟩) =
      some (proverSideOfClaimCombination (I.weights Zq ∘ g) (O.pile Zq G) (whereOf Zq)) := by
  have hm : proverSideOfClaimCombination (Rc := Rc') (Tr := Cells) (X := Unit) (I.weights Zq ∘ g) (O.pile Zq G)
      (whereOf Zq) ∈ firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots := by
    unfold firstOf
    refine List.mem_flatMap.2 ⟨(k13FillLot I O).thru (Local.thru g rd) (Local.thru g rd),
      List.mem_map.2 ⟨_, k13FillLot_mem I o Sz O, rfl⟩, ?_⟩
    rw [k13FillLot_thru_halves]
    exact List.mem_singleton.2 rfl
  have hsome : ((firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots).find?
      fun x => x.place == ⟨1, none, 3, .K13⟩).isSome = true :=
    List.find?_isSome.2 ⟨_, hm, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have e₀ := List.find?_some hy
  have hp : y.place = ⟨1, none, 3, .K13⟩ := beq_iff_eq.1 e₀
  rw [hy, k13_first_only g rd d I o Sz O Zq G y (List.mem_of_find?_eq_some hy) (by rw [hp])]

/-! ## As an equation of lists -/

/-- The test: a side is at a place of the kind K13. -/
abbrev atK13 {V W X : Type} (x : Placed V W X) : Bool := x.place.kind == KindName.K13

/-- Sides none of which is at a place of the kind: the test keeps none. -/
theorem filter_atK13_nil {V W X : Type} {l : List (Placed V W X)}
    (h : ∀ x ∈ l, x.place.kind ≠ .K13) : l.filter atK13 = [] :=
  List.filter_eq_nil_iff.2 fun x hx e => h x hx (beq_iff_eq.1 e)

/-- Of lots listed with their kinds, none of them K13: the test keeps no side. -/
theorem filter_pairs_nil {V W X : Type} (Zq : Pub) (G : Ground) :
    ∀ qs : List (HLot V W X × KindName),
      (∀ r ∈ qs, ∀ x ∈ r.1.halves Zq G, x.place.kind = r.2) → (∀ r ∈ qs, r.2 ≠ .K13) →
      ((qs.map (·.1)).flatMap fun M => M.halves Zq G).filter atK13 = []
  | [], _, _ => rfl
  | q :: qs, hk, hn => by
    rw [List.map_cons, List.flatMap_cons, List.filter_append,
      filter_atK13_nil fun x hx e => hn q (List.mem_cons.2 (Or.inl rfl))
        ((hk q (List.mem_cons.2 (Or.inl rfl)) x hx).symm.trans e),
      filter_pairs_nil Zq G qs (fun r hr => hk r (List.mem_cons_of_mem _ hr))
        fun r hr => hn r (List.mem_cons_of_mem _ hr)]
    rfl

/-- **Of lots listed with their kinds, no kind twice: the sides that the test keeps are those of the
lot that is listed with the kind K13**, in the list's order, none twice and none beside. -/
theorem filter_pairs_one {V W X : Type} (Zq : Pub) (G : Ground) (E : HLot V W X) :
    ∀ qs : List (HLot V W X × KindName),
      (∀ r ∈ qs, ∀ x ∈ r.1.halves Zq G, x.place.kind = r.2) → (qs.map (·.2)).Nodup →
      (E, KindName.K13) ∈ qs →
      ((qs.map (·.1)).flatMap fun M => M.halves Zq G).filter atK13 = E.halves Zq G
  | [], _, _, hE => by cases hE
  | q :: qs, hk, hn, hE => by
    have hn' : (q.2 :: qs.map (·.2)).Nodup := hn
    obtain ⟨n1, n2⟩ := List.nodup_cons.1 hn'
    rw [List.map_cons, List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.1 hE with e | hE'
    · subst e
      rw [filter_pairs_nil Zq G qs (fun r hr => hk r (List.mem_cons_of_mem _ hr))
        fun r hr e => n1 (List.mem_map.2 ⟨r, hr, e⟩), List.append_nil]
      exact List.filter_eq_self.2 fun x hx =>
        beq_iff_eq.2 (hk _ (List.mem_cons.2 (Or.inl rfl)) x hx)
    · rw [filter_atK13_nil fun x hx e => n1 (List.mem_map.2 ⟨_, hE',
          ((hk q (List.mem_cons.2 (Or.inl rfl)) x hx).symm.trans e).symm⟩),
        filter_pairs_one Zq G E qs (fun r hr => hk r (List.mem_cons_of_mem _ hr)) n2 hE']
      rfl

/-- **Among the first chain's sides of the filling, those at a place of the kind K13 are, as a list,
the kind's one side.** -/
theorem k13_filter_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    (firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).filter atK13 =
      [proverSideOfClaimCombination (I.weights Zq) (O.pile Zq G) (whereOf Zq)] := by
  unfold firstOf
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots, List.flatMap_append, List.flatMap_append,
    List.flatMap_append, List.filter_append, List.filter_append, List.filter_append,
    filter_pairs_one Zq G (k13FillLot I O) (widerPairs I o Sz O)
      (FirstFill.widerKinds I o Sz O Zq G).all widerPairs_nodup (k13FillLot_pair I o Sz O)]
  have c1 : ((closeLotAt I Sz :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G).filter
      atK13 = [] :=
    filter_atK13_nil fun x hx e => by
      have h := closeLotAt_kinds I Sz Zq G x hx
      rw [e] at h
      cases h
  have c2 : ((proxLotAt I Sz :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G).filter
      atK13 = [] :=
    filter_atK13_nil fun x hx e => by
      have h := proxLotAt_kinds I Sz Zq G x hx
      rw [e] at h
      cases h
  have c3 : ((wLotAt I o O :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G).filter
      atK13 = [] :=
    filter_atK13_nil fun x hx e => by
      rw [wLotAt_halves] at hx
      cases hmsg : OnBytes.linMessageW Zq.first.lin with
      | none =>
        rw [hmsg] at hx
        cases hx
      | some msg =>
        rw [hmsg] at hx
        obtain rfl := List.mem_singleton.1 hx
        cases e
  rw [List.flatMap_singleton, List.flatMap_singleton, List.flatMap_singleton, c1, c2, c3]
  rfl

/-- **The same at the filling read through**: as a list, the sides at a place of the kind are the
sides of the rows of `k13SLot` at the reader of the index composed. -/
theorem k13_filter_through {Pb : Type} (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀')
    (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub)
    (G : Ground) :
    (firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots).filter atK13 =
      ((k13SLot (Rc := Rc') (Tr := Cells) (X := Unit) (Pb := Pb) (I.weights Zq ∘ g) O.pile).rows Zq
        G).map (·.half) := by
  have e : firstOf Zq G (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots =
      (firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
    unfold firstOf
    show ((onlineProverPartsInUse I o Sz O).lots.map
      (HLot.thru (Local.thru g rd) (Local.thru g rd))).flatMap (fun l => l.halves Zq G) = _
    rw [List.flatMap_map, List.map_flatMap]
    rfl
  have ef : ((firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).map
      (Placed.thru (Local.thru g rd) (Local.thru g rd))).filter atK13 =
      ((firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).filter atK13).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
    rw [List.filter_map]
    rfl
  rw [e, ef, k13_filter_wider, k13SLot_halves, List.map_singleton, ← k13Half_thru]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.filter_atK13_nil
#print axioms ProofFile.Honest.K13.filter_pairs_nil
#print axioms ProofFile.Honest.K13.filter_pairs_one
#print axioms ProofFile.Honest.K13.k13_filter_wider
#print axioms ProofFile.Honest.K13.k13_filter_through
#print axioms ProofFile.Honest.K13.k13FillLot_pair
#print axioms ProofFile.Honest.K13.k13FillLot_mem
#print axioms ProofFile.Honest.K13.k13_only
#print axioms ProofFile.Honest.K13.k13FillLot_thru_halves
#print axioms ProofFile.Honest.K13.k13SLot_halves
#print axioms ProofFile.Honest.K13.k13FillLot_thru_rows
#print axioms ProofFile.Honest.K13.k13FillLot
#print axioms ProofFile.Honest.K13.atK13
#print axioms ProofFile.Honest.K13.k13_first_only
#print axioms ProofFile.Honest.K13.k13_first_found
