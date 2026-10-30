-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillKinds.lean: OF THE NINE FIELDS OF WiderKinds
(Honest/Thread/FirstFill.lean: "every side of the list is at a place of the list's kind", a field a
list of the filling of record) EIGHT ARE SHOWN, WITH NO PREMISE: all but K6's. Statements with their
proofs; no definition.

  BY THE LISTS' AUTHORS' OWN LEMMAS, called: K3's: K3.Law.rowLotAt_kind
  (Honest/K3/Law/LotKind.lean) · K4's: K4.k4HLot_kind (Honest/K4/Law/LotKind.lean) · K5's:
  K5.k5LotK_kind (Honest/K5/Law/LotKind.lean) · K13's: K13.k13Lot_kind (Honest/K13/LotKind.lean).
  TYPED HERE OFF THE LISTS' TEXTS, each general in the list's arguments, the public part and the
  ground:
  k1_blocks_kind      every sub-protocol of the description's list for K1 is at a place of the kind
  k1_kind             K1's: the sides' places are those sub-protocols' (dataSideNo_places,
                      Honest/K1/LotNoPure.lean)
  k1_blocks_linked · k1_linked   each of these places names a segment: so K1's list has no side at a
                      place behind the segments
  k2_kind             K2's: a side's place is taken out of a list that is filtered by the kind
  k8_kind · k11_kind  a side's place is written in the list's text with its kind
  widerKinds_of_one   CONDITIONAL: **WiderKinds from the one field that is left: K6's**

THESE ARE LEMMAS ON OTHER AUTHORS' LISTS (Honest/K1/LotNoPure.lean with the library's
Johnson/Desc/ProofFile/Lot/K1.lean · K2/AtPlan.lean and Half.lean · K8/Part.lean · K11/Part.lean).
Where a list's authors have the like lemma in a file of their own, theirs is the one
to keep and this one to strike.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. K6's field is a hypothesis of widerKinds_of_one: shown of nothing here. The statements are
about lists and places: they say at which KIND of place a side stands, not that a sub-protocol
stands there, nor which side it is. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFill
import Johnson.Desc.ProofFile.Honest.K3.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K4.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K5.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K13.LotKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ Rc Xi Tr V W X : Type}

/-- **Every sub-protocol of the description's list for K1 is at a place of the kind K1**, where
nothing quiet is laid behind the reads. No premise. -/
theorem k1_blocks_kind (Z : Pub) (G : Ground) :
    ∀ b ∈ (VerifiableInference.Desc.K1.lotWith (fun _ _ _ => none) Z).own G,
      b.place.kind = .K1 := by
  intro b hb
  rcases List.mem_append.1 hb with h | h
  · obtain rfl := List.mem_singleton.1 h
    rfl
  · obtain ⟨⟨Y, l⟩, _, hy⟩ := List.mem_flatMap.1 h
    dsimp only at hy
    split at hy
    · cases hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> rfl

/-- **Every side of K1's list is at a place of the kind K1.** No premise. -/
theorem k1_kind (S : OnBytes.HonestTrace.Sz) (wit : W → K1.PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (Z : Pub) (G : Ground) :
    ∀ x ∈ (K1.dataSideNo (V := V) (X := X) S wit o).halves Z G, x.place.kind = .K1 := by
  intro x hx
  have hm : x.place ∈ ((K1.dataSideNo (V := V) (X := X) S wit o).halves Z G).map (·.place) :=
    List.mem_map.2 ⟨x, hx, rfl⟩
  rw [K1.dataSideNo_places S wit o (fun _ _ _ => none) Z G] at hm
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
  rw [← e]
  exact k1_blocks_kind Z G b hb

/-- Every sub-protocol of the description's list for K1 is at a place that names a segment. No
premise. -/
theorem k1_blocks_linked (Z : Pub) (G : Ground) :
    ∀ b ∈ (VerifiableInference.Desc.K1.lotWith (fun _ _ _ => none) Z).own G,
      b.place.link ≠ none := by
  intro b hb
  rcases List.mem_append.1 hb with h | h
  · obtain rfl := List.mem_singleton.1 h
    exact Option.some_ne_none _
  · obtain ⟨⟨Y, l⟩, _, hy⟩ := List.mem_flatMap.1 h
    dsimp only at hy
    split at hy
    · cases hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> exact Option.some_ne_none _

/-- **Every side of K1's list is at a place that names a segment.** No premise. -/
theorem k1_linked (S : OnBytes.HonestTrace.Sz) (wit : W → K1.PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (Z : Pub) (G : Ground) :
    ∀ x ∈ (K1.dataSideNo (V := V) (X := X) S wit o).halves Z G, x.place.link ≠ none := by
  intro x hx
  have hm : x.place ∈ ((K1.dataSideNo (V := V) (X := X) S wit o).halves Z G).map (·.place) :=
    List.mem_map.2 ⟨x, hx, rfl⟩
  rw [K1.dataSideNo_places S wit o (fun _ _ _ => none) Z G] at hm
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
  rw [← e]
  exact k1_blocks_linked Z G b hb

/-- **Every side of the code switch's list is at a place of the kind K2.** No premise. -/
theorem k2_kind (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K2.switchLot (X := X) D readers).halves Z G, x.place.kind = .K2 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  show p.place.kind = .K2
  unfold K2.switchPlaces at hp
  split at hp
  · obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hp
    exact eq_of_beq (List.mem_filter.1 hsp).2
  · cases hp

/-- **Every side of the smallness test's list is at a place of the kind K8.** No premise. -/
theorem k8_kind (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat)) (Z : Pub)
    (G : Ground) :
    ∀ x ∈ (K8.smallLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells mats).halves Z G,
      x.place.kind = .K8 := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  rfl

/-- **The one side of the list of the merge of the weights' claims is at a place of the kind K11.**
No premise. -/
theorem k11_kind (claims : Pub → Ground → Inst → List Fmt.Drawn → List OnBytes.Model.WsClaim)
    (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K11.headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).halves Z G,
      x.place.kind = .K11 := by
  intro x hx
  obtain rfl := List.mem_singleton.1 hx
  rfl

/-- **WiderKinds FROM THE ONE FIELD THAT IS LEFT.** CONDITIONAL: k6: the field of that name, to the
letter. -/
theorem widerKinds_of_one {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {Z : Pub} {G : Ground}
    (k6 : ∀ x ∈ (K6.headLot K6.headFitsB (K6.headWit' id (I.weights Z)) :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
      x.place.kind = .K6) : WiderKinds I o S O Z G :=
  { k1 := k1_kind _ _ _ Z G
    k2 := k2_kind _ _ Z G
    k11 := k11_kind _ _ Z G
    k13 := K13.k13Lot_kind _ _ Z G
    k3 := K3.Law.rowLotAt_kind _ Z G
    k4 := K4.k4HLot_kind _ _ _ Z G
    k5 := K5.k5LotK_kind id O.keyOf Z G
    k6 := k6
    k8 := k8_kind _ _ Z G }

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k1_blocks_kind
#print axioms ProofFile.Honest.FirstFill.k1_kind
#print axioms ProofFile.Honest.FirstFill.k1_blocks_linked
#print axioms ProofFile.Honest.FirstFill.k1_linked
#print axioms ProofFile.Honest.FirstFill.k2_kind
#print axioms ProofFile.Honest.FirstFill.k8_kind
#print axioms ProofFile.Honest.FirstFill.k11_kind
#print axioms ProofFile.Honest.FirstFill.widerKinds_of_one
