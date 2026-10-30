-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/KindPlaces.lean: kind K13, the members' batching: where the kind
stands in the proof file's description, in all three chains; and the kind's conditions `fits`,
`exact` and `fresh` of `Good` (Honest/Side.lean) asked by kind: at every list of parts that stands
at a place of the kind K13, in each of the three chains. Under the library's head h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). Statements with their proofs, three of them evaluations in Lean's kernel;
no definition. At the full size and at the hash `OnBytes.secondHashFunction` alone.

  `wp_shared_no_K13`, `wp_second_no_K13`   the written plan's shared and second chain have no place
     of the kind K13. `wp_shared_has_K14`: the same test at the kind K14 fails, so it can say no
  `k13_places_of_kind`   under h: in the first chain every sub-protocol at a place of the kind K13
     is at the kind's one place; the shared and the second chain have none
  `k13_kind_pays`   at sides G of the head's description and the book that `bookWhole` returns: at
     every list of G at a place of the kind K13, at every side that it has there, a term of `Good`
     at the list's own `On` and `bud`, with `pre`, face, order, chain number and first tree as the
     frame's rule for a file lays them (`hand₁`, `hand₂`, `hand₃` of `file_owed_rows`,
     Honest/Thread/Rows.lean)
  `k13_kind_pays_of_eq`, `k13_kind_pays_atPure`   the same at a description that is equal to the
     head's, and so at sides of the description and the book that `onlineProverFromPublicFiles` (Honest/AtPure.lean)
     returns at the head's files, at any filling

Limits.
  * `k13_kind_pays` takes one hypothesis on G (hG): each list of G's first chain at a place of the
    kind is a row of `k13SLot` at some reader of the index and some filler of the pile. Who lays G
    has to show it. In the shared and the second chain nothing is asked of G: no list of the kind
    has a side there.
  * The terms of `Good` stand at A := B := False. What they pay and what they do not: the head of
    GoodRows.lean of this folder, whose Limits all hold here.
  * Nothing is said of the key file's description.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.GoodRows
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K13.Found355
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain alike₂_place)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)
open ProofFile.Honest.K14 (planAlike_at_head)

set_option maxRecDepth 1000000 in
/-- The written plan's shared chain has no place of the kind K13. By the kernel. -/
theorem wp_shared_no_K13 : (WP.shared.blocksInOrder.all fun b => b.place.kind != .K13) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written plan's second chain has no place of the kind K13. By the kernel. -/
theorem wp_second_no_K13 : (WP.second.blocksInOrder.all fun b => b.place.kind != .K13) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can say no: the shared chain has a place of the kind K14. By the kernel. -/
theorem wp_shared_has_K14 : (WP.shared.blocksInOrder.all fun b => b.place.kind != .K14) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}

include h in
/-- **Where the kind stands in the head's description**: in the first chain at its one place; in the
shared and in the second chain nowhere. -/
theorem k13_places_of_kind :
    (∀ b ∈ cF.blocksInOrder, b.place.kind = .K13 → b.place = ⟨1, none, 3, .K13⟩) ∧
      (∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place.kind ≠ .K13) ∧
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, b.place.kind ≠ .K13 := by
  have A := planAlike_at_head h
  refine ⟨fun b hb hk => ?_, fun b hb hk => ?_, fun b hb hk => ?_⟩
  · have e := P5J.At.places_paid h.scope h.reads h.laid
    have hm : b.place ∈ P5J.At.ps := by
      rw [← e]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    have q := List.all_eq_true.1 ps_K13_one _ hm
    rw [hk] at q
    simpa using q
  · have hm : b.place ∈ WP.shared.blocksInOrder.map (·.place) := by
      rw [alike₂_place _ _ A.shared]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hwp⟩ := List.mem_map.1 hm
    have q : (w.place.kind != .K13) = true := List.all_eq_true.1 wp_shared_no_K13 w hw
    rw [hwp, hk] at q
    cases q
  · have hm : b.place ∈ WP.second.blocksInOrder.map (·.place) := by
      rw [alike₂_place _ _ A.second]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hwp⟩ := List.mem_map.1 hm
    have q : (w.place.kind != .K13) = true := List.all_eq_true.1 wp_second_no_K13 w hw
    rw [hwp, hk] at q
    cases q

include h in
/-- **`fits`, `exact` and `fresh`, asked by kind, in the form of the rule's three hypotheses on
the rows' authors.** hG: each list of G's first chain at a place of the kind is a row of `k13SLot`.
The second and the third part hold because no list of the kind has a side in these chains. -/
theorem k13_kind_pays {W₀ Rc Ky Tr X₀ X : Type}
    {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 M = .ok Bk)
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hG : ∀ L ∈ G.first, L.place.kind = .K13 →
      L.bare ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := ProofFile.Inst) weights pile).rows Zp Gr) :
    (∀ L ∈ G.first, L.place.kind = .K13 → ∀ σ,
        L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder G.falls₁ = some σ →
        ∃ A' B', Good (preOf 0 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 0)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder L.place) .own σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 0 0 A' B' L.On L.bud) ∧
      (∀ L ∈ G.shared, L.place.kind = .K13 → ∀ σ,
        L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 1)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder L.place) .shared σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 1 0 A' B' L.On L.bud) ∧
      ∀ L ∈ G.second, L.place.kind = .K13 → ∀ σ,
        L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder G.falls₃ = some σ →
        ∃ A' B', Good (preOf 2 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
            (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 2)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder L.place) .own σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 2
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber A' B' L.On L.bud := by
  obtain ⟨-, p2, p3⟩ := k13_places_of_kind h
  refine ⟨fun L hL hk σ hσ => ?_, fun L _ hk σ hσ => ?_, fun L _ hk σ hσ => ?_⟩
  · exact ⟨_, _, (k13_good_rows h hW weights pile Gr _ .own _ 0 0 G.falls₁ L.bare
      (hG L hL hk)).2 σ hσ⟩
  · exact absurd (by rw [sideSeated_place hσ]; exact hk) (p2 σ.block (sideSeated_mem hσ))
  · exact absurd (by rw [sideSeated_place hσ]; exact hk) (p3 σ.block (sideSeated_mem hσ))

include h in
/-- The same at a description F that is equal to the head's. -/
theorem k13_kind_pays_of_eq {W₀ Rc Ky Tr X₀ X : Type} {F : VerifiableInference.Desc.FileDescription
    ProofFile.Inst} (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 M = .ok Bk)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hG : ∀ L ∈ G.first, L.place.kind = .K13 →
      L.bare ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := ProofFile.Inst) weights pile).rows Zp Gr) :
    (∀ L ∈ G.first, L.place.kind = .K13 → ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
        ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0
          A' B' L.On L.bud) ∧
      (∀ L ∈ G.shared, L.place.kind = .K13 → ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1
          0 A' B' L.On L.bud) ∧
      ∀ L ∈ G.second, L.place.kind = .K13 → ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
        ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
          (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud := by
  subst eF
  exact k13_kind_pays h hW G weights pile Gr hG

include h in
/-- **The same at what `onlineProverFromPublicFiles` returns at the head's files**, at any filling: at sides G of the
returned description and book. -/
theorem k13_kind_pays_atPure {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Ky : Type} (G : Sides A.F A.B W₀ Rc Ky Tr X₀ X)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hG : ∀ L ∈ G.first, L.place.kind = .K13 →
      L.bare ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := ProofFile.Inst) weights pile).rows Zp Gr) :
    (∀ L ∈ G.first, L.place.kind = .K13 → ∀ σ, L.side A.F.first.blocksInOrder G.falls₁ = some σ →
        ∃ A' B', Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder L.place) .own σ A.B (orderOf A.F)
          0 0 A' B' L.On L.bud) ∧
      (∀ L ∈ G.shared, L.place.kind = .K13 → ∀ σ, L.side A.F.shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf A.F 1) A.F.shared.blocksInOrder L.place) .shared σ A.B
          (orderOf A.F) 1 0 A' B' L.On L.bud) ∧
      ∀ L ∈ G.second, L.place.kind = .K13 → ∀ σ, L.side A.F.second.blocksInOrder G.falls₃ = some σ →
        ∃ A' B', Good (preOf 2 A.F.lastChainFirstTreeNumber (earlierOf A.F 2) A.F.second.blocksInOrder L.place) .own σ A.B
          (orderOf A.F) 2 A.F.lastChainFirstTreeNumber A' B' L.On L.bud :=
  k13_kind_pays_of_eq h (Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value))
    (ProofFile.Honest.K14.atPure_book_at_head h hA) G weights pile Gr hG

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_kind_pays_of_eq
#print axioms ProofFile.Honest.K13.k13_kind_pays_atPure
#print axioms ProofFile.Honest.K13.wp_shared_no_K13
#print axioms ProofFile.Honest.K13.wp_second_no_K13
#print axioms ProofFile.Honest.K13.wp_shared_has_K14
#print axioms ProofFile.Honest.K13.k13_places_of_kind
#print axioms ProofFile.Honest.K13.k13_kind_pays
