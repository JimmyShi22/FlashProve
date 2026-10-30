-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/KindPaysAtFill.lean: the smallness test at a filling whose lots lay no other side of the
kind: the kind pays,
in the form `KindPays` (Honest/Law/ReadyOfSides.lean): at the book that the maker returns,
`chainSteps` returns at each of the kind's members, at every view and every run's coins. That is what
`ready` asks of this kind, and no more: nothing here says that a part plays or that a verifier
accepts. One theorem.

What is assumed. The public head h, that the maker returns A, and that no lot but the kind's lays a side of
the kind (`ho_base`).
Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K8.SimAtFill
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open ProofFile.Honest ProofFile.Honest.K8
open OnBytes OnBytes.Model.Stages
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS)

variable {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Each side of the kind's lot pays, at the book of any return of the maker.** The lot's own types
are free of the filling's. -/
theorem k8_sidePays {W₁ R₁ X₁ : Type}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) :
    ∀ g ∈ (smallLot (W₀ := W₁) (Rc := R₁) (Xi := ProofFile.Inst) (X := X₁) id matsO).halves A.Z A.G,
      SidePays A.B 0 cF.blocksInOrder g := by
  intro g hgM b hb hp hs hf v k
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have h25 : A.G.built.size = 25 := (IM.ground_gets h.scope h.reads hZ hG).1
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hgM
  have hX : A.G.built[y.2]? = some y.1 := by
    have e := List.mem_zipIdx_iff_getElem?.1 hy
    rwa [Array.getElem?_toList] at e
  have hl : y.2 < 25 := h25 ▸ (Array.getElem?_eq_some_iff.1 hX).1
  obtain ⟨G₀, Xl, blk, hb₀, hX', hfl, hpl, hse, ho⟩ := small_block_at h hl
  obtain rfl : G₀ = A.G := Option.some.inj (hb₀.symm.trans hG)
  obtain rfl : Xl = y.1 := Option.some.inj (hX'.symm.trans hX)
  have hbm : blk ∈ cF.blocksInOrder := List.mem_of_getElem? hfl
  obtain rfl : b = blk :=
    List.inj_on_of_nodup_map (first_nodup h) hb hbm (hp.trans hpl.symm)
  have hB := book_at_maker h hA
  have hkind : b.place.kind = KindName.K8 := by rw [hp]; rfl
  have hps : b.place ∈ P5J.At.ps := by
    have e := P5J.At.places_paid h.scope h.reads h.laid
    rw [← e]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  have hmem : smallPlace (ProofFile.k8Par A.Z A.G y.1 y.2) ∈
      placesAt (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) 0 := by
    refine List.mem_map.2 ⟨b, hb, ?_⟩
    exact hpl
  obtain ⟨c, hc⟩ := k8_lendRow (W₁ := W₁) (R₁ := R₁) (Xi := ProofFile.Inst) (X₁ := X₁) h hA id
    (ProofFile.k8Par A.Z A.G y.1 y.2, K3.matsOwn A.G.W y.2) hmem k
  refine ⟨_, chainSteps_side A.B _ _ v b hs _ hf ?_ ?_ ?_ (k8_rows_any hB hkind _)
    (k8_ahead_any hB hkind _) c ?_⟩
  · have hr := hse.1
    rw [ho, hr]
    rfl
  · have hr := hse.1
    rw [hr]
    rfl
  · exact k8_cuts hB hps hkind
  · rw [hpl]
    exact hc

/-- **The kind pays at the maker's prover.** -/
theorem k8_kindPays
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K8) ∨
      M.halves A.Z A.G =
        (smallLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id matsO).halves A.Z A.G) :
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K8 := by
  intro g hg hk
  obtain ⟨-, -, -, -, -, -, -, hfirst, -⟩ := atPure_ok hA
  rw [hfirst] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1 hg
  rcases ho M hM with h1 | h1
  · exact absurd hk (h1 g hgM)
  rw [h1] at hgM
  exact k8_sidePays hA h g hgM

end AtFullSide.K8

#print axioms AtFullSide.K8.k8_sidePays
#print axioms AtFullSide.K8.k8_kindPays
