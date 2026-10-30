-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelEnd.lean: THE END OF THE SKELETONS' LAWS: four of the seven
steps of `ProofFile.onlineDescriptionFromPublicPart`'s back (no fault; nothing lacking; the blocks at the places; the first
chain) FROM FOUR CLOSED FACTS ON SKELETONS. Statements and proofs.
  `toldFrom_zip`: `toldFrom` is "the non-empty members, each with its number" in the words of
    Johnson/Desc/Ok/PlanWritten/CutTest.lean's `toldRounds`
  `Skel.row`: the six fields that a row of that file's `cutOf` holds
  `base_of_lacking`   T18: where nothing is lacking, `PureParts.base` returns
  `back_of_skel`      T19
The premises of `back_of_skel`. hB: the base's blocks are the lots' (`baseOf`'s own text). hk: the
lots' skeletons are ks: one row a lot. hS: `Steady` at every lot: by `steady_none` it holds of a lot
that supplies no batching. c₂ c₃ c₄ c₅: closed facts: they name the places, the shape, the places of
the batchings, the segments' sorts, ks, and of the two later seats the name and `standIns`: no
block, no function of a block, none of the segments' records.
Limits. NO PREMISE IS PAID HERE. Whether Lean's kernel bears c₂ … c₅ at the real lists is not asked.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem toldFrom_zip (l : List (List Oracle)) :
    ∀ k, ((l.zipIdx k).filter fun x => !x.1.isEmpty).map (fun x => (x.2, x.1)) = toldFrom k l := by
  induction l with
  | nil => intro k; rfl
  | cons a l ih =>
    intro k
    rw [List.zipIdx_cons, toldFrom]
    cases h : a.isEmpty with
    | true =>
      rw [List.filter_cons_of_neg (by simp [h]), ih]
      simp
    | false =>
      rw [List.filter_cons_of_pos (by simp [h]), List.map_cons, ih]
      simp

/-- The six fields of a row of `cutOf`. -/
def Skel.row (k : Skel) :
    String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat) :=
  (k.name, k.place, k.nRounds, k.nOracles, k.told, k.before)

/-- A lot that supplies no batching is steady. -/
theorem steady_none (G : Ground) (L : Lot) (h : ∀ a, L.batch G a = none) : Steady G L := by
  intro a mk e
  rw [h a] at e
  cases e

theorem mapM_returns {α β : Type} (f : α → Except String β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := mapM_returns f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl⟩

/-- **T18. Where nothing is lacking, the blocks at the places are all there.** -/
theorem base_of_lacking (T : PureSeat) (P : PureParts) (h : lackingAt T P = []) :
    ∃ base, P.base = .ok base := by
  unfold lackingAt at h
  dsimp only at h
  have h1 := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
    (List.append_eq_nil_iff.1 h).1).1).1
  refine mapM_returns _ _ fun x hx => ?_
  have h2 := List.filterMap_eq_nil_iff.1 h1 x hx
  cases e : x.2 with
  | ok b => exact ⟨b, rfl⟩
  | error w =>
    rw [e] at h2
    cases h2

/-- **T19. Four steps of `onlineDescriptionFromPublicPart`'s back, from four closed facts on skeletons.** -/
theorem back_of_skel (Z : Pub) (T : PureSeat) (B : PureBase) (ks : List LotSk)
    (bl fl : List Skel)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hk : T.lots.map (lotSk B.G₀) = ks)
    (hS : ∀ L ∈ T.lots, Steady B.G₀ L)
    (c₂ : faultsSk B.spots B.shape B.batchAt ks = [])
    (c₃ : lackingSk (placesSk B.spots ks) ((framesSk B.shape ks).map (·.1))
      (onRoadSk B.batchAt ks) (eachAtSk B.spots ks) (testsAtSk B.spots ks)
      (T.shared.map fun A => (A.lot, A.standIns)) (T.second.map fun A => (A.lot, A.standIns)) = [])
    (c₄ : ((placesSk B.spots ks).mapM fun x => x.2) = .ok bl)
    (c₅ : chainBySk (subsOf Z) bl (framesSk B.shape ks) (roadSk B.spots ks) = .ok fl) :
    faultsAt T B = [] ∧ lackingAt T (partsAt T B) = [] ∧
      ∃ base, (partsAt T B).base = .ok base ∧ base.map skel = bl ∧
        ∃ c, chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
          c.blocksInOrder.map skel = fl := by
  subst hk
  have hr : (partsAt T B).frames.map (·.1) =
      (framesSk B.shape (T.lots.map (lotSk B.G₀))).map (·.1) := by
    rw [← frames_skel T B hB, List.map_map]
    rfl
  refine ⟨by rw [faultsAt_skel T B hB, c₂], ?_, ?_⟩
  · rw [lackingAt_skel, places_skel T B hB, hr, onRoad_skel, eachAt_skel, testsAt_skel, c₃]
  · have h4 := base_skel (partsAt T B)
    rw [places_skel T B hB, c₄] at h4
    cases e : (partsAt T B).base with
    | error w =>
      rw [e] at h4
      cases h4
    | ok base =>
      rw [e] at h4
      have hb : base.map skel = bl := Except.ok.inj h4
      have h5 := chainBy_skel Z base (partsAt T B).frames (partsAt T B).road _
        (road_skel T B hS)
      rw [hb, frames_skel T B hB, c₅] at h5
      refine ⟨base, rfl, hb, ?_⟩
      cases e5 : chainBy Z base (partsAt T B).frames (partsAt T B).road with
      | error w =>
        rw [e5] at h5
        cases h5
      | ok c =>
        rw [e5] at h5
        exact ⟨c, rfl, Except.ok.inj h5⟩

end ProofFile.Sk

#print axioms ProofFile.Sk.toldFrom_zip
#print axioms ProofFile.Sk.steady_none
#print axioms ProofFile.Sk.mapM_returns
#print axioms ProofFile.Sk.base_of_lacking
#print axioms ProofFile.Sk.back_of_skel
