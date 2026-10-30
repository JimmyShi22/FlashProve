-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1LaidHasAMember.lean: the shared "sending" (the kind K1): K1Laid (KindPaysK1AtTheG.lean) IS MET: a value of the kinds' rows that
lays our two lots and the shared chain's two sendings' rows, and nothing else, over the base filling; so kindPays_K1_at_theG is
not empty for want of a K.

  base_names_apart  THE LOTS OF THE BASE FILLING BEAR NAMES THAT ARE APART: by Lean's kernel, on closed strings. overlayLot finds a
                    kind's lot by the lot's NAME: were two names one, no K could lay ours
  k1Rows h          the value: lots := [baseLotS, baseWS] · shared := baseSendings h · second := []
  k1Laid_k1Rows     K1Laid h (k1Rows h)
  kindPays_K1_at_k1Rows   KindPays (theGOfReturn made h T (k1Rows h)) .K1: no premise on K left

Limits. At this K every other kind's place holds the filling's own side beside a simulator that tells nothing: it is a WITNESS that
K1Laid can be met, not the K of record: whoever gathers all kinds' rows lays that one, and owes K1Laid of it. A lot's name is a
String that hangs on no datum. No property of the protocol is claimed.
-/
import AtFullSide.K1.KindPaysK1AtTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Compilation (KindPays)
open OnBytes (TableKey)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.Term
open ProofFile.Honest.K14 (sendingRows simRows ownRows simPub simData randNow simRows_now)
open ProofFile.Honest.K12.AtProof (sharedWithUO halfU halfO)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

set_option maxRecDepth 1000000 in
/-- **The base filling's lots bear names that are apart.** -/
theorem base_names_apart (files : VerifierAndGoals.PublicFiles) : ((baseFilling files).lots.map (·.name)).Nodup := by
  show ((onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots.map
    (·.name)).Nodup
  decide +kernel

/-- In a list whose names are apart, a lot is known by its name. -/
theorem lot_of_name {V W Y : Type} {ls : List (HLot V W Y)} (hn : (ls.map (·.name)).Nodup)
    {L M : HLot V W Y} (hL : L ∈ ls) (hM : M ∈ ls) (e : L.name = M.name) : L = M :=
  List.inj_on_of_nodup_map hn hL hM e

/-- In a list whose images are apart, the search for an entry's image finds that entry. -/
theorem find_of_apart {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ r ∈ l, (l.find? fun x => f x == f r) = some r
  | [], _, _, hr => by cases hr
  | x :: t, hn, r, hr => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hr with rfl | hr
    · exact List.find?_cons_of_pos (by simp)
    · have hne : f x ≠ f r := fun e => hn.1 (e ▸ List.mem_map_of_mem hr)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_of_apart f t hn.2 r hr

theorem baseLotS_mem (files : VerifierAndGoals.PublicFiles) : baseLotS.toHLot ∈ (baseFilling files).lots := by
  rw [show (baseFilling files).lots = _ from
    lots_split_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest]
  exact List.mem_cons_self

theorem baseWS_mem (files : VerifierAndGoals.PublicFiles) : baseWS.toHLot ∈ (baseFilling files).lots := by
  rw [show (baseFilling files).lots = _ from
    lots_split_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)

set_option maxRecDepth 1000000 in
/-- Our two lots' names are apart. -/
theorem two_names_apart : ([baseLotS, baseWS].map (·.name)).Nodup := by decide +kernel

/-- The two sendings' places. -/
theorem sendings_places (h : HeadAtReturn files A) :
    (baseSendings h).map (·.place) = [ProofFile.Honest.K14.sendPlace 2, ProofFile.Honest.K14.sendPlace 5] := rfl

/-- The base filling's shared halves. -/
theorem base_shared (h : HeadAtReturn files A) :
    ∃ rest, (∀ x ∈ rest, x.place.kind = .K12) ∧ (baseFilling files).shared A.Z A.G =
      (simRows (simData A.Z h.places) (simPub A.Z h.places) (matrixInput.weights A.Z)
        (randNow (VerifiableInference.Desc.K1.qAt A.Z h.places)) :
        List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)).map (·.half) ++ rest := by
  have hs := simRows_now (Pb := TableKey) h.head (matrixInput.weights A.Z)
  refine ⟨halfU (matrixInput.weights A.Z)
      (fun w => Bind.ForProver.encW A.Z (matrixInput.weights A.Z w)) A.Z ++
    halfO (matrixInput.weights A.Z) A.Z, ?_, ?_⟩
  rotate_left
  · show sharedWithUO matrixInput A.Z = _
    unfold sharedWithUO
    rw [hs]
    exact List.append_assoc _ _ _
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [AtFullSide.K12.halfU_place _ _ _ x hx]
      rfl
    · rw [AtFullSide.K12.halfO_place _ _ x hx]
      rfl

/-- **The value**: our two lots, the two sendings' rows, nothing else. -/
def k1Rows (h : HeadAtReturn files A) : KindRows (baseFilling files) A.Z A.G where
  lots := [baseLotS, baseWS]
  named := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact List.any_eq_true.2 ⟨_, baseLotS_mem files, beq_self_eq_true _⟩
    · exact List.any_eq_true.2 ⟨_, baseWS_mem files, beq_self_eq_true _⟩
  apart := two_names_apart
  lots_fit := by
    intro L hL s hs
    have hm := List.mem_of_find?_eq_some hs
    have hq := List.find?_some hs
    have hp : s.name = L.name := beq_iff_eq.1 hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [lot_of_name (base_names_apart files) hL (baseLotS_mem files) hp.symm]
      rfl
    · rw [lot_of_name (base_names_apart files) hL (baseWS_mem files) hp.symm]
      rfl
  shared := baseSendings h
  shared_named := by
    intro r hr
    obtain ⟨rest, -, e⟩ := base_shared h
    rw [e]
    exact List.any_eq_true.2 ⟨r.half, List.mem_append_left _
      (List.mem_map_of_mem (List.mem_append_right _ hr)), beq_self_eq_true _⟩
  shared_apart := by
    rw [sendings_places]
    decide
  shared_fit := by
    intro x hx r hs
    have hm := List.mem_of_find?_eq_some hs
    have hq := List.find?_some hs
    have hp : r.place = x.place := beq_iff_eq.1 hq
    have hk : r.place.kind = .K1 := by
      have := List.mem_map_of_mem (f := (·.place)) hm
      rw [sendings_places] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e <;> · rw [e]; rfl
    obtain ⟨rest, hr, e⟩ := base_shared h
    rw [e] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hx
      have hn : ((simRows (simData A.Z h.places) (simPub A.Z h.places) (matrixInput.weights A.Z)
          (randNow (VerifiableInference.Desc.K1.qAt A.Z h.places)) :
          List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)).map (·.place)).Nodup := by
        rw [ProofFile.Honest.K14.simRows_places h.head]
        decide
      rw [List.inj_on_of_nodup_map hn (List.mem_append_right _ hm) hr' hp]
    · exfalso
      rw [hp, hr x hx] at hk
      cases hk
  second := []
  second_named := by intro r hr; cases hr
  second_apart := List.nodup_nil
  second_fit := by intro x _ r hs; cases hs

/-- **K1Laid is met.** -/
theorem k1Laid_k1Rows (h : HeadAtReturn files A) : K1Laid h (k1Rows h) where
  lot := find_of_apart (·.name) [baseLotS, baseWS] two_names_apart baseLotS List.mem_cons_self
  w := find_of_apart (·.name) [baseLotS, baseWS] two_names_apart baseWS
    (List.mem_cons_of_mem _ List.mem_cons_self)
  shared := fun r hr => find_of_apart (·.place) (baseSendings h)
    (by rw [sendings_places]; decide) r hr

/-- **KindPays at the named sides, at this K: no premise on K left.** -/
theorem kindPays_K1_at_k1Rows (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) :
    KindPays (theGOfReturn made h T (k1Rows h)) .K1 :=
  kindPays_K1_at_theG hS hL made h T (k1Rows h) (k1Laid_k1Rows h)

end AtFullSide.K1

#print axioms AtFullSide.K1.base_names_apart
#print axioms AtFullSide.K1.lot_of_name
#print axioms AtFullSide.K1.find_of_apart
#print axioms AtFullSide.K1.two_names_apart
#print axioms AtFullSide.K1.base_shared
#print axioms AtFullSide.K1.k1Rows
#print axioms AtFullSide.K1.k1Laid_k1Rows
#print axioms AtFullSide.K1.kindPays_K1_at_k1Rows
