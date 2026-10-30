-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03DigPartsAt.lean: THE LOOKUP ARGUMENTS ON THE DIGITS: THREE SORTS OF PREMISES OF THE
LOOKUPS' AUTHORS' JOIN INTO hForms (`hForms_dig_mgAll`,
Johnson/Desc/Sound/MgAt/K3DigitsFormsJoin.lean [not imported here]), PAID AT THE CLOSED CONSTANT
UNDER THE HEAD `AtMgA` ALONE, AT ALL 25 SEGMENTS. That file's cone is not needed for these.
  **`k03_ns_pos_dig`** (its hpos): the place's number of slots is positive: by the entry test's row
    on the digits (`K3Asks.digRow`, from the head: `k03_digRow_at`): its clause "x.F.next +
    Forest.elems tl.f9 ≤ x.ns", and `Forest.elems` has the summand 1 + 2 * d + 5.
  `k03_sFvFits_lay`, **`k03_sFvFits_dig`** (its hfits): at a state in front of the digits' lookup
    that is on the promise, reached and without a mark (the first: reached alone) the test
    `sFvFitsB` accepts: at a layers' segment: the merge's slot lies below the ledger's next slot
    (`mergeBelow_reach`); at attention's and at the head's: the merge has no slot
    (`k03_merge_none_att_digits`, `k03_merge_none_head_digits`).
  `k03_ix_dig`, **`k03_finds_dig`** (its lk, hlk, hrawO, hrawG, hfO, hfG): ONE link of the
    description for the four finds: by `k03_objects_raw`, `k03_guests_raw`
    (Johnson/Desc/First/Look/K03StatesRaw.lean: the driver's guard around these runs is idle).

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03MergeAll
import Johnson.P5J.K03TestsAt
import Johnson.P5J.K03ObjTerms
import Johnson.Desc.First.Look.K03StatesRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.First.Look (Place lookAt)
open VerifiableInference.Desc.K9 (mergeOf statesOfLink)
open Johnson.Desc.First.Walk.Tied (reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **The digits' place's number of slots is positive.** -/
theorem k03_ns_pos_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {y : Place} (hy : lookAt (At.X Zp) l true = some y) : 0 < y.ns := by
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have hd := k03_digRow_at h.toAtMg
  unfold VerifiableInference.Desc.K3Asks.digRow at hd
  have hlen : VerifiableInference.Desc.K3Asks.linksOf (At.X Zp) = 25 := by
    unfold VerifiableInference.Desc.K3Asks.linksOf
    rw [if_pos hp4, hN]
  rw [hlen] at hd
  have h1 := List.all_eq_true.1 hd l (List.mem_range.2 hl)
  obtain ⟨xt, hxt, hB⟩ := (Option.any_eq_true _ _).1 h1
  unfold VerifiableInference.Desc.K3Asks.digAt at hxt
  obtain ⟨y', hy', hxt⟩ := Option.bind_eq_some_iff.1 hxt
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  obtain ⟨tl', -, hxt⟩ := Option.bind_eq_some_iff.1 hxt
  obtain ⟨h', -, rfl⟩ := Option.map_eq_some_iff.1 hxt
  unfold VerifiableInference.Desc.K3Asks.digB VerifiableInference.Desc.K3Asks.digAddrB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
  have hle : y'.F.next + Forest.elems h' ≤ y'.ns := hB.2.1.2
  have he : 0 < Forest.elems h' := by
    unfold Forest.elems
    omega
  omega

/-- In front of a layers' segment's digits' lookup the test accepts. -/
theorem k03_sFvFits_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (z : ProofFile.InstPub) (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hr : h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2)) :
    VerifiableInference.Desc.K3.sFvFitsB u.1 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' := reach_raw (h.toAtMg.rch_is_reach _ _ hr)
  rw [digits_number g hg] at hr'
  exact sFvFits_of_below
    (OnBytes.Road.K4.mergeBelow_reach h.scope h.reads O h.laid.planOk hg (by omega : 3 < 4) hr')

/-- **In front of every digits' lookup the test accepts.** -/
theorem k03_sFvFits_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (z : ProofFile.InstPub) (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hu : onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l true) u)
    (hr : h.toAtMg.rch (k3K l true) ((z, u.1), u.2)) (hun : u.1.failed = none) :
    VerifiableInference.Desc.K3.sFvFitsB u.1 = true := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.mod_two_eq_zero_or_one l with he | ho
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      exact k03_sFvFits_lay h (by omega) z u hr
    · exact VerifiableInference.Desc.K3.sFvFits_none
        (k03_merge_none_att_digits h l h24 ho z u hu hun)
  · obtain rfl : l = 24 := by omega
    exact VerifiableInference.Desc.K3.sFvFits_none
      (k03_merge_none_head_digits h ((z, u.1), u.2) hr.1 hun)

/-- The two lookups' numbers in their link. -/
theorem k03_ix_dig {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) :
    IM.k3Ix l false = 1 + shift sub ∧ IM.k3Ix l true = 6 + shift sub := by
  obtain ⟨sub', hsub', h2, h3⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have e2 : IM.k3Ix l false + 1 = 2 + shift sub' := h2
  have e3 : IM.k3Ix l true + 1 = 7 + shift sub' := h3
  omega

/-- **ONE LINK FOR THE FOUR FINDS.** -/
theorem k03_finds_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) :
    ∃ lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim,
      (h.toAtMg.𝔇 h.𝔇).lk l = some lk ∧
      (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "objects") =
        some ("objects", objectsRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm)) ∧
      (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "guests") =
        some ("guests", guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest
          VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim))) ∧
      (statesOfLink lk (6 + shift sub)).find? (fun y => y.1 == "objects") =
        some ("objects", objectsRun (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm)) ∧
      (statesOfLink lk (6 + shift sub)).find? (fun y => y.1 == "guests") =
        some ("guests", guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest
          VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim))) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨e1, e6⟩ := k03_ix_dig hl hsub
  obtain ⟨lk, hk, o1⟩ := k03_objects_raw h.scope h.reads O l hl false
  obtain ⟨lk₂, hk₂, g1⟩ := k03_guests_raw h.scope h.reads O l hl false
  obtain ⟨lk₃, hk₃, o6⟩ := k03_objects_raw h.scope h.reads O l hl true
  obtain ⟨lk₄, hk₄, g6⟩ := k03_guests_raw h.scope h.reads O l hl true
  obtain rfl : lk = lk₂ := Option.some.inj (hk.symm.trans hk₂)
  obtain rfl : lk = lk₃ := Option.some.inj (hk.symm.trans hk₃)
  obtain rfl : lk = lk₄ := Option.some.inj (hk.symm.trans hk₄)
  rw [e1] at o1 g1
  rw [e6] at o6 g6
  exact ⟨lk, (h.laid.linkAt l).trans hk, o1, g1, o6, g6⟩

end P5J

#print axioms P5J.k03_ns_pos_dig
#print axioms P5J.k03_sFvFits_lay
#print axioms P5J.k03_sFvFits_dig
#print axioms P5J.k03_ix_dig
#print axioms P5J.k03_finds_dig
