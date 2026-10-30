-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RidesDigAt.lean: THE KIND "LOOKUP" (K3): WHAT RIDES PAST THE LOOKUP ON A SEGMENT's
DIGITS, AT THE TWELVE LAYERS' SEGMENTS, AT THE CLOSED CONSTANT, FROM ONE PREMISE ON THE STATES
(hOwn) WHICH IS NOT SHOWN HERE: UNTIL IT HAS A PAYER THE ROW BUYS NOTHING.
(Where this and lean/THEOREM.md differ, the page
holds.) The end is the field
rides of `DigLastR` (Johnson/P5J/K03Last.lean) there, by one call of another author's
`ridesAtR_digits_layers` (Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean). Two closed tests with code
and seven theorems: four by the kernel (two of them negative tests), the others joinings.
  `k3DigPinIB`, `k3DigPinI_full`, `k3DigPinI_control`: the item "the index masks' message is
    pinned" is open at the digits' border of each of the 25 segments: by the kernel; at the
    chain's start it is not.
  `linksLayFullB`, `linksLayFull`, `linksLayFull_control`: the even segments below 24 of the
    written list are layers' segments; segment 1 is not.
  `k03_pieceAt_dig`: in the goals' scope the digits' piece of segment l, by the kind's own text,
    is the written place's. `k03_index_low_dig`: the tree of the index masks' message lies below
    the piece's base.
  `k03_rides_dig_layers`: the field.
What is paid. The terms of the parameters; the place; the piece's facts; the value and its test on
the plan; ONE LINK Lk of the head's own chain for the readers and for both finds (another author's
`k03_objects_raw`, `k03_guests_raw`, Johnson/Desc/First/Look/K03StatesRaw.lean: the driver's guard
around these runs is idle, so what the link states IS the run); the second hole's silence (the
holes' own text off the head's segment); the table's fences' test (`k03_fence_at`,
Johnson/P5J/K03TestsAt.lean).
WHAT STAYS IN FRONT: ONE PREMISE ON THE STATES, IN THAT AUTHOR's OWN TEXT: hOwn: under both
promises, "reached", no mark and an accept of the sub-protocol: the readers of the calling kind's
two runs "front" and "back" (block 2 of the link) answer behind what they answered in front. NO
PAYER IS KNOWN: a search by the statement's end found none.
(Where this and lean/THEOREM.md differ, the
page holds.) By that author's `link_fwd`
(Johnson/Top/H/Keep/FormsPassK3.lean) it falls to `RunSame` at the two runs that the link states
there: a law on the calling kind's own texts. (The promise behind is a hypothesis of the field
rides itself: hOwn is handed no more than the field is.) And that `digAt` answers at the segment:
a binder on public data: it gives the place and its shape. "What the link's first hole answered in
front it answers behind" is paid by that author's `k3_digits_step_smallReader`
(Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean).
Limits: joinings. The head h and the free letters' three equations are premises. THE OTHER
THIRTEEN DIGITS' PLACES (attention's twelve segments and the output head's) ARE NOT TOUCHED. The
full size alone. No soundness is claimed.

-/
import Johnson.P5J.K03RidesAt
import Johnson.P5J.K03TestsAt
import Johnson.P5J.K03ObjTerms
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Desc.Sound.MgAt.K3DigitsFormsSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item ModelPart openSets start sampledIn)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K9 (holesAt smallReader)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The index masks' pin is open at the digits' border of every segment. -/
def k3DigPinIB : Bool :=
  (List.range 25).all fun l =>
    ((openSets linksFull PS (start linksFull))[k3K l true]?.getD []).contains Item.pinI

set_option maxRecDepth 1000000 in
theorem k3DigPinI_full : k3DigPinIB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the same list at the chain's start has it not. -/
theorem k3DigPinI_control :
    ((openSets linksFull PS (start linksFull))[0]?.getD []).contains Item.pinI = false := by
  decide +kernel

/-- The even segments below 24 of the written list are layers' segments. -/
def linksLayFullB : Bool := (List.range 12).all fun g => linksFull[2 * g]? == some ModelPart.layers

theorem linksLayFull : linksLayFullB = true := by decide +kernel

/-- **A negative test.** -/
theorem linksLayFull_control : (linksFull[1]? == some ModelPart.layers) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- In scope the digits' piece, by the kind's own text, is the written place's. -/
theorem k03_pieceAt_dig (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (l : ℕ) :
    (IM.k3Place l true).piece = VerifiableInference.Desc.K3.pieceAt (At.X Zp) l true := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
  rw [p4, ng]
  by_cases e : l = 24
  · subst e
    rfl
  · simp [IM.k3Place, IM.k3Ix, e]

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- The index masks' tree lies below the piece's base. -/
theorem k03_index_low_dig {l : ℕ} (hl : l < 25) (q)
    (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q) : (At.N Zp cF).index.1 < q.base := by
  refine k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF)
    (k03_fence_at h.toAtMg) l hl true q hq _ ?_
  have h0 := List.all_eq_true.1 k3DigPinI_full l (List.mem_range.2 hl)
  have hm : Item.pinI ∈ (openSets linksFull PS (start linksFull))[k3K l true]?.getD [] := by
    simpa using h0
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨.pinI, hm, List.mem_singleton.2 rfl⟩

/-- **THE FIELD rides AT THE TWELVE LAYERS' DIGITS, AT THE CONSTANT.** -/
theorem k03_rides_dig_layers : ∀ l < 24, l % 2 = 0 → ∀ y tl,
    VerifiableInference.Desc.First.Look.digAt (At.X Zp) l = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd l) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K l true) q b' := by
  intro l hl24 he y tl hdig q hq b' hb' hOwn
  have hl : l < 25 := by omega
  obtain ⟨hs, hx, hsh⟩ : ∃ hs, lookAt (At.X Zp) l true = some y ∧
      (VerifiableInference.Desc.First.Look.P.ofPlace
        (OnBytes.Params.settingOf (At.X Zp).P.frame) true y).shape = some hs := by
    unfold VerifiableInference.Desc.First.Look.digAt at hdig
    obtain ⟨x', hx', hd1⟩ := Option.bind_eq_some_iff.1 hdig
    obtain ⟨tl', -, hd2⟩ := Option.bind_eq_some_iff.1 hd1
    obtain ⟨s, hs', hd3⟩ := Option.map_eq_some_iff.1 hd2
    obtain ⟨rfl, -⟩ := Prod.mk.inj hd3
    exact ⟨s, hx', hs'⟩
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hback := Pc.back l hl true q hq
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[l]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull (l / 2) (List.mem_range.2 (by omega))
    rw [show 2 * (l / 2) = l by omega] at h0
    simpa using h0
  have hix : IM.k3Ix l false = 1 := by
    unfold IM.k3Ix
    simp [show l ≠ 24 by omega]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, hLk, hO⟩ := k03_objects_raw h.scope h.reads O l hl false
  obtain ⟨Lk', hLk', hG⟩ := k03_guests_raw h.scope h.reads O l hl false
  obtain rfl : Lk = Lk' := Option.some.inj (hLk.symm.trans hLk')
  rw [hix] at hO hG
  have hsil : ∀ (n : String) (s : VerifiableInference.Desc.First.S),
      (holesAt (At.X Zp) (headLink (At.X Zp)) l Lk).silent 1 n s = none := by
    intro n s
    unfold holesAt
    rw [h24]
    simp [show l ≠ 24 by omega]
  exact ridesAtR_digits_layers (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch
    (holesAt (At.X Zp) (headLink (At.X Zp)) l Lk) Lk K3Lot.ofForm (K3Lot.readersAt (At.X Zp))
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hb' (Pc.planOk l hl true b' hb') rfl
    (k03_pieceAt_dig h.toAtMg l) rfl rfl hl hsub (k03_hlink h l Lk hLk) k03_atS2_calls
    (At.seats Zp) (k03_es h) (k03_hD h) (k03_hd h) q (K3Lot.k03_at_full l hl true) rfl
    (by
      show 7 ≤ (if (true : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
      simp)
    hback hx hsh (k03_index_low_dig h 𝔏 q₁ q₂ q₃ hl q hq) (fun _ _ _ _ => rfl)
    (k03_hHeadAll h q.base)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hO.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hG.symm.trans e))).2.symm)
    (fun _ u _ _ _ _ _ _ => hsil "objects" u.1) (fun _ u _ _ _ _ _ _ => hsil "guests" u.1)
    hOwn
    (fun _ u v _ _ _ _ hst R hR => by
      obtain ⟨rs, gs, hd⟩ := hst
      show smallReader v.1 = some R
      rw [k3_digits_step_smallReader K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
        Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hb' (Pc.planOk l hl true b' hb') l rfl
        (k03_pieceAt_dig h.toAtMg l) u.1 v.1 rs gs hd]
      exact hR)

end

end P5J

#print axioms P5J.k3DigPinI_full
#print axioms P5J.k3DigPinI_control
#print axioms P5J.linksLayFull
#print axioms P5J.linksLayFull_control
#print axioms P5J.k03_pieceAt_dig
#print axioms P5J.k03_index_low_dig
#print axioms P5J.k03_rides_dig_layers
