-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MergeHeadDigitsAt.lean: THE LOOKUP ARGUMENT ON THE DIGITS AT THE OUTPUT HEAD's
SEGMENT: THE NAMED FACT hmerge ("no heard row names the slot of the merge's end value"), IN ITS OWN
TEXT, AT THE STATE BEHIND AN ACCEPT, AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA` AND ONE NAMED
PREMISE.
  hNo, THE PREMISE (other files' to show): at a state that is reached at border 345 of the first
    chain (in front of the head's digits' lookup) and bears no mark, the merge has no slot: the
    merge runs behind that lookup. In the form other files give it, at the constant's description.
  `quietAt_head_is`: at the head's segment the step without a round behind the digits' lookup is
    `K3.quietHead` (it lays the claim on the weights alone: `quietHead_ok`,
    Johnson/Desc/First/Look/K3QuietLaws.lean).
  **`k03_mergeAt_digits_head`**: THE FACT: the proof of `k03_mergeAt_digits_of`
    (Johnson/P5J/K03MergeAttAt.lean) at l := 24, past that other quiet step.

Limits. hNo is a premise: not shown here. At this place the fact asks nothing at the honest run. The
head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03MergeAttAt
import Johnson.Desc.First.Look.K3QuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt lookAt k3LookIn_onIn)
open VerifiableInference.Desc.K9 (mergeOf)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- At the head's segment the step without a round behind the digits' lookup. -/
theorem quietAt_head_is {X : Verify.Public} {i : ℕ}
    (hh : VerifiableInference.Desc.K3.isHead X i = true)
    {f : VerifiableInference.Desc.First.S → Except String VerifiableInference.Desc.First.S}
    (hf : VerifiableInference.Desc.K3.quietAt X i true = some f) :
    f = VerifiableInference.Desc.K3.quietHead X := by
  unfold VerifiableInference.Desc.K3.quietAt at hf
  simp only [if_true] at hf
  rw [if_pos hh] at hf
  exact (Option.some.inj hf).symm

set_option maxHeartbeats 4000000 in
/-- **hmerge BEHIND THE DIGITS' LOOKUP AT THE OUTPUT HEAD's SEGMENT, AT THE CONSTANT.** -/
theorem k03_mergeAt_digits_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hNo : ∀ a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) × (FrD).E.Str,
      RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 345 a → a.1.2.failed = none → mergeOf a.1.2 = none) :
    ∀ y tl, digAt (At.X Zp) 24 = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ G, (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard v.1 = some G →
        ∀ f ∈ G.rows.toList, ∀ t ∈ f.slots.toList, mergeOf v.1 ≠ some t.1 := by
  intro y tl hy q hq b' hb' B' hB z u v hu hr hun ⟨τ, hout⟩
  have hl : 24 < 25 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape 24 true b' hb'
  obtain ⟨sub, hsub, -, hpcT⟩ := K3Lot.k03_sub_full 24 hl
  have hlook : lookAt (At.X Zp) 24 true = some y := by
    unfold digAt at hy
    obtain ⟨x', h1, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨tl', -, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨h', -, hy⟩ := Option.map_eq_some_iff.1 hy
    obtain rfl : x' = y := congrArg Prod.fst hy
    exact h1
  have hfit : VerifiableInference.Desc.K3.sFvFitsB u.1 = true :=
    VerifiableInference.Desc.K3.sFvFits_none (hNo ((z, u.1), u.2) hr.1 hun)
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below (strictAt B' q) B' rfl
    (K.back 24 hl true q hq) u τ v hout
  have hd := hB.1.2 _ _ _ _ hd0
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ := theStated_yes_digits K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b'
    hb' (K.planOk 24 hl true b' hb') 24 rfl hpc u.1 v.1 _ cols hd
  have hOpen := digits_lookIn_open (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS
    (k3K 24 true) (IM.k3Place 24 true) 24 sub
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (K3Lot.k03_at_full 24 hl true) rfl hsub hpcT
    (.lookIn 24 (7 + shift sub)) (by simp)
  have hp := onQ_front hu hun _ (List.mem_append_left _ hOpen)
  rw [hpcT.symm.trans hpc] at hp
  have hIn := k3LookIn_onIn (fLook_at (k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) 24 true hlook z u.1 hp)
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  have key := k3_digits_hmerge (hd := hyes) (hF := hF) (hS := hS) (h := hfit)
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact key
  · have hh : VerifiableInference.Desc.K3.isHead (At.X Zp) 24 = true := by
      unfold VerifiableInference.Desc.K3.isHead
      rw [if_pos hp4, hN]
      rfl
    obtain rfl := quietAt_head_is hh hf
    obtain ⟨a, c, ha, ho, ev⟩ := VerifiableInference.Desc.K3.quietHead_ok (At.X Zp) s' v.1 hfs
    have e1 : mergeOf v.1 = mergeOf s' := by
      rw [ev]
      simp [mergeOf, ha]
    have e2 : v.1.tl? = s'.tl? := by
      rw [ev]
      simp [VerifiableInference.Desc.First.S.tl?, ha]
    intro G0 hG0 f0 hf0 t ht
    have hG1 : (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard s' = some G0 := by
      have hG0' : v.1.tl?.bind (·.heard) = some G0 := hG0
      rw [e2] at hG0'
      exact hG0'
    rw [e1]
    exact key G0 hG1 f0 hf0 t ht

end P5J

#print axioms P5J.quietAt_head_is
#print axioms P5J.k03_mergeAt_digits_head
