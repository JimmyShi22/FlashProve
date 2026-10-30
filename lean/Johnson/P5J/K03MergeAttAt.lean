-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03MergeAttAt.lean: THE LOOKUP ARGUMENT ON THE DIGITS AT THE TWELVE ATTENTION's
SEGMENTS: THE NAMED FACT hmerge ("no heard row names the slot of the merge's end value": the premise
of the lookups' authors' `objects_formsIn`), IN ITS OWN TEXT, AT THE STATE BEHIND AN ACCEPT, AT THE
CLOSED CONSTANT, UNDER THE HEAD `AtMgA`, A VALUE OF `Free` AND ITS THREE EQUATIONS. IT HOLDS THERE
BECAUSE THE MERGE HAS NO SLOT; AND
THAT IS SAID BY THE TABLE's OWN PROMISE IN FRONT: NO FACT ON REACHED STATES IS SPENT.
  `k03_mergeAt_digits_of`: at every segment l < 24: hmerge behind the digits' lookup FROM the
    lookups' authors' test `sFvFitsB` at the state in front. The proof of `k03_mergeAt_digits_lay`
    (Johnson/P5J/K03MergeAt.lean) without its step on reached states, general in the segment's sort.
  `merge_none_of_heard5`: where an attention's own rounds are heard, the part is an attention's: so
    the merge has no slot (`mergeOf_none`, Johnson/Top/H/Keep/PlanesSlotsIn.lean).
  `k03_merge_none_att_digits`: on the promise in front of the digits' lookup of an attention's
    segment, at a state without a mark: the public item "K5.okAt" is asked there (`digits_sorted`,
    Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean: by the kernel) and its test reads what these rounds
    heard (`okThereB_iff`, Johnson/Desc/First/Att/Door/Law/OkThereTie.lean).
  **`k03_mergeAt_digits_att`**: THE FACT.

Limits. At these twelve places the fact asks nothing at the honest run (the merge has no slot): it
is wanted for the form's sake. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone.
Nothing on soundness.

-/
import Johnson.P5J.K03MergeAt
import Johnson.Desc.Sound.MgAt.K3DigitsSorted
import Johnson.Desc.First.Att.Door.Law.OkThereTie
import Johnson.Top.H.Keep.PlanesSlotsIn

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
open VerifiableInference.Desc.First (ModelPart shift pubAll_more_okAt)
open VerifiableInference.Desc.First.Look (digAt lookAt k3LookIn_onIn)
open VerifiableInference.Desc.K9 (mergeOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **hmerge behind the digits' lookup of a segment l < 24, from the test in front.** -/
theorem k03_mergeAt_digits_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ l < 24, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true) u →
      u.1.failed = none → VerifiableInference.Desc.K3.sFvFitsB u.1 = true →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ G, (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard v.1 = some G →
        ∀ f ∈ G.rows.toList, ∀ t ∈ f.slots.toList, mergeOf v.1 ≠ some t.1 := by
  intro l h24 y tl hy q hq b' hb' B' hB z u v hu hun hfit ⟨τ, hout⟩
  have hl : l < 25 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l true b' hb'
  obtain ⟨sub, hsub, -, hpcT⟩ := K3Lot.k03_sub_full l hl
  have hlook : lookAt (At.X Zp) l true = some y := by
    unfold digAt at hy
    obtain ⟨x', h1, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨tl', -, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨h', -, hy⟩ := Option.map_eq_some_iff.1 hy
    obtain rfl : x' = y := congrArg Prod.fst hy
    exact h1
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below (strictAt B' q) B' rfl
    (K.back l hl true q hq) u τ v hout
  have hd := hB.1.2 _ _ _ _ hd0
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ := theStated_yes_digits K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place l true) b'
    hb' (K.planOk l hl true b' hb') l rfl hpc u.1 v.1 _ cols hd
  have hOpen := digits_lookIn_open (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS
    (k3K l true) (IM.k3Place l true) l sub
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
    (.lookIn l (7 + shift sub)) (by simp)
  have hp := onQ_front hu hun _ (List.mem_append_left _ hOpen)
  rw [hpcT.symm.trans hpc] at hp
  have hIn := k3LookIn_onIn (fLook_at (k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) l true hlook z u.1 hp)
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  have key := k3_digits_hmerge (hd := hyes) (hF := hF) (hS := hS) (h := hfit)
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact key
  · have hh : VerifiableInference.Desc.K3.isHead (At.X Zp) l = false := by
      unfold VerifiableInference.Desc.K3.isHead
      rw [if_pos hp4, hN]
      exact beq_eq_false_iff_ne.2 (by omega)
    obtain ⟨used, claims, rfl⟩ := quietAt_digits_is hh hf
    unfold VerifiableInference.Desc.K3.quietDigits at hfs
    obtain ⟨F2, -, hfs⟩ := k03_bind_ok hfs
    obtain ⟨G2, -, hfs⟩ := k03_bind_ok hfs
    have ev : s'.putFork G2 = v.1 := Except.ok.inj hfs
    have e1 : mergeOf (s'.putFork G2) = mergeOf s' := mergeOf_putFork s' G2
    have e2 : (s'.putFork G2).tl? = s'.tl? := tl_putFork s' G2
    intro G0 hG0 f0 hf0 t ht
    rw [← ev] at hG0 ⊢
    have hG1 : (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard s' = some G0 := by
      have hG0' : (s'.putFork G2).tl?.bind (·.heard) = some G0 := hG0
      rw [e2] at hG0'
      exact hG0'
    rw [e1]
    exact key G0 hG1 f0 hf0 t ht

/-- Where an attention's own rounds are heard the merge has no slot. -/
theorem merge_none_of_heard5 {s : VerifiableInference.Desc.First.S}
    {w : VerifiableInference.Desc.First.Att.P.Heard} (e : s.heard5? = some w) :
    mergeOf s = none := by
  refine mergeOf_none (fun a ha => ?_) (fun a ha => ?_) <;>
    · unfold VerifiableInference.Desc.First.S.heard5? at e
      rw [ha] at e
      cases e

/-- **On the promise in front of an attention's digits' lookup the merge has no slot.** -/
theorem k03_merge_none_att_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ l < 24, l % 2 = 1 → ∀ (z : ProofFile.InstPub)
      (u : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true) u →
      u.1.failed = none → mergeOf u.1 = none := by
  intro l h24 ho z u hu hun
  have hsub := links_att l h24 ho
  have eM : (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more = mgMore :=
    mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl
  have hfront := onQ_front hu hun
  rw [eM] at hfront
  have hk := (digits_sorted (by omega : l < 25) hsub).2 (.more (some l) "K5.okAt")
    (by simp [keptDigits])
  have hp := hfront _ hk
  have hAtt : (h.toAtMg.𝔇 h.𝔇).pubD.d5.isAtt l = true := by
    show ((h.toAtMg.𝔇 h.𝔇).links[l]? == some ModelPart.attention) = true
    have hlinks : (h.toAtMg.𝔇 h.𝔇).links = linksFull := rfl
    rw [hlinks, hsub]
    rfl
  rw [mgAll_pub, pubAll_more_okAt _ _ l hAtt] at hp
  obtain ⟨p, -, hp⟩ := (Option.any_eq_true _ _).1 hp
  obtain ⟨U, w, -, e5, -⟩ := (H2K5.Door.okThereB_iff _ _).1 hp
  exact merge_none_of_heard5 e5

/-- **hmerge BEHIND THE DIGITS' LOOKUP AT THE TWELVE ATTENTION's SEGMENTS, AT THE CONSTANT.** -/
theorem k03_mergeAt_digits_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ l < 24, l % 2 = 1 → ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ G, (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard v.1 = some G →
        ∀ f ∈ G.rows.toList, ∀ t ∈ f.slots.toList, mergeOf v.1 ≠ some t.1 :=
  fun l h24 ho y tl hy q hq b' hb' B' hB z u v hu _ hun hout =>
    k03_mergeAt_digits_of h 𝔏 q₁ q₂ q₃ l h24 y tl hy q hq b' hb' B' hB z u v hu hun
      (VerifiableInference.Desc.K3.sFvFits_none (k03_merge_none_att_digits h l h24 ho z u hu hun))
      hout

end P5J

#print axioms P5J.k03_mergeAt_digits_of
#print axioms P5J.merge_none_of_heard5
#print axioms P5J.k03_merge_none_att_digits
#print axioms P5J.k03_mergeAt_digits_att
