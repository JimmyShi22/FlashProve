-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03MergeAt.lean: THE LOOKUP ARGUMENT ON THE DIGITS AT THE TWELVE LAYERS' SEGMENTS:
THE NAMED FACT hmerge ("no heard row names the slot of the merge's end value": the premise of the
lookup's files' `objects_formsIn`, Johnson/Top/H/Keep/FormsInObjects.lean), IN ITS OWN TEXT, AT
THE STATE BEHIND AN ACCEPT, AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`, A VALUE OF `Free` AND
ITS THREE EQUATIONS. These are the
places at which the merge has a slot, so that the fact asks something.

A JOIN OF THEOREMS FROM THREE OTHER FOLDERS.
  (α) in front, on reached states: the merge's slot lies below the open ledger's next slot:
    `mergeBelow_reach` (Johnson/Road/K4/MergeBelowReached.lean), at "reached" := `AtMg.rch`.
  (β) at the accept: the heard rows name no slot below that next slot: `k3_digits_hmerge`
    (Johnson/Top/H/Keep/MergeApart.lean), from the test `sFvFitsB` in front.
  The accept of the stated sub-protocol is a yes of the lookup's own decision and then a step
    without a round: `theStated_yes_digits` (Johnson/Desc/First/Look/K3DigitsSeatedYes.lean).
HERE: `sFvFits_of_below` ((α)'s sentence gives (β)'s test) · `quietAt_digits_is` (outside the head's
segment that step is `K3.quietDigits`: it writes the ledger alone: past it by the lookup's files'
`mergeOf_putFork` and `tl_putFork`) · `digits_number` (the border's
number) · **`k03_mergeAt_digits_lay`**.

NOT HERE: the digits' lookups at attention's segments and at the output head's: there the merge has
no slot at the honest run; that it has none at every reached state is not shown here.
Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At
OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OthersPubAt
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Desc.First.Look.K3DigitsTies
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.Sound.DigitsRow
import Johnson.Top.H.K3PieceHears
import Johnson.Top.H.Keep.MergeApart
import Johnson.Road.K4.MergeBelowReached

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
open Johnson.Desc.First.Walk.Tied (reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- (α)'s sentence gives (β)'s test. -/
theorem sFvFits_of_below {s : VerifiableInference.Desc.First.S}
    (h : OnBytes.Road.K4.MergeBelow s) : VerifiableInference.Desc.K3.sFvFitsB s = true := by
  unfold VerifiableInference.Desc.K3.sFvFitsB
  cases hm : mergeOf s with
  | none => rfl
  | some j =>
    obtain ⟨F, hF, hlt⟩ := h j hm
    show (s.fork?.any fun F => decide (j < F.next)) = true
    rw [hF]
    simp only [Option.any_some]
    exact decide_eq_true hlt

/-- The number of the border in front of the digits' lookup of the layers' segment 2 g. -/
theorem digits_number : ∀ g, g < 12 → k3K (2 * g) true = 28 * g + 5 + 3 := by decide

/-- Outside the head's segment the step without a round behind the digits' lookup writes the ledger
alone. -/
theorem quietAt_digits_is {X : Verify.Public} {i : ℕ}
    (hh : VerifiableInference.Desc.K3.isHead X i = false)
    {f : VerifiableInference.Desc.First.S → Except String VerifiableInference.Desc.First.S}
    (hf : VerifiableInference.Desc.K3.quietAt X i true = some f) :
    ∃ used claims, f = VerifiableInference.Desc.K3.quietDigits used claims := by
  unfold VerifiableInference.Desc.K3.quietAt at hf
  simp only [if_true] at hf
  split at hf
  · rename_i hc
    rw [hh] at hc
    cases hc
  · split at hf <;> split at hf <;>
      (obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact ⟨_, _, rfl⟩)

/-- An accepting bind. -/
theorem k03_bind_ok {ε α β : Type} {y : Except ε α} {f : α → Except ε β} {b : β}
    (h : (y >>= f) = .ok b) : ∃ a, y = .ok a ∧ f a = .ok b := by
  cases y with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

set_option maxHeartbeats 4000000 in
/-- **hmerge BEHIND THE DIGITS' LOOKUP AT THE TWELVE LAYERS' SEGMENTS, AT THE CONSTANT.** -/
theorem k03_mergeAt_digits_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ y tl, digAt (At.X Zp) (2 * g) = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true) u →
      h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ G, (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard v.1 = some G →
        ∀ f ∈ G.rows.toList, ∀ t ∈ f.slots.toList, mergeOf v.1 ≠ some t.1 := by
  intro g hg y tl hy q hq b' hb' B' hB z u v hu hr hun ⟨τ, hout⟩
  have hl : 2 * g < 25 := by omega
  have h24 : 2 * g < 24 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (2 * g) true b' hb'
  have hsub := links_lay (2 * g) h24 (by omega)
  obtain ⟨sub, hs', -, hpcT⟩ := K3Lot.k03_sub_full (2 * g) hl
  obtain rfl : sub = ModelPart.layers := Option.some.inj (hs'.symm.trans hsub)
  have hlook : lookAt (At.X Zp) (2 * g) true = some y := by
    unfold digAt at hy
    obtain ⟨x', h1, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨tl', -, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨h', -, hy⟩ := Option.map_eq_some_iff.1 hy
    obtain rfl : x' = y := congrArg Prod.fst hy
    exact h1
  -- the accept: a yes of the lookup's own decision, then the step without a round
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below (strictAt B' q) B' rfl
    (K.back (2 * g) hl true q hq) u τ v hout
  have hd := hB.1.2 _ _ _ _ hd0
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ := theStated_yes_digits K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b'
    hb' (K.planOk (2 * g) hl true b' hb') (2 * g) rfl hpc u.1 v.1 _ cols hd
  -- in front: a ledger is open, with its sizes
  have hOpen := digits_lookIn_open (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS
    (k3K (2 * g) true) (IM.k3Place (2 * g) true) (2 * g) ModelPart.layers
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (K3Lot.k03_at_full (2 * g) hl true) rfl hsub hpcT
    (.lookIn (2 * g) (7 + shift ModelPart.layers)) (by simp)
  have hp := onQ_front hu hun _ (List.mem_append_left _ hOpen)
  rw [hpcT.symm.trans hpc] at hp
  have hIn := k3LookIn_onIn (fLook_at (k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) (2 * g) true hlook z u.1
    hp)
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  -- (α)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' := reach_raw (h.toAtMg.rch_is_reach _ _ hr)
  rw [digits_number g hg] at hr'
  have hfit := sFvFits_of_below
    (OnBytes.Road.K4.mergeBelow_reach h.scope h.reads O h.laid.planOk hg (by omega : 3 < 4) hr')
  -- (β)
  have key := k3_digits_hmerge (hd := hyes) (hF := hF) (hS := hS) (h := hfit)
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact key
  · have hh : VerifiableInference.Desc.K3.isHead (At.X Zp) (2 * g) = false := by
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

end P5J

#print axioms P5J.sFvFits_of_below
#print axioms P5J.digits_number
#print axioms P5J.quietAt_digits_is
#print axioms P5J.k03_bind_ok
#print axioms P5J.k03_mergeAt_digits_lay
