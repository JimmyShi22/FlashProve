-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/InsideAtWrap.lean: "EVERY ENTRY THAT THE OPEN SEGMENT's DATA READ LIES INSIDE THE
RANGES OF THE MEMBER AT ITS SEAT" (the library's `InsideAt`, Johnson/Desc/Sound/Clamp/FormsClamp.lean) WITHOUT THE
TABLE's PROMISE: under the library's head alone, at every state without a mark that the wrapped blocks reach at one of
the batching's three borders. The library has it (`P5J.AtMgA.inside_at`, Johnson/P5J/InsideAtCore.lean) at the states
that `onTR` admits at the table `mgAll`, on the verifier's side's frame. Here that proof's closed test `three_full`,
`AtMgA.planFits_at` and `AtMgA.ns_is` are laid again at "reached"; in place of its `inTot_of_promise`, `fold_full` and
`slots_at`: the library's `insideAt_reached`, `foldFacts_at_head'` and `slots_at_reached`, and the smallness test's
`book_at_wrap`: AFTER THAT PROOF, AND AFTER THE PATTERN OF
Johnson/Desc/K8/Honest/MaskOkAtWrap.lean, out of whose `link_at_wrap` and `ns_at_wrap` 5 of the 7 lines of our second
lemma's proof and 9 of the 12 of our third's are taken to the sign, widened from the batching's border to
its three. Statements and proofs ON THE VERIFIER's STATE; no witness, no prover and no frame of the honest side is in
this file; no goal is stated.
  `three_num`   the three borders as numbers · `link_at_three`: the part's link has the segment's number (the library's
      `Meaning.K2.group_all`) · `slots_at_three`: the open ledger's two numbers are the plan's (`slots_at_reached`,
      `AtMgA.ns_is`, `slotsAre_iff`): these two at the RAW reach
  **`insideAt_at_wrap`**   m < 25, i < 3: at (z, s) reached by `cF.blocksInOrder.map below` at `batchAt fullLinks At.ps m + i`, s
      without a mark, pa the part that K9's lens answers: `InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) pa`. By the library's
      `insideAt_reached` at `foldFacts_at_head'`, `three_full` (a closed test, by the kernel), `AtMgA.planFits_at`, and
      that house's `book_at_wrap`
ONE DEVICE: "attribute [-instance] Inst.Model.Scl.ref", as in the files that it follows. TACTICS THAT SEARCH: omega, at
numbers of cuts; one "simp only" with a closed list.
WHAT IS NOT CLAIMED. That any such state is reached. The head is a premise. At the full size and the format's second
hash function alone. Called by Honest/K9/InsideAtStand.lean and InsideBehind.lean. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 3 files: this one and two of the smallness test's house's
(Johnson/Desc/K8/Honest/CellOkAtWrap.lean, MaskOkAtWrap.lean): reading copies.

-/
import Johnson.Desc.K8.Honest.MaskOkAtWrap
import Johnson.P5J.InsideAtCore
import Johnson.Desc.First.Link.Law.PartFitsReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K8.Honest (book_at_wrap)
open VerifiableInference.Desc.LinkJoin (batchAt part_reads slotsAre_iff SlotsInv nsZ slots_at_reached
  insideAt_reached)
open VerifiableInference.Desc.K13.Law (LFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw RchAt)
open P5J (AtMgA TS F0T fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- The three borders as numbers. -/
theorem three_num {m : ℕ} (hm : m < 25) {i : ℕ} (hi : i < 3) :
    14 * m + 3 + (if m = 24 then 1 else 0) ≤ batchAt fullLinks P5J.At.ps m + i ∧
      batchAt fullLinks P5J.At.ps m + i ≤ 14 * m + 14 + (if m = 24 then 2 else 0) ∧
      batchAt fullLinks P5J.At.ps m + i ≤ 353 := by
  rw [LPFK9.batch_nAt m hm]
  unfold IM.nAt
  refine ⟨?_, ?_, ?_⟩ <;> split <;> omega

/-- The part's link has the segment's number, at the batching's three borders. -/
theorem link_at_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {i : ℕ} (hi : i < 3)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m + i) (z, s))
    {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) : pa.L.link = m := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  obtain ⟨n1, n2, -⟩ := three_num hm hi
  obtain ⟨L, hL, hl, -⟩ := Meaning.K2.group_all h.scope h.reads O hm n1 n2 f
  have hL' := (part_reads s pa hpa).1
  obtain rfl : L = pa.L := Option.some.inj (hL.symm.trans hL')
  exact hl

/-- The open ledger's two numbers there. -/
theorem slots_at_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {i : ℕ} (hi : i < 3)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m + i) (z, s))
    {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) :
    pa.F.ns = P5J.At.nsAt Zp m ∧ pa.F.LS.size = pa.F.ns := by
  have hL := (part_reads s pa hpa).1
  have hlk := link_at_three h hm hi hr hpa
  have hs : SlotsInv (nsZ Zp Zp.p.X.H.ns) s := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨A, B, c, e, _, hs⟩ := slots_at_reached _ h.laid.pub h.headSpots h.laid.value
    have he : HEq cF c :=
      congr_arg_heq (fun X : VerifiableInference.Desc.FileDescription ProofFile.Inst => X.first) e
    obtain rfl : cF = c := eq_of_heq he
    exact hs _ (z, s) hr (by rw [Meaning.Carry.front_len h.scope h.reads O]; exact (three_num hm hi).2.2)
  have hs' := hs pa.F pa.L (K9.get_fork s pa hpa) hL
  rw [hlk, h.ns_is hm] at hs'
  exact (slotsAre_iff _ _).1 hs'

/-- **"INSIDE THE MEMBERS' RANGES", WITHOUT THE TABLE's PROMISE**: under the head alone, at every state without a mark
that the wrapped blocks reach at one of the batching's three borders, at the part that K9's lens answers. -/
theorem insideAt_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {i : ℕ} (hi : i < 3)
    {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m + i) (z, s))
    (hu : s.failed = none) {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) :
    InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) pa := by
  have hB := List.all_eq_true.1 (List.all_eq_true.1 P5J.three_full m (List.mem_range.2 hm)) i
    (List.mem_range.2 hi)
  unfold P5J.threeB at hB
  cases hp : P5J.At.ps[batchAt fullLinks P5J.At.ps m + i]? with
  | none =>
    rw [hp] at hB
    cases hB
  | some p =>
    rw [hp] at hB
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hB
    obtain ⟨⟨⟨hl, hpc⟩, hk⟩, -⟩ := hB
    have F := P5J.foldFacts_at_head' h.toAtMg
      (fun k (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Unit) =>
        RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a) (fun _ _ ha => ha) (P5J.laid_at_head h.toAtMg)
      (P5J.startB_at_head h.toAtMg)
      (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
    have hrch : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) (batchAt fullLinks P5J.At.ps m + i) ((z, s), ()) := hw
    have hraw := reach_raw hw
    obtain ⟨e1, e2⟩ := slots_at_three h hm hi hraw hpa
    exact insideAt_reached F h.𝔇.N h.𝔇.ms (h.𝔇.N.group m) hrch hu hp hl hpc hpa (book_at_wrap h hraw)
      (h.planFits_at hk hp hl hm) e1 (Nat.le_of_eq e2)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.three_num
#print axioms ProofFile.Honest.K9.link_at_three
#print axioms ProofFile.Honest.K9.slots_at_three
#print axioms ProofFile.Honest.K9.insideAt_at_wrap
