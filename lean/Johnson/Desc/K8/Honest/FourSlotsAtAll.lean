-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourSlotsAtAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: IN FRONT
OF EACH OF THE 25 BATCHINGS EVERY SLOT THAT A FORM OF THE FIRST FOUR CLAIMS OF THE RUN
"K8.equations" NAMES (K9L.four8) LIES IN THE WINDOW OF THE SUMCHECK OVER THE LEAVES OR IS FILLED AT
THE STATE's OWN LEDGER, AND THAT LEDGER HAS ITS SIZES: IN THE FORM OF WHAT IS FIXED BEFORE THE DRAW:
IN THE GOALS' SCOPE, THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN,
AT EVERY STATE THAT THE BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH THERE. THAT ANY
SUCH STATE IS REACHED IS NOT SHOWN. THE LAW IS THE LIBRARY's: calls; none of the library's goals.

  `four_behind_digits_wrap` the four · l < 25 · the wrapped blocks' reach right behind the lookup on
                   the digits · the ledger there has its sizes ⊢ ∃ g G, what was heard, the ledger,
                   its sizes, none of the four forms names an entry, and at every later ledger H the
                   clause on the slots
  **`fourSlots_at_all`** the four · l < 25 · the wrapped blocks' reach at the segment's batching · π
                   φ u with π (φ s) = (s.tl?.map (blank u), s.funs?) ⊢ ∀ v tlb g, (fixed9 φ s).2 =
                   some v → (π (fixed9 φ s).1).1 = some tlb → tlb.heard = some g → Sized v.F ∧ ∀ cl
                   ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList, InWin (winOf g.leaves) x.1 ∨ Filled
                   v.F x.1
By: the library's law of the step, LinkJoin.four_behind_digits, and four_fixed
(Johnson/Desc/First/Link/Law/FourBehindDigits.lean) · the sizes in front of the step pulled back
from those behind it (LinkJoin.sizes_behind_digits, SizesS.pulls) · below 24: P1K8.sized_at_batch ·
at the head's segment: across the merge by LinkJoin.backB_of with MergeLaw.merge_leaves_tl,
k11_laterS, k11_sizesS, and `sized_at_head_wrap` (AllFrontAtHeadSeg.lean).
KIN IN THE LIBRARY, NOT CALLED: LinkJoin.four_raw_at, four_at_batch, four_at_head
(Johnson/Desc/First/Link/Law/FourAtBatch.lean) end in the same sentences at the chain's own blocks,
UNDER A PREMISE ON EVERY STATE REACHED IN FRONT OF THE STEP (hLed: its ledger has its sizes), which
at the head's segment nothing pays; their proofs spend it at the one state in front alone. HERE THAT
PREMISE IS GONE: for that the walk stands at the wrapped family. four_raw_at's PROOF IS WRITTEN A
FURTHER TIME in the first, as `slot_behind_digits_wrap` (SlotAtHeadSeg.lean) has it;
`slot_at_head_seg`'s in the second.
WHAT IT IS FOR: the first fact of `FourFactsAt` (FourFactsAt.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
four lines, on numbers of segments alone · a bare `simp` on one line, on a sum of two `if`s.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED: where none is, all is idle. That the window itself
lies below the ledger's number of slots is not said. IN SCOPE ALONE: the full size; the first chain;
at OnBytes.secondHashFunction. Which of the files beneath it are rows of the library is for the library's own
list to say: it is not said here. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.SlotAtHeadSeg
import Johnson.Desc.First.Link.Law.FourAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (piece_digits sizes_behind_digits SizesS)
open VerifiableInference.Desc.K9L (Pub9 fixed9 four8)
open VerifiableInference.Desc.K4Values (winOf InWin)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide reach_raw)
open OnBytes.Road.K4 (reach_pred)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Right behind the lookup on the digits, at the blocks with the test on words in front: what was
heard, the ledger, and where the four claims' slots lie. -/
theorem four_behind_digits_wrap (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (h1 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + IM.k3Ix l true + 2 + 1) (z, s))
    (hz : ∃ G, s.fork? = some G ∧ PscRun.Sized G) :
    ∃ g G, s.tl?.bind (·.heard) = some g ∧ s.fork? = some G ∧ PscRun.Sized G ∧
      (∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[]) ∧
      ∀ H, _root_.Fo.Later G H → ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
        InWin (winOf g.leaves) x.1 ∨ PscRun.Filled H x.1 := by
  have hp := blocks_planOk O hOk
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  obtain ⟨z', s₀, s'', b₀, e, hr, hb, hy⟩ := reach_pred h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  rw [List.getElem?_map, hf] at hb
  obtain rfl : Sound.below b = b₀ := Option.some.inj hb
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨-, hd₀⟩ := Sound.below_yes b _ _ _ _ hd
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s₀ _ rs gs).1 hd₀).1
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨G₀, hG₀, hz₀⟩ :=
    (sizes_behind_digits _ _ _ _ _ _ b' l e3 hOk' rfl hpc s₀ rs gs _ hd').pulls hz
  exact LinkJoin.four_behind_digits _ _ _ _ _ _ b' e3 hOk' l rfl hpc s₀ _ rs gs hd' hG₀ hz₀

/-- **IN FRONT OF EACH OF THE 25 BATCHINGS: THE FOUR CLAIMS' SLOTS LIE IN THE LEAVES' WINDOW OR ARE
FILLED AT THE STATE's OWN LEDGER**, in the form of what is fixed. -/
theorem fourSlots_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (TailClaims.Law.blank u), s.funs?)) :
    ∀ v tlb g, (fixed9 φ s).2 = some v → (π (fixed9 φ s).1).1 = some tlb →
      tlb.heard = some g → PscRun.Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        InWin (winOf g.leaves) x.1 ∨ PscRun.Filled v.F x.1 := by
  by_cases h24 : l = 24
  · subst h24
    have h' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s) := h
    obtain ⟨Lk, b, e1, e2, e4, -⟩ := IM.k11_of hS hR O
    obtain ⟨s6, r6, k1, k2, k3⟩ := LinkJoin.backB_of
      (R := fun u t => t.tl? = u.tl? ∧ LaterS u t ∧ SizesS u t) hS hR O (l := 24) (i := 8)
      (by omega) e1 e2 e4 (fun h => nomatch h)
      (fun u rs gs t hd => ⟨MergeLaw.merge_leaves_tl _ u rs gs t hd,
        LinkJoin.k11_laterS _ u rs gs t hd, LinkJoin.k11_sizesS _ u rs gs t hd⟩) h'
    obtain ⟨G7', hG7', hz7⟩ := sized_at_head_wrap hS hR O hOk h'
    obtain ⟨g, G6, a1, a2, -, a3, a4⟩ := four_behind_digits_wrap hS hR O hOk (l := 24)
      (by omega) (z := z) (s := s6) r6 (k3.pulls ⟨G7', hG7', hz7⟩)
    obtain ⟨G7, hG7, L⟩ := k2 G6 a2
    obtain rfl : G7 = G7' := Option.some.inj (hG7.symm.trans hG7')
    exact (LinkJoin.four_fixed π φ u hπ (by rw [k1]; exact a1) hG7 hz7 a3
      (a4 G7 ⟨L.next, L.ns, L.keep⟩)).1
  · have hl' : l < 24 := by omega
    rw [if_neg h24] at h
    have i3 : IM.k3Ix l true = 6 := by
      show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
      rw [if_neg h24]
      rfl
    have h1 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
        (14 * l + IM.k3Ix l true + 2 + 1) (z, s) := by
      rw [i3]
      exact h
    obtain ⟨g, G, a1, a2, az, a3, a4⟩ := four_behind_digits_wrap hS hR O hOk hl h1
      (_root_.P1K8.sized_at_batch hS hR O hOk hl' (reach_raw h))
    exact (LinkJoin.four_fixed π φ u hπ a1 a2 az a3
      (a4 G ⟨le_refl _, rfl, fun _ hx => ⟨hx, rfl, rfl⟩⟩)).1

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.four_behind_digits_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.fourSlots_at_all
