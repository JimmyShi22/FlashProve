-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/SlotAtHeadSeg.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE WINDOW
OF SLOTS THAT THE LOOKUP ON THE DIGITS LAYS IN THE TEST's DATA ENDS INSIDE THE LEDGER's NUMBER OF
SLOTS (tl.slotB ≤ G.ns) IN FRONT OF THE OUTPUT HEAD's SEGMENT's BATCHING TOO: IN THE GOALS' SCOPE,
THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN, AT EVERY STATE THAT
THE FIRST CHAIN's BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH AT 347. THAT ANY SUCH
STATE IS REACHED IS NOT SHOWN. Lemmas; none of the library's goals.

  `slot_behind_digits_wrap` the scope · the files read · the opening · the test on the plan · l < 25
                   · a state that the wrapped blocks reach at 14 l + IM.k3Ix l true + 2 + 1 · its
                   ledger has its sizes ⊢ tl.slotB ≤ G.ns
  **`slot_at_head_seg`** the first four · a state that the wrapped blocks reach at 347 ⊢ tl.slotB ≤
                   G.ns
HOW. One block back over the head's merge (the library's IM.k11_of and LinkJoin.backB_of), at three
relations at once: the merge leaves the test's data (MergeLaw.merge_leaves_tl,
Johnson/Top/H0/MergeLaw/LeavesTl.lean), makes the ledger a later one, so with the same number of
slots (LinkJoin.k11_laterS, Johnson/Desc/First/Link/Law/LaterStretch.lean; PscRun.Later.ns), and
hands the sizes back (LinkJoin.k11_sizesS, SizesStretch.lean). The sizes at 347:
`sized_at_head_wrap` (AllFrontAtHeadSeg.lean). Behind the lookup on the digits: `slot_behind_digits`
(SlotAtReach.lean).
WRITTEN A FURTHER TIME: `slot_behind_digits_wrap` is the proof of `slot_at_batch` (SlotAtReach.lean)
at the wrapped family, at l < 25, with the sizes as a premise; its lines up to the seated block's
yes are those of `zy_below_behind_digits` (AllFrontAtHeadSeg.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: a bare
`simp` on one line, on a sum of two ifs · `omega` on three lines, on numbers of segments alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED AT 347: where none is, all is idle. AT THE WRAPPED
FAMILY ALONE (`Sound.below` is a device of the proof and runs nowhere). IN SCOPE ALONE: the full
size; the first chain; at OnBytes.secondHashFunction. Which of the files beneath it are rows of the library is
for the library's own list to say: it is not said here. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.AllFrontAtHeadSeg
import Johnson.Desc.K8.Honest.SlotAtReach
import Johnson.Desc.First.Link.Law.LaterStretch
import Johnson.Desc.First.Link.Law.SizesStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (piece_digits sizes_behind_digits SizesS)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind the lookup on the digits, at each of the 25 segments**, at a state that the wrapped
blocks reach and whose ledger has its sizes. -/
theorem slot_behind_digits_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (h1 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + IM.k3Ix l true + 2 + 1) (z, s))
    (hz : ∃ G, s.fork? = some G ∧ PscRun.Sized G) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) : tl.slotB ≤ G.ns := by
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
  obtain ⟨G', n, a1, a2, a3⟩ :=
    slot_behind_digits _ _ _ _ _ _ b' e3 hOk' l rfl hpc s₀ _ rs gs hd' hG₀ hz₀
  obtain rfl : G' = G := Option.some.inj (a1.symm.trans hG)
  rw [ht] at a2
  obtain rfl : tl.slotB = n := Option.some.inj a2
  exact a3

/-- **IN FRONT OF THE HEAD's SEGMENT's BATCHING.** -/
theorem slot_at_head_seg (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) : tl.slotB ≤ G.ns := by
  obtain ⟨Lk, b, e1, e2, e4, -⟩ := IM.k11_of hS hR O
  obtain ⟨s6, r6, k1, k2, k3⟩ := LinkJoin.backB_of
    (R := fun u t => t.tl? = u.tl? ∧ LaterS u t ∧ SizesS u t) hS hR O (l := 24) (i := 8)
    (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun u rs gs t hd => ⟨MergeLaw.merge_leaves_tl _ u rs gs t hd,
      LinkJoin.k11_laterS _ u rs gs t hd, LinkJoin.k11_sizesS _ u rs gs t hd⟩) h
  obtain ⟨G6, hG6, hz6⟩ := k3.pulls (sized_at_head_wrap hS hR O hOk h)
  have a := slot_behind_digits_wrap hS hR O hOk (l := 24) (by omega) (z := z) (s := s6) r6
    ⟨G6, hG6, hz6⟩ (k1.symm.trans ht) hG6
  obtain ⟨G7, hG7, L⟩ := k2 G6 hG6
  obtain rfl : G7 = G := Option.some.inj (hG7.symm.trans hG)
  rw [L.ns]
  exact a

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.slot_behind_digits_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.slot_at_head_seg
