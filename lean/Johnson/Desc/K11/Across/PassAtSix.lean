-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Across/PassAtSix.lean: the proofs of `PassAtSix` and `RunsPassAtReached`
(Johnson/Desc/K11/Across/PassAtSixStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. The first: THE LIBRARY's OWN PROOF OF `fwd_of_runsPass`
(Johnson/Top/H0/MergeLaw/RunsAtMerge.lean), TAKEN OVER LINE FOR LINE, with the field on the late
slots beside each field on the reader, and both halves of `equations_pass` at the tenth run. The
second: joinings, as the kind's own `frontAtReached` and `promiseBehindMerge` have them
(Johnson/Desc/K11/Behind/): the head's segment has the number 24 (`Meaning.scope_plans`) ·
`leaves_reach_paid` · `K11.tablesLaid_346` · `runsAre_at_link24` · `speaksOfTests` · the lookup's
test out of the public item "lookOut 24 3" · `runsPassOfTests`.

Limits. Those of the statements. One closed fact goes by evaluation in Lean's kernel (`decide
+kernel`), as in the library's own proof. Nothing on any property.
-/
import Johnson.Desc.K11.Across.PassAtSixStatement
import Johnson.Desc.K11.Behind.Reached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Across
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub)
open VerifiableInference.Desc.First.Look (lookOutC)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge.Behind (speaksOfTests runsPassOfTests)

/-- **Both facts at every run under the six names.** -/
theorem passAtSix : PassAtSix := by
  intro Xi P Tok rows cols nR X D hl Pm a b rs hy H y hy' p hp
  have hs : D.links[24]? = some .head := by
    rw [hl]
    decide +kernel
  rw [runs_at_sort D 24 y.1 y.2 .head hs] at hp
  have hmem : p ∈ sixNames.flatMap
      (fun x => VerifiableInference.Desc.First.runsOf .head x.1 x.2) :=
    List.mem_flatMap.2 ⟨y, hy', hp⟩
  rw [six_are_ten] at hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨H.fwd_objects2, H.late_objects2⟩
  · exact ⟨H.fwd_guests2, H.late_guests2⟩
  · exact ⟨H.fwd_planes2, H.late_planes2⟩
  · exact ⟨H.fwd_join3, H.late_join3⟩
  · exact ⟨H.fwd_norm3, H.late_norm3⟩
  · exact ⟨H.fwd_policy3, H.late_policy3⟩
  · exact ⟨H.fwd_logits3, H.late_logits3⟩
  · exact equations_pass D.lk X _ 24 5 Pm hy
  · exact ⟨H.fwd_objects7, H.late_objects7⟩
  · exact ⟨H.fwd_guests7, H.late_guests7⟩

/-- **The library's condition on the nine runs, at a reached state, from the public tests.** -/
theorem runsPassAtReached : RunsPassAtReached := by
  intro Z D r Zp Np cF x h Pm z s s' rs hR hq hled hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hH : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  have hlen : leavesLenB s = true := leaves_reach_paid h.scope h.reads O h.laid.planOk hR
  have ht : TablesLaid (VerifiableInference.Desc.K9.phAt (P5J.At.X Zp) 24) s := by
    have e := K11.tablesLaid_346 h.scope h.reads O (z, s) hR
    rw [O.W] at e
    exact e
  obtain ⟨Lk, iU3, lm, hLk, -, -, HR⟩ := runsAre_at_link24 h.scope h.reads O
  have hlk24 : h.𝔇.lk 24 = some Lk := (ToldDesc.linkAt_of_open O 24).trans hLk
  have HR' : RunsAre Lk (P5J.At.X Zp) iU3 lm := by
    have e := HR
    rw [O.W] at e
    exact e
  have hsp : Speaks Lk s := speaksOfTests _ _ _ _ _ _ _ h.𝔇 mgBase z s Lk rfl hH hq hlk24 ht
  have hout : lookOutC h.𝔇.pubD.d3 24 false s = true := by
    have h1 : (mgAll h.𝔇 mgBase).pub (.lookOut 24 3) (z, s) = true :=
      hq (Pub.lookOut 24 3) (by simp [keep24])
    rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_lookOut h.𝔇.pubD mgBase.pub 24 3 false
      (sorts_at_head hH).1] at h1
    exact h1
  exact runsPassOfTests _ _ _ _ _ _ _ h.𝔇 Pm Lk iU3 lm s s' rs hlk24 HR' hy hled hout hsp hlen

end Johnson.Desc.First.ForkMerge.Across

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Across.passAtSix
#print axioms Johnson.Desc.First.ForkMerge.Across.runsPassAtReached
