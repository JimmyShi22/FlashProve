-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchRowsAt.lean: at sizes z whose setting, codes, links, links' group and last test's
stages are the full size's written ones, THE RECORD OF THE CODE SWITCH THAT `rowOf` MAKES OF z AND
OF THE PLANNER's RECORD OF A GROUP IS THE WRITTEN RECORD OF THAT SWITCH, at each of the 25; so the
four facts that are proved of the written records hold of it; and the written list of what is
sampled goes along what the planner's record says is sent.

Why. The law of the code switch at a seated place (`K02LawOf`, Johnson/Top/H0/K2Caller/SitsLaw.lean)
speaks of `rowOf z lo l kept f` at all lists lo, l, kept, and asks of it two tests' yes, a third
beneath, and has its level as a field of it. At the 25 written records (`tableFullLit`) these lie as
theorems. One equation carries them over.
  `full_allP`: what holds of the five different written records holds of all 25.
  `lit_fields`: of each written record: its setting, codes, number of trees and rider, and that its
  radius is the planner's at its setting and the group in front.
  `row_written`: THE EQUATION: by `frames_written` and `rowOf_eq`
  (Johnson/Top/H0/K2Caller/RowEq.lean).
  `row_paid`: so ok, writtenOK and sizedB say yes at it, and its target is 128.
  `tiedOkAt`, `tiedOk_all`, `tied_written`: the test `tiedB` (Johnson/Top/H0/K2Hands/TiedAt.lean)
  says yes at the written record's list l and what the planner's record says is sent: Lean's kernel
  says so at all 25.
Limits. LAWS WITH EIGHT PREMISES on z: that the planner's sizes in the goals' scope meet them is not
shown here. lo, l and kept are laid as the written record's: nothing says that they are the
planner's lists. The full size alone. Nothing on the running text of a block; nothing on soundness
or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.SwitchFramesAt
import Johnson.Top.H0.K2Caller.RowEq
import Johnson.Top.H0.K2Caller.LitFull
import Johnson.Top.H0.K2Caller.WrittenLit
import Johnson.Top.H0.K2Caller.SizedLit
import Johnson.Top.H0.K2Caller.At128
import Johnson.Top.H0.K2Hands.TiedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Params OnBytes.Plan H2K.Sizes H2K.Member
open VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First.K2Hands (tiedB)
open Johnson.Top.H (radiusOf)

/-- **What holds of the five different written records holds of all 25.** -/
theorem full_allP (P : SwRow → Prop) (h0 : P full0) (h1 : P fullOdd) (h2 : P fullEven)
    (h3 : P full23) (h4 : P full24) : ∀ R ∈ tableFullLit, P R := by
  intro R hR
  rw [full_is] at hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

set_option maxRecDepth 1000000 in
/-- Five fields of each written record. -/
theorem lit_fields : ∀ R ∈ tableFullLit, R.set = setLit ∧ R.cs = codesFull2 ∧ R.roots = 1 ∧
    R.rider = { maskRows := 1, maskCode := 0, answers := 0 } ∧ radiusOf R.set R.g = R.rad :=
  full_allP _ ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩ ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩
    ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩ ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩
    ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩

/-- The test `tiedB` at switch number i; and that the record is not the first. -/
def tiedOkAt (i : Nat) : Bool :=
  match liteFull[i + 1]?, tableFullLit[i]? with
  | some f, some R => decide (f.l ≠ 0) && tiedB R.l f.members
  | _, _ => false

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at all 25.** -/
theorem tiedOk_all : ((List.range 25).all tiedOkAt) = true := by decide +kernel

/- Lean compares these names and does not open them. -/
attribute [local irreducible] linksFull gLink szLFull codesFull2 tableFullLit liteFull

section
variable (z : ProofSized) (sub : Subproofs) (hlink : z.request.link = linksFull)
  (hcode : z.request.code = 0) (hmask : z.request.maskCode = 0) (hans : z.request.answers = 1)
  (hg : z.link.group = gLink) (hL : z.last.stages = szLFull)
include hlink hcode hmask hans hg hL

/-- **THE WRITTEN LIST OF WHAT IS SAMPLED GOES ALONG WHAT THE PLANNER's RECORD SAYS IS SENT**, at
each of the 25 switches. -/
theorem tied_written : ∀ i, i < 25 → ∀ f, (framesOf z sub)[i + 1]? = some f →
    ∀ R, tableFullLit[i]? = some R → tiedB R.l f.sent = true := by
  intro i hi f hf R hR
  have hf' : liteFull[i + 1]? = some f.lite := by
    rw [← lite_written z sub hlink hcode hmask hans hg hL, List.getElem?_map, hf]
    rfl
  have hk : tiedOkAt i = true := List.all_eq_true.1 tiedOk_all i (List.mem_range.2 hi)
  unfold tiedOkAt at hk
  rw [hf', hR] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [(sent_of_mem z _ _ _ _ _ f (List.mem_of_getElem? hf) hk.1).1]
  exact hk.2

variable (hcs : z.codes = codesFull2) (hset : z.set = setLit)
include hcs hset

/-- **THE EQUATION**: the record that `rowOf` makes of z and of the planner's record of the group,
at the written record's three lists, is the written record. -/
theorem row_written : ∀ i, i < 25 → ∀ f, (framesOf z sub)[i + 1]? = some f →
    ∀ R, tableFullLit[i]? = some R → rowOf z R.lo R.l R.kept f = R := by
  intro i hi f hf R hR
  obtain ⟨a1, a2, a3, a4⟩ := frames_written z sub hlink hcode hmask hans hg hL hcs i hi f hf R hR
  obtain ⟨b1, b2, b3, b4, b5⟩ := lit_fields R (List.mem_of_getElem? hR)
  exact rowOf_eq z f R (hset.trans b1.symm) (hcs.trans b2.symm) a1 b5 a2 (a3.trans (by rw [b3]))
    (a4.trans b4.symm)

/-- **ITS FOUR FRUITS**: the two tests and the third beneath say yes at that record, and its target
is 128. -/
theorem row_paid : ∀ i, i < 25 → ∀ f, (framesOf z sub)[i + 1]? = some f →
    ∀ R, tableFullLit[i]? = some R →
      (rowOf z R.lo R.l R.kept f).ok = true ∧ (rowOf z R.lo R.l R.kept f).writtenOK = true ∧
        (rowOf z R.lo R.l R.kept f).sizedB = true ∧
        (rowOf z R.lo R.l R.kept f).set.target = 128 := by
  intro i hi f hf R hR
  rw [row_written z sub hlink hcode hmask hans hg hL hcs hset i hi f hf R hR]
  have hm := List.mem_of_getElem? hR
  exact ⟨List.all_eq_true.1 tableFullLit_ok R hm, List.all_eq_true.1 full_written_ok R hm,
    List.all_eq_true.1 full_sized R hm, target_full R hm⟩

end

end Johnson.G

#print axioms Johnson.G.full_allP
#print axioms Johnson.G.lit_fields
#print axioms Johnson.G.tiedOk_all
#print axioms Johnson.G.tied_written
#print axioms Johnson.G.row_written
#print axioms Johnson.G.row_paid
