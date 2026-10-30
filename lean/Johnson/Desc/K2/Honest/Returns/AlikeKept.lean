-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/AlikeKept.lean: TWO STATEMENTS WITH THE SAME CODES, IN WHICH EACH
KEPT MEMBER OF THE OLD GROUP STANDS AS ONE AND THE SAME MESSAGE, ARE ALIKE TO THOSE PREMISES OF THE
LAW ON THE STEP BEHIND THE SENDING THAT THE SENDING MUST KEEP (Returns/BehindAt.lean's head: "who
must leave what"): the program's test on the target, `OldFits`, `TablesFit`, "the stored rows read
the main table alone". Statements and proofs.

WHY. Returns/Alike.lean has the like for two statements with the same core of EVERY message: so over
the joins. A sending lays new messages: that relation fails over it. These premises read a message
at the kept old members' numbers alone.

  `AlikeKept`       the relation, at the carried rows `old`
  `AlikeKept.getD`, `.bits`   what it gives of a kept member: the message; its tables' index bits
  `AlikeKept.sizes`   `sizesAt` is one
  `AlikeKept.check`   the program's test on the target is carried: NOT PROVED ANEW: the library's
                    `check_congr` (Johnson/Top/H/SwitchPads.lean, "The test in front of the sending
                    and behind it"), which asks less: the same shapes at the kept members
  `AlikeKept.oldFits`, `.tables`, `.reads`   the three others are carried

Limits. That a sending gives the relation is not shown here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.BehindAt
import Johnson.Top.H.SwitchPads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (readsMainOf)

/-- The same codes; each kept member of the old group is one and the same message. -/
structure AlikeKept (old : SingleRows) (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  same : ∀ o ∈ (switchKept old).toList, S'.oracles[o]? = S.oracles[o]?

variable {old : SingleRows} {S S' : Statement}

theorem AlikeKept.getD (h : AlikeKept old S S') (o : Nat) (ho : o ∈ (switchKept old).toList) :
    S'.oracles.getD o default = S.oracles.getD o default := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, h.same o ho]

theorem AlikeKept.bits (h : AlikeKept old S S') (o : Nat) (ho : o ∈ (switchKept old).toList)
    (part : Part) : S'.tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [h.same o ho, h.codes]

theorem AlikeKept.sizes (h : AlikeKept old S S') (T : SwitchTarget) :
    sizesAt S' old T = sizesAt S old T := by
  unfold sizesAt
  rw [h.codes, List.map_congr_left fun o ho => by rw [h.getD o ho]]

/-- The program's test on the target: the library's `check_congr`. -/
theorem AlikeKept.check (h : AlikeKept old S S') {T : SwitchTarget}
    (c : switchTargetCheck S old T = true) : switchTargetCheck S' old T = true :=
  (Johnson.Top.H.check_congr S S' old h.codes (fun o ho => by rw [h.getD o ho]) T).trans c

theorem AlikeKept.oldFits (h : AlikeKept old S S') (F : OldFits S old) : OldFits S' old := by
  have hc := h.codes
  exact ⟨by rw [hc]; exact F.mainVars, by rw [hc]; exact F.d0, by rw [hc]; exact F.d1,
    by rw [List.map_congr_left fun o ho => by rw [h.getD o ho]]; exact F.rows, F.named, F.once,
    fun o ho => by rw [h.getD o ho]; exact F.keptCode o ho,
    fun o ho => by rw [h.getD o ho]; exact F.stored o ho⟩

theorem AlikeKept.tables (h : AlikeKept old S S') {T : SwitchTarget} (N : OldFits S old)
    (F : TablesFit S old T) : TablesFit S' old T :=
  ⟨by rw [h.codes]; exact F.bitsG, by rw [h.sizes, h.codes]; exact F.bitsKept,
    by rw [h.codes]; exact F.claimMain,
    fun f hf => by rw [h.bits f.oracle (N.named f hf)]; exact F.claimKept f hf,
    fun o ho => by rw [h.getD o ho, h.bits o ho]; exact F.stored o ho⟩

theorem AlikeKept.reads (h : AlikeKept old S S')
    (F : ∀ o ∈ (switchKept old).toList,
      ∀ r ∈ (S.oracles.getD o default).sampleRows.toList, readsMainOf o r = true) :
    ∀ o ∈ (switchKept old).toList,
      ∀ r ∈ (S'.oracles.getD o default).sampleRows.toList, readsMainOf o r = true :=
  fun o ho => by rw [h.getD o ho]; exact F o ho

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.sizes
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.check
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.oldFits
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.tables
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.reads
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.getD
#print axioms VerifiableInference.Desc.K2.Honest.Returns.AlikeKept.bits
