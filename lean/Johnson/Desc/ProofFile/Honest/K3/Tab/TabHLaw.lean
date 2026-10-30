-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabHLaw.lean:
the reader of the head's keys and bits off tables is the filling's own. Theorems without a
hypothesis, but one small one, whose hypothesis is named.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Tab/TabH.lean; Honest/K3/Tab/TabHSeat.lean.

What is shown.
  `nrTab_ok`, `whTab_ok`, `lwTab_ok`, `colTabH_ok`: each table of Honest/K3/Tab/TabH.lean is an
    array at which `Memo.read` is the function (`Ok1`, `Ok2`: Honest/K3/Tab/TabGLaw.lean).
  `colTabH_read`: so `colH` read off its table is `colH`.
  `innerTabH_is_of`: conditional on `Ok1` of the third array (`h`): the rows' values are the
    library's own. `innerTabH_is`: so are those of the rows off the three tables (`InnerH.Is`).
  `ownH_lift`: `ownH` is `ownHF`, lifted. `kvH_own`: so a call's key at the seated reading is the
    key in the base field, lifted: by `HeadMap.kvH_map` (Johnson/HonestTrace/CountsHeadMap.lean).
  `headTab_eq`: the main theorem: `headTab X (pubH x) C W` is the field `head` of `ownSourcesBound`
    at x, C and W.

Imported. Honest/K3/Tab/TabHSeat.lean, Honest/K3/Tab/TabGLaw.lean, Honest/K3/WitBound.lean,
Johnson/HonestTrace/CountsHeadMap.lean.

Users. Honest/K3/Tab/TabAll2Law.lean and Honest/K3/Tab/TabHToy.lean [not in this library] import
this file.

Limits. The equations say that the terms are equal, not how long either takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabHSeat
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabGLaw
import Johnson.Desc.ProofFile.Honest.K3.WitBound
import Johnson.HonestTrace.CountsHeadMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabH
open OnBytes.Model OnBytes.Ends.H
open ProofFile.Honest.K3.TabG (Ok1 Ok2 ok1_nil ok1_tab ok2_tab)

section Tables

variable {R : Type} [Field R] (P : PubH) (cell : NameH → R)

theorem nrTab_ok : Ok2 (nrTab P cell) fun t k => nrm P cell k t :=
  ok2_tab _ _ _ fun _ => ok1_tab _ _

theorem whTab_ok : Ok2 (whTab P cell) fun v k => wH P cell k v :=
  ok2_tab _ _ _ fun _ => ok1_tab _ _

theorem colTabH_ok : Ok2 (colTabH P) (colH P.L) :=
  ok2_tab _ _ _ fun _ => ok1_tab _ _

/-- Read off its table, `colH` is `colH`. -/
theorem colTabH_read : Memo.read2 (colTabH P) (colH P.L) = colH P.L :=
  funext fun q => funext fun j => colTabH_ok P q j

/-- The values of the rows off the first two tables and any third array at which `Memo.read` is the
checked token's logit are the library's own. Conditional on that `Ok1`; it is used at two arrays of
which it holds: the empty one (`ok1_nil`) and `lwTab` (`lwTab_ok`). -/
theorem innerTabH_is_of (lw : Array R) (h : Ok1 lw fun t => lg P cell (P.win.getD t 0) t) :
    (innerTabH P cell (nrTab P cell) (whTab P cell) lw).Is P cell :=
  ⟨fun t k => nrTab_ok P cell t k, fun v k => whTab_ok P cell v k, fun t => h t⟩

theorem lwTab_ok :
    Ok1 (lwTab P cell (nrTab P cell) (whTab P cell)) fun t => lg P cell (P.win.getD t 0) t := by
  have e : (fun t => lgBy P (innerTabH P cell (nrTab P cell) (whTab P cell) #[])
      (P.win.getD t 0) t) = fun t => lg P cell (P.win.getD t 0) t :=
    funext fun t => lgBy_of (innerTabH_is_of P cell #[] (ok1_nil _)) _ _
  unfold lwTab
  simp only [e]
  exact ok1_tab _ _

/-- **The values of the rows off the three tables are the library's own.** -/
theorem innerTabH_is :
    (innerTabH P cell (nrTab P cell) (whTab P cell)
      (lwTab P cell (nrTab P cell) (whTab P cell))).Is P cell :=
  innerTabH_is_of P cell _ (lwTab_ok P cell)

end Tables

/-- **The seated reading is the reading in the base field, lifted.** -/
theorem ownH_lift (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) :
    ownH X cell entry link = fun n => algebraMap Cb.Gl.F Cb.Gl.E (ownHF X cell entry link n) := by
  funext n
  cases n with
  | w r c => rfl
  | cell a r c =>
    show atOwn X cell link a r c = algebraMap Cb.Gl.F Cb.Gl.E (TabG.atOwnF X cell link a r c)
    unfold atOwn TabG.atOwnF
    cases (tlOf X link).mats[a]? with
    | none => exact (map_zero _).symm
    | some M => rfl

/-- **A call's key at the seated reading is the key in the base field, lifted.** -/
theorem kvH_own (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) (P : PubH) (q i : ℕ) :
    kvH P (ownH X cell entry link) q i =
      algebraMap Cb.Gl.F Cb.Gl.E (kvH P (ownHF X cell entry link) q i) := by
  rw [ownH_lift]
  exact (OnBytes.HonestTrace.HeadMap.kvH_map (algebraMap Cb.Gl.F Cb.Gl.E) P
    (ownHF X cell entry link) q i).symm

/-- **The reader off tables is the filling's own.** -/
theorem headTab_eq {W₀ Xi Tr : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → PubH) (x : Xi) (C : Cells) (W : Weights) :
    headTab X (pubH x) C W = (ownSourcesBound X cells weights pubH).head x C W := by
  have h : (fun q i => algebraMap Cb.Gl.F Cb.Gl.E
      (kvHBy (pubH x) (ownHF X C.cell W.entry (linkH X))
        (innerTabH (pubH x) (ownHF X C.cell W.entry (linkH X))
          (nrTab (pubH x) (ownHF X C.cell W.entry (linkH X)))
          (whTab (pubH x) (ownHF X C.cell W.entry (linkH X)))
          (lwTab (pubH x) (ownHF X C.cell W.entry (linkH X))
            (nrTab (pubH x) (ownHF X C.cell W.entry (linkH X)))
            (whTab (pubH x) (ownHF X C.cell W.entry (linkH X)))))
        (colH (pubH x).L) q i)) = kvH (pubH x) (ownH X C.cell W.entry (linkH X)) := by
    funext q i
    rw [kvHBy_of (innerTabH_is _ _), ← kvH_own]
  unfold headTab
  simp only [colTabH_read, h]
  rfl

end ProofFile.Honest.K3.TabH

#print axioms ProofFile.Honest.K3.TabH.nrTab_ok
#print axioms ProofFile.Honest.K3.TabH.whTab_ok
#print axioms ProofFile.Honest.K3.TabH.innerTabH_is_of
#print axioms ProofFile.Honest.K3.TabH.lwTab_ok
#print axioms ProofFile.Honest.K3.TabH.colTabH_ok
#print axioms ProofFile.Honest.K3.TabH.colTabH_read
#print axioms ProofFile.Honest.K3.TabH.innerTabH_is
#print axioms ProofFile.Honest.K3.TabH.ownH_lift
#print axioms ProofFile.Honest.K3.TabH.kvH_own
#print axioms ProofFile.Honest.K3.TabH.headTab_eq
