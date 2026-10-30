-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastTreeO.lean: THE SHAPE OF THE TREE OF OMEGA's COPY, IN THE LAST CHAIN's OWN
BOOK: A TEST WITH CODE ON THE STATE; EARNED AT K14's SECOND PART's OWN ACCEPTING RUN; SPENT AT THE
OWN PROXIMITY TEST. THE DEFINITIONS `treeOB` AND `yTree` LIE IN PlmCode.lean
(so that a walk can load them lightly); this file
imports it and holds `PlanTreeO` and the lemmas.
Why. The last table's book-keeping says of that tree its number and its source, not its shape (the
field `Laid.tree`). So "its shape is what the description tells" could be asked of no statement
inside the promise: a premise that nobody can meet. Here it rides as a layer on the last chain's own
state (LastLayerS.lean).
  `treeOB cs S s`: the verifier's own layout of the plan's one notice for Omega can be made; the
    message at s.loc.omega has a place in s's book; the tree there has that layout's one shape.
    `yTree cs S`: the layer: that test at borders 1 and 2; yes elsewhere.
  `treeOB_of_yes`: **K14's second part's accepting run lays it**, where the state in front bears the
    plan's codes: by `laid_tree_shape`
    (Johnson/Desc/Third/Law/TreeShape.lean) and
    `laid_k14Second` (where the copy's number and place lie).
  `treeO_of_test`: the test's yes, with ONE TEST ON THE PLAN (`PlanTreeO`: that layout's shape is
    what the description tells of the tree with Omega's number), gives the clause that `BookAt` asks
    at Omega's copy.
Limits. That the shared chain's own tree of Omega has that shape is not said here (left to a law on
layouts, and to `omegaShape_real | _key`, not in this library). Nothing on soundness.
-/
import Johnson.LLT25R.PlmCode
import Johnson.LLT25R.LastYesLays
import Johnson.Desc.Third.Law.TreeShape
import Johnson.Desc.Third.Law.Laid
import Johnson.Desc.K12.Coin.FramesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K12.Coin (ShapeIs)

/-- **K14's second part's accepting run lays it.** -/
theorem treeOB_of_yes {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hc : s.st.codes = p.codes) : treeOB p.codes p.S s' = true := by
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s s' rs gs h
  obtain ⟨lay, tO, hl, ht, hs, -⟩ := laid_tree_shape p s s' rs gs h
  rw [hc] at hl
  have e1 : s'.loc.omega = s.st.oracles.size := by rw [L.loc]
  unfold treeOB
  rw [hl, e1, L.place]
  simp only [ht, hs, decide_true]

/-- **The test on the plan**: that layout's shape is what the description tells of the tree number
n. -/
def PlanTreeO {Xi : Type} (G : FileDescription Xi) (cs : Codes) (S : LinShape) (n : ℕ) : Prop :=
  ∀ lay, layTrees cs #[⟨S.omega, S.omegaLeafClass⟩] = some lay →
    ∀ o, G.oracleAt n = some o → ShapeIs (lay.shapes.getD 0 {}) o

/-- **What `BookAt` asks at Omega's copy.** -/
theorem treeO_of_test {Xi : Type} (G : FileDescription Xi) (cs : Codes) (S : LinShape) (n : ℕ) (s : S₃)
    (h : treeOB cs S s = true) (hP : PlanTreeO G cs S n) :
    ∀ z u T, s.book.place[s.loc.omega]? = some (z, u) → s.book.trees[z]? = some T →
      ∀ o, G.oracleAt n = some o → ShapeIs T.shape o := by
  intro z u T hp hT o ho
  unfold treeOB at h
  cases hl : layTrees cs #[⟨S.omega, S.omegaLeafClass⟩] with
  | none => rw [hl] at h; simp at h
  | some lay =>
    rw [hl, hp] at h
    simp only [hT] at h
    rw [of_decide_eq_true h]
    exact hP lay hl o ho

end LLT25

#print axioms LLT25.treeOB_of_yes
#print axioms LLT25.treeO_of_test
