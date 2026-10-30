-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SplitDepth.lean: the rule that places the oracle messages of one prover's
message in trees (`layTrees`, OnBytes/Iop/Ground.lean), at two messages of two classes of leaves,
the first with main rows, the second of mask rows alone: the second has a tree of its own, as deep
as its mask rows' code. Statements and proofs; no definition.

Why. On a proof file's shared chain the mask message of the split goes out with Omega. The proximity
tests' members want its tree's depth against the first stage's mask code.
Whose is what. Called: `lay_one` (OnBytes/Tie/Pv/Keeps/LayOne.lean: a tree that holds one message
alone has that message's depth); `layTrees_some` (the same file); `laidOf`, `layPass`, `layStep`
(OnBytes/Params/Fit/LayPasses.lean).
What it is not: that `layTrees` returns, the two shapes' rows and that the two classes part are
premises. Two messages alone. No kind and no chain is named but in `split_depth`.
Main names: `two_trees`, `second_depth`, `split_depth`.
Limits: no soundness is claimed. Nothing on hiding.

-/
import OnBytes.Tie.Pv.Keeps.LayOne
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Pin
open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Keeps.Fit (lay_one depth1 layTrees_some)

/-- Two messages, the first with main rows, the second without, of two classes: two trees. -/
theorem two_trees (codes : Codes) (n0 n1 : OracleNotice) (h0 : n0.shape.mainRows ≠ 0)
    (h1 : n1.shape.mainRows = 0) (hc : n0.leafClass ≠ n1.leafClass) :
    (laidOf codes #[n0, n1]).2.2 = #[0, 1] := by
  have b0 : (n0.shape.mainRows == 0) = false := by simpa using h0
  have b1 : (n1.shape.mainRows == 0) = true := by simpa using h1
  have bc : (n0.leafClass == n1.leafClass) = false := by simpa using hc
  simp [laidOf, layPass, layStep, List.range_succ, b0, b1, bc, Array.getD_eq_getD_getElem?]
  rfl

/-- **The tree of the second of two such messages is as deep as its mask rows' code.** -/
theorem second_depth (codes : Codes) (n0 n1 : OracleNotice) (T : TreeLay)
    (h : layTrees codes #[n0, n1] = some T) (h0 : n0.shape.mainRows ≠ 0)
    (h1 : n1.shape.mainRows = 0) (h2 : 0 < n1.shape.maskRows)
    (hc : n0.leafClass ≠ n1.leafClass) :
    (T.shapes.getD (T.tree.getD 1 0) default).logN =
      (codes.mask.getD n1.shape.maskCode default).logN := by
  obtain ⟨_, _, eT, _⟩ := layTrees_some h
  have et : T.tree = #[0, 1] := eT.trans (two_trees codes n0 n1 h0 h1 hc)
  obtain ⟨hlt, hd, _⟩ := lay_one (i0 := 1) h (by simp) (by
    intro j hj e
    rw [et] at e
    have hj' : j < 2 := by simpa using hj
    rcases j with _ | _ | j
    · simp at e
    · rfl
    · omega)
  have e1 : (#[n0, n1] : Array OracleNotice).getD 1 default = n1 := rfl
  rw [e1] at hd
  unfold depth1 at hd
  rw [h1, Nat.zero_mul, if_pos rfl, if_pos h2] at hd
  rw [← hd]
  generalize T.tree.getD 1 0 = q at hlt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  rfl

/-- At what goes out with Omega, where the chain has a split. -/
theorem split_depth (codes : Codes) (S : LinShape) (T : TreeLay)
    (hS : S.sharedSplitNeeded = true) (h : layTrees codes (linMessageOmega S) = some T)
    (h0 : S.omega.mainRows ≠ 0) (h1 : S.sharedSplit.mainRows = 0)
    (h2 : 0 < S.sharedSplit.maskRows) (hc : S.omegaLeafClass ≠ S.sharedSplitLeafClass) :
    (T.shapes.getD (T.tree.getD 1 0) default).logN =
      (codes.mask.getD S.sharedSplit.maskCode default).logN := by
  have e : linMessageOmega S =
      #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] := by
    unfold linMessageOmega
    simp [hS]
  rw [e] at h
  exact second_depth codes _ _ T h h0 h1 h2 hc

end H2K.Pin

#print axioms H2K.Pin.two_trees
#print axioms H2K.Pin.second_depth
#print axioms H2K.Pin.split_depth
