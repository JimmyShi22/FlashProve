-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsTie.lean: after a run of the program's code switch the tie before the next fold
holds.

Between the blocks of the program's proximity test a tie says where the oracle messages that the
next block reads are in the book of trees, and how the group places them
(OnBytes/Slice/BlkTies.lean: `GroupTie`). This file shows the tie after a run of the code switch
(OnBytes/Slice/BlkCsRun.lean: `CsRan`) into a stage, where one oracle message, the next fold's fresh
mask, goes with the new one in the same prover's message.

Main theorems: `CsRan.noKept`, `CsRan.vars`, `CsRan.layAt`, `CsRan.groupTie`.
What is asked: the group was new; the program has put both oracle messages in one tree, whose shape
lists their symbols and has the new code's length.
Not claimed. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsSeat
import OnBytes.Slice.BlkNoKept
import OnBytes.Slice.BlkBatVars
import OnBytes.Slice.BlkTies

set_option autoImplicit false

namespace OnBytes.Slice

section
variable {old : SingleRows} {gp nc nz a b : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The row that a run of the switch into a new group returns has no form on a kept member. -/
theorem CsRan.noKept
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) : row.kept = #[] := by
  refine combine_noKept _ gp _ theta row h.row (h.fits hm hr) fun i => ?_
  show lay.kept.getD i false = false
  rw [h.lay_eq hm hk]
  cases i <;> rfl

/-- After a run of the switch into a new group, each tensor of the returned row's form on the main
table has at least one variable. -/
theorem CsRan.vars
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) :
    ∀ v ∈ row.c.tensors, 1 ≤ v.vars := by
  intro v hv
  have h1 : lay.k ≤ v.vars := combine_vars _ gp _ theta row h.row (h.fits hm hr) v hv
  have h2 : lay.k = max (max a b) 1 := by rw [h.lay_eq hm hk]
  omega

/-- The layout that a run of the switch into a new group returns has the new oracle message as its
one member, from the row 0 on in both tables. -/
theorem CsRan.layAt
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) :
    LayAt [c.st.oracles.size] #[some 0] #[some 0] lay := by
  rw [h.lay_eq hm hk]
  exact ⟨rfl, fun w hw => by
    obtain rfl : w = 0 := by simpa using hw
    rfl, rfl, rfl⟩

/-- The tie before the next fold holds after a run of the switch. N: the oracle message that
goes with the new one. sh: the shape of their tree. n: the tree's number. -/
theorem CsRan.groupTie (s' : Sg) (N : OracleNotice)
    (h : CsRan old (switchTargetStage nc nz a b 1) gp #[N] c c' out row lay theta D)
    (hG : D.G = { code := nc, maskCode := nz }) (sh : TreeShape) (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (sentOf (switchTargetStage nc nz a b 1) #[N]).size →
      D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols = (((sentOf (switchTargetStage nc nz a b 1) #[N]).toList.map
      (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols = (((sentOf (switchTargetStage nc nz a b 1) #[N]).toList.map
      (·.shape)).map fun s => s.maskRows * 3).toArray)
    (hlog : sh.logN = s'.C.a) (n : ℕ) (hn : c.ch.firstTree + c.ch.roots = n) :
    GroupTie s' n [(switchTargetStage nc nz a b 1).shape, N.shape] #[some 0] #[some 0] c' row lay
      (c.st.oracles.size + 1) := by
  have hm : D.G.members = #[] := by rw [hG]
  have hk : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  refine ⟨h.noKept hm hk hr, [c.st.oracles.size], h.layAt hm hk, ?_⟩
  have hs := h.seat sh h1 ht hmain hmask
  rw [hlog, hn] at hs
  have hids : (List.range (sentOf (switchTargetStage nc nz a b 1) #[N]).size).map
      (· + c.st.oracles.size) = [c.st.oracles.size] ++ [c.st.oracles.size + 1] := by
    show [0 + c.st.oracles.size, 1 + c.st.oracles.size] = _
    rw [Nat.zero_add, Nat.add_comm 1]
    rfl
  rw [hids] at hs
  exact hs

end

end OnBytes.Slice

#print axioms OnBytes.Slice.CsRan.noKept
#print axioms OnBytes.Slice.CsRan.vars
#print axioms OnBytes.Slice.CsRan.layAt
#print axioms OnBytes.Slice.CsRan.groupTie
