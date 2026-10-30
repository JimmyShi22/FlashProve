-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJointLast.lean: after a run of the program's last stage, from the joint before it,
in which no named test has failed, the library's decision on the base case accepts.

OnBytes/Slice/BlkJoints.lean writes down what is known between two blocks of the program's run on a
link's chain. This file adds the joint before the base case and proves the statement of
OnBytes/Slice/BlkChain.lean on the last stage for it, from the theorem on the program's last stage
run on a view (OnBytes/Slice/BaseOpen.lean).

Main definitions.
 `OneAndOne`   an oracle message of one main row over the extension field and one mask row.
 `LastAt`      the joint before the base case.
Main theorems.
 `lastBook_of_seat`   the seat of the last tree (OnBytes/Slice/BlkSeat.lean: `Seat`, which oracle
                      messages are its parts) gives what that theorem asks of the book.
 `lastRuns_at`        from `LastAt` at a claim q, a run of the last stage after which no named test
                      has failed gives that the library's decision, `LdwAccept`
                      (Cb/Ld/LdBaseWords.lean), accepts at q, at the word and the masking word of
                      the last written tree and at the values of the two written rounds.

Not claimed. That a run of the program reaches the joint `LastAt`. Nothing on soundness.
-/
import OnBytes.Slice.BaseGk
import OnBytes.Slice.BaseOpen
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.ChainTop

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- An oracle message of one main row over the extension field and one mask row. -/
structure OneAndOne (sh : OracleShape) : Prop where
  /-- one main row -/
  main : sh.mainRows = 1
  /-- over the extension field -/
  deg : sh.mainDeg = 3
  /-- one mask row -/
  mask : sh.maskRows = 1

/-- The joint before the base case, at the last stage s. The program's last group has one row
variable, the stage none: the claim is read with the group's own numbers of row bits. q: the claim.
n: the number of the last tree, whose two parts are the last stage's oracle message and the masking
oracle. The clause on the program's form is what its fixing of a variable is in the field. The
three clauses on the layout say that the one member's rows are folded and begin at the row 0 of
both tables. -/
structure LastAt (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (cur : IoppStage)
    (q : GE × (s.cIn.J → GE)) (rest : List Fmt.RoundView) (n : Nat) (answers : Nat) (c : Ctx)
    (row : GroupRow) (L : GroupLayout) (mask : Option Nat) : Prop where
  /-- what every joint says of the run -/
  run : RunAt V K roots rest answers c
  /-- the program's row on the last group, read in the field, is the claim -/
  claim : stmGk s 1 0 row = q
  /-- fixing the form's lowest variable at 0 picks the entries of the first row -/
  fix : FixLaw row.c [zeroE]
  /-- the one member is not kept -/
  kept : L.kept.getD 0 false = false
  /-- its main row is row 0 of the group's main table -/
  mainFirst : L.mainFirst.getD 0 none = some 0
  /-- its mask row is row 0 of the group's mask table -/
  maskFirst : L.maskFirst.getD 0 none = some 0
  /-- the last tree holds the one member and the masking oracle, which has come -/
  seat : ∃ (o star : Nat) (sh sh' : OracleShape), L.members = #[o] ∧ mask = some star ∧
    OneAndOne sh ∧ OneAndOne sh' ∧ Seat c [o, star] n s.C.a [sh, sh']

/-- The seat of the last tree gives what is asked of the book. -/
theorem lastBook_of_seat (c : Ctx) (o star n logN : Nat) (sh sh' : OracleShape) (h1 : OneAndOne sh)
    (h2 : OneAndOne sh') (h : Seat c [o, star] n logN [sh, sh']) :
    ∃ (t : Nat) (tree : Tree) (xo xs : Oracle), tree.number = n ∧
      LastBook c o star t tree xo xs logN := by
  obtain ⟨t, tree, ht, hn, hlog, hmain, hmask, hpl⟩ := h.tree
  have l0 : 0 < [o, star].length := Nat.zero_lt_succ _
  have l1 : 1 < [o, star].length := Nat.succ_lt_succ (Nat.zero_lt_succ _)
  obtain ⟨xo, hxo, exo⟩ := h.shape 0 l0
  obtain ⟨xs, hxs, exs⟩ := h.shape 1 l1
  have eo : xo.shape = sh := exo
  have es : xs.shape = sh' := exs
  refine ⟨t, tree, xo, xs, hn, ⟨hpl 0 l0, hpl 1 l1, ht, hlog, ?_, ?_, hxo, hxs,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hmain]
    show #[sh.mainRows * sh.mainDeg, sh'.mainRows * sh'.mainDeg] = #[3, 3]
    rw [h1.main, h1.deg, h2.main, h2.deg]
  · rw [hmask]
    show #[sh.maskRows * 3, sh'.maskRows * 3] = #[3, 3]
    rw [h1.mask, h2.mask]
  · rw [eo]; exact h1.main
  · rw [eo]; exact h1.deg
  · rw [eo]; exact h1.mask
  · rw [es]; exact h2.main
  · rw [es]; exact h2.deg
  · rw [es]; exact h2.mask

/-- From `LastAt` at a claim q, after a run of the program's last stage in which no named test has
failed, the library's decision on the base case (`LdwAccept`) accepts at q. Asked: a stage without a
row variable, public facts on sizes, codes and draws, and that the view shows the last written
tree's columns under the key n (`hsh`). -/
theorem lastRuns_at (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (h0 : s.h = 0)
    (g0 : s.g = 0) (hza : s.Z.a ≤ s.C.a) (ha : s.C.a ≤ 32) (ride : Bool) (cur : IoppStage)
    (hK : StageCodes s cur K) (dS dL dB : PQ.RD) (mS : (wRound dS).Msg)
    (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (τB : Tr (PQ.uL (ckP .two) [dL, dB])) (rest : List Fmt.RoundView) (q : GE × (s.cIn.J → GE)) (n : Nat)
    (hsh : Shows V n (treeCol dS mS)) {nB : ℕ} (hB : SendsDraws dB nB 0 s.t s.C.a) :
    LastRuns ride cur (LastAt V K roots s cur q (PQ.rvSL (ckP .two) [dL, dB] τB ++ rest) n)
      (LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) q) q.1
        (s.cIn.T (wordIn s (lastColW dS mS.1))) (s.cIn.T (wordMk s (lastMk dS mS.1)))
        (lst (sentW dL τB.1) 0) (gOne _ (valsOf dL τB.2.1)) (shownW s (sentW dB τB.2.2.1))
        (gPos s.C.a s.t _ (valsOf dB τB.2.2.2.1))) := by
  intro answers c row L mask c' hJ hrun hfail
  obtain ⟨o, star, sh, sh', hL, rfl, k1, k2, hseat⟩ := hJ.seat
  obtain ⟨cd, hcd, hC⟩ := hK.base
  have hlog : cd.logN = s.C.a := congrArg (·.a) hC
  obtain ⟨t, tree, xo, xs, hn, hb⟩ := lastBook_of_seat c o star n s.C.a sh sh' k1 k2 hseat
  obtain ⟨x1, xc, xd⟩ := claim_of_stmGk s row
  rw [hJ.claim] at x1 xc xd
  refine ioppLast_view s h0 g0 hza ha answers ride cur row L o star hL dS dL dB mS.1 hW hN τB.1
    τB.2.1 τB.2.2.1 τB.2.2.2.1 rest c c' hJ.run.onView.dry hJ.run.pending hrun hfail hB cd
    (by rw [hJ.run.codes]; exact hcd) hC (by rw [hJ.run.codes]; exact hK.mask) q x1 xc xd hJ.fix
    t tree xo xs (by rw [hlog]; exact hb) ?_ hJ.kept hJ.mainFirst hJ.maskFirst
  intro e he hk
  rw [hn, hJ.run.onView.first, Nat.sub_zero] at hk
  exact treeCol_some _ _ _ _ (hsh e (hJ.run.onView.opened e he) hk)

end OnBytes.Slice

#print axioms OnBytes.Slice.lastBook_of_seat
#print axioms OnBytes.Slice.lastRuns_at
