-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingData.lean: the first three clauses of `DataFront`
(K12/ShapeAll.lean) at the job of the first chain's closing proximity test (`jobL`,
K12/AtProof/JobL.lean), where the sender's text returns. The state holds the carrying message's rows
on the stage's main table, and the one tree's column holds their symbols and the fresh table's.

  `parL`, `carryV`, `plainL`   the sending's numbers; its messages by number, as `treesL` has them;
                               the rows as plain functions
  `FitsAtL`                    the public clauses
  `rowsL_ok`, `treesL_ok`      the job's two texts where the sender's text returns
  `stateAt_L`, `treesAt_L`, `colsAt_L`   the three clauses
  `dataFront_L`                `DataFront`, with its clause on values as a premise

By what. The proofs of `state_one`, `trees_one`, `cols_one` (K12/JobOne.lean), at the sender's own
sending (`K2.sendingPar`): `sent_memAt`, `sent_freshAt` (Johnson/Desc/K12/Honest/SentMember.lean),
`lay_some`, `length_col` (Johnson/Prover/Send/Enc.lean), `groupTrees_colsFrom`
(Johnson/Desc/K12/Honest/FirstAsks.lean).

Hypotheses. hr: the sender's text returns R at the coins that the job's first stage reads: the job
lays zeros where it refuses, and then none of this holds of the honest rows. H: the public clauses.

Limits.
- `FitsAtL` is asked; it is shown at no place here. Its clauses `rows` and `logRows` say that the
  carrying message fills the stage's main table, and `noMask` that it has no mask row: the mask
  table and its tails are then zeros, as `StateAt` asks of a table in no member's block.
- hr is a premise on the closing, which may refuse on the prover's input.
- The clause on values of `DataFront`, that the rows taken in say their claims of these words, is a
  premise of `dataFront_L`. It reads the targets, so it is false at a state that has lost them.
- The door is a letter here. A job with one stand patched is this job at another door.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingJob
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll
import Johnson.Desc.K12.Honest.SentMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TreeLay layTrees)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.First (Plain Seat1 oM oZ logAt widthAt kk)
open Johnson.Prover.Link (PS)
open Johnson.Prover.Send (col lay_some length_col)
open ProofFile.Honest.K12 (TestJob stA PlainRows StateAt ColsAt SeatIs DataFront sent_memAt sent_freshAt
  groupTrees colsFrom groupTrees_colsFrom)

variable {W₀ Rc Xi Tr X : Type}

/-- The numbers of the sending that the finish makes. -/
abbrev parL (p : K2.SwitchPlace) : VerifiableInference.Desc.K1.Par :=
  K2.sendingPar p.sizes.codes (sentL p)

/-- The finish's messages by number, as `treesL` has them, at the carrying message's rows. -/
def carryV (p : K2.SwitchPlace) (R : Johnson.Prover.Send.Rows) (P : PS) :
    ℕ → Johnson.Prover.Send.Rows :=
  fun k => if k == 0 then R
    else if k == (sentL p).size - 1 then { K2.zeroMessage with mask := P.fM, maskTl := P.fT }
    else K2.zeroMessage

/-- **The prover's rows as plain functions**: the carrying message at every member's number; no
mask row; the fresh table of the first stage's state. -/
def plainL (R : Johnson.Prover.Send.Rows) (P : PS) : PlainRows where
  M := fun _ => R.mainE
  T := fun _ => R.mainTlE
  Z := fun _ _ _ => 0
  ZT := fun _ _ _ => 0
  F := P.fM
  FT := P.fT

/-- **The public clauses.** q: the test's parameters. p: the sender's place. Dp: the plain data. s:
the member's seat. u: the tree's place in the book of trees. Ly: the sending's layout. -/
structure FitsAtL (q : P12) (p : K2.SwitchPlace) (Dp : Plain) (s : Seat1) (u : ℕ) (Ly : TreeLay) :
    Prop where
  plan : VerifiableInference.Desc.K1.planOkOwn (parL p) = true
  lay : layTrees (parL p).codes (parL p).sent = some Ly
  two : 1 < (parL p).sent.size
  count : (sentL p).size = 2
  mems : Dp.mems = [s]
  ts : Dp.ts = [u]
  seat : SeatIs (stA q) (parL p) Ly 0 s
  fresh : SeatIs (stA q) (parL p) Ly 1 Dp.fresh
  tree0 : Ly.tree.getD 0 0 = 0
  tree1 : Ly.tree.getD 1 0 = 0
  some0 : 0 < Ly.shapes.size
  at0 : s.t = u
  at1 : Dp.fresh.t = u
  rowsF : Dp.fresh.sh.maskRows = 2 ^ (stA q).h
  deg : s.sh.mainDeg = 3
  noMask : s.sh.maskRows = 0
  rows : s.sh.mainRows = 2 ^ kk (stA q)
  logRows : OnBytes.ceilLog2 (shapeL p).mainRows = kk (stA q)
  first : oM Dp.L 0 = 0
  depth : logAt Dp.book u =
    (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
      default).logN
  width : widthAt Dp.book u = (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth

theorem get_L {q : P12} {p : K2.SwitchPlace} {Dp : Plain} {s : Seat1} {u : ℕ} {Ly : TreeLay}
    (H : FitsAtL q p Dp s u Ly) (j : Fin Dp.mems.length) : Dp.mems.get j = s ∧ j.val = 0 := by
  refine ⟨List.mem_singleton.1 (H.mems ▸ List.get_mem Dp.mems j), ?_⟩
  have hl : Dp.mems.length = 1 := by
    rw [H.mems]
    rfl
  exact Nat.lt_one_iff.1 (lt_of_lt_of_eq j.isLt hl)

section
variable (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
  (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
  (w : Local W₀ Rc Xi Tr) (fr : Front X) (C : ProofFile.Honest.K12.TestCoins) {R : Johnson.Prover.Send.Rows}
  (hr : carryRows D readers closing p w (heardL fr) C.mem = .ok R)
include hr

theorem rowsL_ok : rowsL D readers closing p w fr C.mem =
    { zeroPS with
      tabM := fun i => R.mainE (i % 2 ^ OnBytes.ceilLog2 (shapeL p).mainRows)
        (i / 2 ^ OnBytes.ceilLog2 (shapeL p).mainRows)
      tM := R.mainTlE } := by
  unfold rowsL
  rw [hr]

theorem treesL_ok (P : PS) : treesL D readers closing p w fr C.mem P =
    [((((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
      default).logN, col (parL p) (carryV p R P) 0)] := by
  unfold treesL
  rw [hr]
  rfl

variable {Dp : Plain} {s : Seat1} {u : ℕ} {Ly : TreeLay} (H : FitsAtL q p Dp s u Ly)
include H

/-- **The state holds the carrying message's rows on the main table, and 0 on the mask table.** -/
theorem stateAt_L : StateAt (stA q) Dp
    ((jobL q door D readers closing p).first w fr C)
    (plainL R ((jobL q door D readers closing p).first w fr C)) := by
  have hP : ∀ n, ((jobL q door D readers closing p).first w fr C).tabM n =
      R.mainE (n % 2 ^ kk (stA q)) (n / 2 ^ kk (stA q)) := by
    intro n
    show (rowsL D readers closing p w fr C.mem).tabM n = _
    rw [rowsL_ok D readers closing p w fr C hr, ← H.logRows]
  have hT : ∀ b r, ((jobL q door D readers closing p).first w fr C).tM b r = R.mainTlE b r := by
    intro b r
    show (rowsL D readers closing p w fr C.mem).tM b r = _
    rw [rowsL_ok D readers closing p w fr C hr]
  have hZ : ∀ n, ((jobL q door D readers closing p).first w fr C).tabZ n = 0 := by
    intro n
    show (rowsL D readers closing p w fr C.mem).tabZ n = 0
    rw [rowsL_ok D readers closing p w fr C hr]
    rfl
  have hZT : ∀ b r, ((jobL q door D readers closing p).first w fr C).tZ b r = 0 := by
    intro b r
    show (rowsL D readers closing p w fr C.mem).tZ b r = 0
    rw [rowsL_ok D readers closing p w fr C hr]
    rfl
  have pM : 0 < 2 ^ kk (stA q) := Nat.two_pow_pos _
  refine ⟨fun j i e hi _ => ?_, fun j i r hi _ => ?_, fun j i e hi _ => ?_, fun j i r hi _ => ?_,
    fun b hb hn => ?_, fun b _ _ => ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨g, j0⟩ := get_L H j
    rw [g, H.rows] at hi
    rw [j0, H.first, Nat.zero_add, hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ pM, Nat.div_eq_of_lt hi, Nat.zero_add]
    rfl
  · obtain ⟨-, j0⟩ := get_L H j
    rw [j0, H.first, Nat.zero_add, hT]
    rfl
  · obtain ⟨g, -⟩ := get_L H j
    rw [g, H.noMask] at hi
    exact absurd hi (Nat.not_lt_zero _)
  · obtain ⟨g, -⟩ := get_L H j
    rw [g, H.noMask] at hi
    exact absurd hi (Nat.not_lt_zero _)
  · have hs : 0 < Dp.mems.length := by
      rw [H.mems]
      exact Nat.zero_lt_one
    have h0 := hn ⟨0, hs⟩
    obtain ⟨g, -⟩ := get_L H ⟨0, hs⟩
    rw [g, H.rows] at h0
    refine absurd ?_ h0
    show oM Dp.L 0 ≤ b ∧ b < oM Dp.L 0 + 2 ^ kk (stA q)
    rw [H.first]
    exact ⟨Nat.zero_le _, by omega⟩
  · exact ⟨fun e _ => hZ _, fun r _ => hZT b r⟩

/-- The one tree, read by `colsFrom` at the place u, is the sending's column at tree number 0. -/
theorem colsFrom_L (x : ℕ) :
    colsFrom ((jobL q door D readers closing p).trees₀ w fr C.mem
      ((jobL q door D readers closing p).first w fr C)) Dp.ts u x =
    col (parL p) (carryV p R ((jobL q door D readers closing p).first w fr C)) 0 x := by
  show colsFrom (treesL D readers closing p w fr C.mem
    ((jobL q door D readers closing p).first w fr C)) Dp.ts u x = _
  rw [treesL_ok D readers closing p w fr C hr]
  unfold colsFrom
  rw [H.ts, List.idxOf_cons_self]
  rfl

/-- **The job's tree is the group's.** -/
theorem treesAt_L :
    (jobL q door D readers closing p).trees₀ w fr C.mem
        ((jobL q door D readers closing p).first w fr C) =
      groupTrees Dp.ts (logAt Dp.book)
        (colsFrom ((jobL q door D readers closing p).trees₀ w fr C.mem
          ((jobL q door D readers closing p).first w fr C)) Dp.ts) := by
  refine (groupTrees_colsFrom _ Dp.ts (logAt Dp.book) (by rw [H.ts]; exact List.nodup_singleton u)
    ?_).symm
  show (treesL D readers closing p w fr C.mem
    ((jobL q door D readers closing p).first w fr C)).map (·.1) = _
  rw [treesL_ok D readers closing p w fr C hr, H.ts]
  show [_] = [logAt Dp.book u]
  rw [H.depth]

/-- **The column holds the rows' symbols.** -/
theorem colsAt_L : ColsAt (stA q) Dp
    (colsFrom ((jobL q door D readers closing p).trees₀ w fr C.mem
      ((jobL q door D readers closing p).first w fr C)) Dp.ts)
    (plainL R ((jobL q door D readers closing p).first w fr C)) := by
  obtain ⟨Ly', hL', eL⟩ := lay_some (parL p) H.plan
  obtain rfl : Ly = Ly' := Option.some.inj (H.lay.symm.trans hL')
  have hc := colsFrom_L q door D readers closing p w fr C hr H
  refine ⟨fun u' hu x _ => ?_, fun j x _ => ?_, fun x _ b hb => ?_⟩
  · rw [H.ts] at hu
    obtain rfl := List.mem_singleton.1 hu
    rw [hc, length_col (parL p) _ H.plan 0 x (by rw [eL]; exact H.some0), eL, H.width]
  · obtain ⟨g, j0⟩ := get_L H j
    rw [g, j0, H.at0, hc]
    have k := sent_memAt (parL p) (carryV p R ((jobL q door D readers closing p).first w fr C))
      H.plan Ly H.lay 0 (Nat.lt_trans Nat.zero_lt_one H.two) H.seat
      (plainL R ((jobL q door D readers closing p).first w fr C)) 0 x
      (fun _ _ _ _ => by rw [H.deg]; rfl) (fun _ _ _ _ => by rw [H.deg]; rfl)
      (fun _ _ hi _ => absurd hi (by rw [H.noMask]; exact Nat.not_lt_zero _))
      (fun _ _ hi _ => absurd hi (by rw [H.noMask]; exact Nat.not_lt_zero _))
    rw [H.tree0] at k
    exact k
  · rw [H.at1, hc]
    have e1 : carryV p R ((jobL q door D readers closing p).first w fr C) 1 =
        { K2.zeroMessage with
          mask := ((jobL q door D readers closing p).first w fr C).fM
          maskTl := ((jobL q door D readers closing p).first w fr C).fT } := by
      unfold carryV
      rw [H.count]
      rfl
    have k := sent_freshAt (parL p) (carryV p R ((jobL q door D readers closing p).first w fr C))
      H.plan Ly H.lay 1 H.two H.fresh (plainL R ((jobL q door D readers closing p).first w fr C)) x
      b (by rw [H.rowsF]; exact hb) (fun _ _ => by rw [e1]; rfl) (fun _ _ => by rw [e1]; rfl)
    rw [H.tree1] at k
    exact k

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **`DataFront` at the job**, its clause on values a premise. -/
theorem dataFront_L (hs : ∀ G, (door w fr).st.groups[(door w fr).g]? = some G →
      AllSay rdE (begun (door w fr).st (door w fr).g G) (runRows (door w fr).st G).toList
        (ProofFile.Honest.K12.wordsAt (begun (door w fr).st (door w fr).g G)
          (layoutOf (door w fr).st G)
          (plainL R ((jobL q door D readers closing p).first w fr C)))) :
    DataFront (jobL q door D readers closing p) w fr C Dp
      (colsFrom ((jobL q door D readers closing p).trees₀ w fr C.mem
        ((jobL q door D readers closing p).first w fr C)) Dp.ts)
      (plainL R ((jobL q door D readers closing p).first w fr C)) :=
  ⟨colsAt_L q door D readers closing p w fr C hr H, stateAt_L q door D readers closing p w fr C hr H,
    treesAt_L q door D readers closing p w fr C hr H, hs⟩

end

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.plainL
#print axioms ProofFile.Honest.K12.AtProof.FitsAtL
#print axioms ProofFile.Honest.K12.AtProof.rowsL_ok
#print axioms ProofFile.Honest.K12.AtProof.treesL_ok
#print axioms ProofFile.Honest.K12.AtProof.stateAt_L
#print axioms ProofFile.Honest.K12.AtProof.treesAt_L
#print axioms ProofFile.Honest.K12.AtProof.colsAt_L
#print axioms ProofFile.Honest.K12.AtProof.dataFront_L
