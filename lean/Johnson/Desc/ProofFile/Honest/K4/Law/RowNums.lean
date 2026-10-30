-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RowNums.lean: the first section of Law/SlotsTrue.lean, cut out so
that what reads the row's numbers need not stand over what reads a run.

What is here. The row of the feed-forward layers' own rounds (kind K4) part by part, and for each
part that sends values, how many rounds and how many spent coins lie in front of it: public.

  `k4RowIn_all`, `k4Tail`, `k4RowIn_at`   the row whole; behind its quiet parts in front; a part by
      its number.
  `foldl_plains`, `ownRun_shapes`, `k4SumSeen_nums`   the coins of a sumcheck's first run, by shape.
  `k4Tail_moves`, `k4Tail_coins`, `k4_moves_at`, `k4_coins_at`, `k4_moves_a`, `k4_moves_b`,
      `k4_coins_a`, `k4_coins_b`   the parts' rounds and coins as lists, and their sums.
  `K4RowNums`, `k4_row_nums`   **the row's numbers.**

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends ownSlots)

/-! ## 1 The row whole, and its numbers -/

/-- **The row at the small input, part by part.** -/
theorem k4RowIn_all (Q : K4Pub) :
    k4RowIn Q = List.replicate (k0 Q.g) k4Quiet ++
      [k4Scalars Q (ledNS Q.P.y.h.xl * Q.P.y.NI) wSums (k0 Q.g), k4Quiet,
       k4Sum Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares (k0 Q.g + 2), k4Quiet,
       k4Scalars Q (ledNP Q.P.y.h.xl * Q.P.y.NI) rowProducts (k0 Q.g + 4),
       k4Sum Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) maskRowRun jobRows
         (k0 Q.g + 5),
       k4Sum Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms (k0 Q.g + 6), k4Quiet,
       k4SumSeen Q (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) jobStack (k0 Q.g + 8),
       k4Sum Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated (k0 Q.g + 9), k4Quiet, k4Quiet,
       k4Sum Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 (k0 Q.g + 12), k4Quiet,
       (if Q.g == 0 then k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)
        else k4Quiet),
       k4Sum Q (k4PlainShape Q.P.wsLay.lk 1 1) indexMaskRun jobMerge (k0 Q.g + 15)] := by
  rcases k0_cases Q.g with ⟨hg, hk⟩ | ⟨hg, hk⟩
  · rw [hk]
    unfold k4RowIn k4Sorts
    rw [hg]
    rfl
  · rw [hk]
    unfold k4RowIn k4Sorts
    rw [hg]
    rfl

/-- The row behind its quiet parts in front. -/
def k4Tail (Q : K4Pub) : List (Part Unit K4In Unit) :=
  [k4Scalars Q (ledNS Q.P.y.h.xl * Q.P.y.NI) wSums (k0 Q.g), k4Quiet,
   k4Sum Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares (k0 Q.g + 2), k4Quiet,
   k4Scalars Q (ledNP Q.P.y.h.xl * Q.P.y.NI) rowProducts (k0 Q.g + 4),
   k4Sum Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) maskRowRun jobRows
     (k0 Q.g + 5),
   k4Sum Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms (k0 Q.g + 6), k4Quiet,
   k4SumSeen Q (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) jobStack (k0 Q.g + 8),
   k4Sum Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated (k0 Q.g + 9), k4Quiet, k4Quiet,
   k4Sum Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 (k0 Q.g + 12), k4Quiet,
   (if Q.g == 0 then k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)
    else k4Quiet),
   k4Sum Q (k4PlainShape Q.P.wsLay.lk 1 1) indexMaskRun jobMerge (k0 Q.g + 15)]

/-- Part number k0 + j of the row is number j of that list. -/
theorem k4RowIn_at (Q : K4Pub) (j : Nat) : (k4RowIn Q)[k0 Q.g + j]? = (k4Tail Q)[j]? := by
  have l : (List.replicate (k0 Q.g) k4Quiet).length = k0 Q.g := List.length_replicate
  rw [k4RowIn_all, List.getElem?_append_right (by rw [l]; omega), l, Nat.add_sub_cancel_left]
  rfl

/-- Two for each of n variables that are summed plainly, of degree bound 3. -/
theorem foldl_plains : ∀ (n k : Nat),
    (List.replicate n (Var.plain 3)).foldl (fun n v => n + (v.d - 1)) k = k + 2 * n
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.replicate_succ, List.foldl_cons, foldl_plains n]
    show k + (3 - 1) + 2 * n = k + 2 * (n + 1)
    omega

/-- How many coins the first run of each of the three shapes of sumcheck holds. -/
theorem ownRun_shapes (mu lt lam dY n : Nat) :
    ownRun (k4LevelShape mu) = ownOf 0 mu 2 ∧ ownRun (k4TokenShape lt dY n) = ownOf 1 lt dY ∧
      ownRun (k4PlainShape lam dY n) = ownOf 0 lam dY := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ownRun_level]
    unfold ownOf
    omega
  · rw [ownRun_token]
    unfold ownOf
    omega
  · show 0 + ownSlots (List.replicate lam (Var.plain 3) ++ [Var.point zeroE (dY + 1)]) = _
    unfold ownSlots ownOf
    rw [List.foldl_append, foldl_plains]
    show 0 + (1 + 2 * lam + (dY + 1 - 1)) = _
    omega

/-- The sumcheck that reads what was shown: its rounds and its coins, as `k4Sum`'s. -/
theorem k4SumSeen_nums (Q : K4Pub) (sh : Call) (job : K4Pub → K4In → Pts → Array OnBytes.E →
    Option Job) (i : Nat) (e : Ends) (he : sh.ends = some e) :
    (k4SumSeen Q sh job i).moves.length = sh.vs.length + 3 ∧
      coinsIn (k4SumSeen Q sh job i) = ownRun sh + e.n := by
  refine ⟨?_, ?_⟩
  · unfold k4SumSeen
    rw [SumLaw.sumPart_moves]
    refine (List.length_map _).trans ?_
    rw [SumLaw.sumGs_count]
    show sh.vs.length + (match sh.ends with
      | none => 1
      | some _ => 3) = _
    rw [he]
  · show (((runName maskRowRun (k4Addr Q i) "sum", (⟨0, ownRun sh⟩ : Due)) ::
      endRuns (runName maskRowRun (k4Addr Q i) "ends") sh.ends).map (·.2.e)).sum = _
    rw [he]
    simp [endRuns]

/-- The rounds of that list's parts. -/
theorem k4Tail_moves (Q : K4Pub) : (k4Tail Q).map (·.moves.length) =
    [1, 1, Q.P.rd.muV + 3, 1, 1, Q.P.y.h.lt + 3, Q.P.y.h.lt + 3, 1, Q.hp.lamS + 3, Q.P.rd.muH + 3,
      1, 1, Q.P.rd.muH2 + 3, 1, 1, Q.P.wsLay.lk + 3] := by
  have e14 : (if Q.g == 0 then k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)
      else k4Quiet).moves.length = 1 := by
    rcases k0_cases Q.g with ⟨hg, _⟩ | ⟨hg, _⟩
    · rw [if_pos hg]
      rfl
    · rw [if_neg (by rw [hg]; exact Bool.false_ne_true)]
      rfl
  have j1 := k4Sum_moves Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares (k0 Q.g + 2) ⟨2, 2⟩ rfl
  have j2 := k4Sum_moves Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) maskRowRun
    jobRows (k0 Q.g + 5) ⟨2, _⟩ rfl
  have j3 := k4Sum_moves Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms
    (k0 Q.g + 6) ⟨1, _⟩ rfl
  have j4 := (k4SumSeen_nums Q (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) jobStack
    (k0 Q.g + 8) ⟨2, _⟩ rfl).1
  have j5 := k4Sum_moves Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated (k0 Q.g + 9) ⟨2, 2⟩ rfl
  have j6 := k4Sum_moves Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 (k0 Q.g + 12) ⟨2, 2⟩ rfl
  have j7 := k4Sum_moves Q (k4PlainShape Q.P.wsLay.lk 1 1) indexMaskRun jobMerge (k0 Q.g + 15)
    ⟨1, 1⟩ rfl
  simp only [k4LevelShape, k4TokenShape, k4PlainShape, List.length_replicate]
    at j1 j2 j3 j4 j5 j6 j7
  unfold k4Tail
  simp only [List.map_cons, List.map_nil, k4LevelShape, k4TokenShape, k4PlainShape, e14, j1, j2, j3,
    j4, j5, j6, j7]
  rfl

/-- The coins that that list's parts spend. -/
theorem k4Tail_coins (Q : K4Pub) : (k4Tail Q).map coinsIn =
    [ledNS Q.P.y.h.xl * Q.P.y.NI, 0, ownOf 0 Q.P.rd.muV 2 + 2, 0, ledNP Q.P.y.h.xl * Q.P.y.NI,
      ownOf 1 Q.P.y.h.lt 2 + ledNO Q.P.y.h.xl * Q.P.y.NI, ownOf 1 Q.P.y.h.lt 1 + nEndT Q.P.y, 0,
      ownOf 0 Q.hp.lamS 2 + nStack Q.P Q.hp Q.g, ownOf 0 Q.P.rd.muH 2 + 2, 0, 0,
      ownOf 0 Q.P.rd.muH2 2 + 2, 0, (if Q.g == 0 then 1 else 0), ownOf 0 Q.P.wsLay.lk 1 + 1] := by
  have e14 : coinsIn (if Q.g == 0 then k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)
      else k4Quiet) = (if Q.g == 0 then 1 else 0) := by
    split <;> rfl
  have j1 := k4Sum_coins Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares (k0 Q.g + 2) ⟨2, 2⟩ rfl
  have j2 := k4Sum_coins Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) maskRowRun
    jobRows (k0 Q.g + 5) ⟨2, _⟩ rfl
  have j3 := k4Sum_coins Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms
    (k0 Q.g + 6) ⟨1, _⟩ rfl
  have j4 := (k4SumSeen_nums Q (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) jobStack
    (k0 Q.g + 8) ⟨2, _⟩ rfl).2
  have j5 := k4Sum_coins Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated (k0 Q.g + 9) ⟨2, 2⟩ rfl
  have j6 := k4Sum_coins Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 (k0 Q.g + 12) ⟨2, 2⟩ rfl
  have j7 := k4Sum_coins Q (k4PlainShape Q.P.wsLay.lk 1 1) indexMaskRun jobMerge (k0 Q.g + 15)
    ⟨1, 1⟩ rfl
  rw [(ownRun_shapes Q.P.rd.muV 0 0 0 0).1] at j1
  rw [(ownRun_shapes 0 Q.P.y.h.lt 0 2 _).2.1] at j2
  rw [(ownRun_shapes 0 Q.P.y.h.lt 0 1 _).2.1] at j3
  rw [(ownRun_shapes 0 0 Q.hp.lamS 2 _).2.2] at j4
  rw [(ownRun_shapes Q.P.rd.muH 0 0 0 0).1] at j5
  rw [(ownRun_shapes Q.P.rd.muH2 0 0 0 0).1] at j6
  rw [(ownRun_shapes 0 0 Q.P.wsLay.lk 1 1).2.2] at j7
  have hq : coinsIn k4Quiet = 0 := rfl
  have hs : ∀ n f i, coinsIn (k4Scalars Q n f i) = n := fun n _ _ => Nat.add_zero n
  unfold k4Tail
  simp only [List.map_cons, List.map_nil, e14, j1, j2, j3, j4, j5, j6, j7, hq, hs]

/-- **For each part that sends such values: the rounds and the spent coins in front of it.** m: the
rounds in front; c: the coins in front; W, P, E: the parts that send the norms' sums, the row
products, the embedding's value; 1 to 6: the sumchecks. The rounds' numbers are the verifier's
(Law/SlotsUnder.lean). THE COINS' NUMBERS ARE THE SLOTS' OF `K4Nums`, COUNTED FROM 0:
slot = n + coin. -/
structure K4RowNums (Q : K4Pub) : Prop where
  mW : movesTo (k4RowIn Q) (k0 Q.g) = k0 Q.g
  cW : spentTo (k4RowIn Q) (k0 Q.g) = 0
  m1 : movesTo (k4RowIn Q) (k0 Q.g + 2) = rJ1 Q.g
  c1 : spentTo (k4RowIn Q) (k0 Q.g + 2) = ledNS Q.P.y.h.xl * Q.P.y.NI
  mP : movesTo (k4RowIn Q) (k0 Q.g + 4) = rowsRound Q.P Q.g
  cP : spentTo (k4RowIn Q) (k0 Q.g + 4) =
    spentTo (k4RowIn Q) (k0 Q.g + 2) + ownOf 0 Q.P.rd.muV 2 + 2
  m2 : movesTo (k4RowIn Q) (k0 Q.g + 5) = rJ2 Q.P Q.g
  c2 : spentTo (k4RowIn Q) (k0 Q.g + 5) =
    spentTo (k4RowIn Q) (k0 Q.g + 4) + ledNP Q.P.y.h.xl * Q.P.y.NI
  m3 : movesTo (k4RowIn Q) (k0 Q.g + 6) = rJ3 Q.P Q.g
  c3 : spentTo (k4RowIn Q) (k0 Q.g + 6) =
    spentTo (k4RowIn Q) (k0 Q.g + 5) + ownOf 1 Q.P.y.h.lt 2 + ledNO Q.P.y.h.xl * Q.P.y.NI
  m4 : movesTo (k4RowIn Q) (k0 Q.g + 8) = rJ4 Q.P Q.g
  c4 : spentTo (k4RowIn Q) (k0 Q.g + 8) =
    spentTo (k4RowIn Q) (k0 Q.g + 6) + ownOf 1 Q.P.y.h.lt 1 + nEndT Q.P.y
  m5 : movesTo (k4RowIn Q) (k0 Q.g + 9) = rJ5 Q.P Q.hp Q.g
  c5 : spentTo (k4RowIn Q) (k0 Q.g + 9) =
    spentTo (k4RowIn Q) (k0 Q.g + 8) + ownOf 0 Q.hp.lamS 2 + nStack Q.P Q.hp Q.g
  m6 : movesTo (k4RowIn Q) (k0 Q.g + 12) = rJ6 Q.P Q.hp Q.g
  c6 : spentTo (k4RowIn Q) (k0 Q.g + 12) =
    spentTo (k4RowIn Q) (k0 Q.g + 9) + ownOf 0 Q.P.rd.muH 2 + 2
  mE : movesTo (k4RowIn Q) (k0 Q.g + 14) = rE Q.P Q.hp Q.g
  cE : spentTo (k4RowIn Q) (k0 Q.g + 14) =
    spentTo (k4RowIn Q) (k0 Q.g + 12) + ownOf 0 Q.P.rd.muH2 2 + 2
  /-- at least three coins are spent from the embedding's place in the row on -/
  more : spentTo (k4RowIn Q) (k0 Q.g + 14) + 2 < spentTo (k4RowIn Q) (k4RowIn Q).length

/-- The rounds in front of part number k0 + j. -/
theorem k4_moves_at (Q : K4Pub) (j : Nat) : movesTo (k4RowIn Q) (k0 Q.g + j) =
    k0 Q.g + (((k4Tail Q).map (·.moves.length)).take j).sum := by
  rw [k4RowIn_all, movesTo_quiet]
  show _ + (((k4Tail Q).take j).map (·.moves.length)).sum = _
  rw [List.map_take]

/-- The coins in front of part number k0 + j. -/
theorem k4_coins_at (Q : K4Pub) (j : Nat) : spentTo (k4RowIn Q) (k0 Q.g + j) =
    (((k4Tail Q).map coinsIn).take j).sum := by
  rw [k4RowIn_all, spentTo_quiet]
  show (((k4Tail Q).take j).map coinsIn).sum = _
  rw [List.map_take]

/-- The rounds in front of the first five of the nine parts. -/
theorem k4_moves_a (Q : K4Pub) :
    movesTo (k4RowIn Q) (k0 Q.g) = k0 Q.g ∧ movesTo (k4RowIn Q) (k0 Q.g + 2) = rJ1 Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 4) = rowsRound Q.P Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 5) = rJ2 Q.P Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 6) = rJ3 Q.P Q.g := by
  have m0 := k4_moves_at Q 0
  have m2 := k4_moves_at Q 2
  have m4 := k4_moves_at Q 4
  have m5 := k4_moves_at Q 5
  have m6 := k4_moves_at Q 6
  rw [k4Tail_moves] at m0 m2 m4 m5 m6
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at m0 m2 m4 m5 m6
  unfold rJ3 rJ2 rJ1 rowsRound
  refine ⟨m0, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The rounds in front of the other four. -/
theorem k4_moves_b (Q : K4Pub) :
    movesTo (k4RowIn Q) (k0 Q.g + 8) = rJ4 Q.P Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 9) = rJ5 Q.P Q.hp Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 12) = rJ6 Q.P Q.hp Q.g ∧
    movesTo (k4RowIn Q) (k0 Q.g + 14) = rE Q.P Q.hp Q.g := by
  have m8 := k4_moves_at Q 8
  have m9 := k4_moves_at Q 9
  have m12 := k4_moves_at Q 12
  have m14 := k4_moves_at Q 14
  rw [k4Tail_moves] at m8 m9 m12 m14
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at m8 m9 m12 m14
  unfold rE rJ6 rJ5 rJ4 rJ3 rJ2 rowsRound
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The coins in front of the first five of the nine parts. -/
theorem k4_coins_a (Q : K4Pub) :
    spentTo (k4RowIn Q) (k0 Q.g) = 0 ∧
    spentTo (k4RowIn Q) (k0 Q.g + 2) = ledNS Q.P.y.h.xl * Q.P.y.NI ∧
    spentTo (k4RowIn Q) (k0 Q.g + 4) =
      spentTo (k4RowIn Q) (k0 Q.g + 2) + ownOf 0 Q.P.rd.muV 2 + 2 ∧
    spentTo (k4RowIn Q) (k0 Q.g + 5) =
      spentTo (k4RowIn Q) (k0 Q.g + 4) + ledNP Q.P.y.h.xl * Q.P.y.NI ∧
    spentTo (k4RowIn Q) (k0 Q.g + 6) =
      spentTo (k4RowIn Q) (k0 Q.g + 5) + ownOf 1 Q.P.y.h.lt 2 + ledNO Q.P.y.h.xl * Q.P.y.NI := by
  have c0 := k4_coins_at Q 0
  have c2 := k4_coins_at Q 2
  have c4 := k4_coins_at Q 4
  have c5 := k4_coins_at Q 5
  have c6 := k4_coins_at Q 6
  rw [k4Tail_coins] at c0 c2 c4 c5 c6
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at c0 c2 c4 c5 c6
  refine ⟨c0, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The coins in front of the other four, and that at least three follow. -/
theorem k4_coins_b (Q : K4Pub) :
    spentTo (k4RowIn Q) (k0 Q.g + 8) =
      spentTo (k4RowIn Q) (k0 Q.g + 6) + ownOf 1 Q.P.y.h.lt 1 + nEndT Q.P.y ∧
    spentTo (k4RowIn Q) (k0 Q.g + 9) =
      spentTo (k4RowIn Q) (k0 Q.g + 8) + ownOf 0 Q.hp.lamS 2 + nStack Q.P Q.hp Q.g ∧
    spentTo (k4RowIn Q) (k0 Q.g + 12) =
      spentTo (k4RowIn Q) (k0 Q.g + 9) + ownOf 0 Q.P.rd.muH 2 + 2 ∧
    spentTo (k4RowIn Q) (k0 Q.g + 14) =
      spentTo (k4RowIn Q) (k0 Q.g + 12) + ownOf 0 Q.P.rd.muH2 2 + 2 ∧
    spentTo (k4RowIn Q) (k0 Q.g + 14) + 2 < spentTo (k4RowIn Q) (k4RowIn Q).length := by
  have len : (k4RowIn Q).length = k0 Q.g + 16 := by
    rw [k4RowIn_all, List.length_append, List.length_replicate]
    rfl
  have c6 := k4_coins_at Q 6
  have c8 := k4_coins_at Q 8
  have c9 := k4_coins_at Q 9
  have c12 := k4_coins_at Q 12
  have c14 := k4_coins_at Q 14
  have c16 := k4_coins_at Q 16
  rw [k4Tail_coins] at c6 c8 c9 c12 c14 c16
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at c6 c8 c9 c12 c14 c16
  have hk : 2 ≤ ownOf 0 Q.P.wsLay.lk 1 := by
    unfold ownOf
    omega
  rw [len]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The row's numbers.** Public. -/
theorem k4_row_nums (Q : K4Pub) : K4RowNums Q :=
  { mW := (k4_moves_a Q).1, cW := (k4_coins_a Q).1
    m1 := (k4_moves_a Q).2.1, c1 := (k4_coins_a Q).2.1
    mP := (k4_moves_a Q).2.2.1, cP := (k4_coins_a Q).2.2.1
    m2 := (k4_moves_a Q).2.2.2.1, c2 := (k4_coins_a Q).2.2.2.1
    m3 := (k4_moves_a Q).2.2.2.2, c3 := (k4_coins_a Q).2.2.2.2
    m4 := (k4_moves_b Q).1, c4 := (k4_coins_b Q).1
    m5 := (k4_moves_b Q).2.1, c5 := (k4_coins_b Q).2.1
    m6 := (k4_moves_b Q).2.2.1, c6 := (k4_coins_b Q).2.2.1
    mE := (k4_moves_b Q).2.2.2, cE := (k4_coins_b Q).2.2.2.1
    more := (k4_coins_b Q).2.2.2.2 }

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4RowIn_all
#print axioms ProofFile.Honest.K4.k4RowIn_at
#print axioms ProofFile.Honest.K4.foldl_plains
#print axioms ProofFile.Honest.K4.ownRun_shapes
#print axioms ProofFile.Honest.K4.k4SumSeen_nums
#print axioms ProofFile.Honest.K4.k4Tail_moves
#print axioms ProofFile.Honest.K4.k4Tail_coins
#print axioms ProofFile.Honest.K4.k4_moves_at
#print axioms ProofFile.Honest.K4.k4_coins_at
#print axioms ProofFile.Honest.K4.k4_moves_a
#print axioms ProofFile.Honest.K4.k4_moves_b
#print axioms ProofFile.Honest.K4.k4_coins_a
#print axioms ProofFile.Honest.K4.k4_coins_b
#print axioms ProofFile.Honest.K4.k4_row_nums
