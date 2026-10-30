-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineChainNum.lean: the counts of the Fiat-Shamir chains of a batch add up, round
by round (words of this library: lean/GLOSSARY.md).

For `Spec.safeChainT0` (Compile/Batch/DisciplineProve.lean): the marked queries of one round and the
bound `MCh` for the rounds that are left (Compile/Batch/DisciplineCnt.lean) add up to at most `MCh`
with this round, for each of the four kinds of rounds of `chainT` (Compile/Batch/Prover.lean): a
local round; a shared round in format (F5) (`Head`, Compile/Batch/Oracles.lean); the joining round;
a shared round without format (at the start or after the later local rounds:
Compile/Batch/Prover.lean). Arithmetic only. A round may have proof-of-work bits: its Fiat-Shamir
query is a search of at most moreOf .. + 1 attempts, counted by `MFb` (one at `fb t`, one at each
ghost name `fbw t k`, k < moreOf ..); in `MCh` the ghost name `fbw t k` has the count `cTry k`
(Compile/Batch/Counts.lean).
-/
import Compile.Batch.DisciplineCnt
import Compile.Batch.DisciplineSum

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {r : Round} {s : Shape}

namespace Num

theorem joins_cons_lo {a : RAnn r} (A : RoundSplits s) (hk : a.kind = .lo) :
    joins (r :: s) (a, A) = joins s A := by
  simp only [joins, hk]

theorem joins_cons_sh {a : RAnn r} (A : RoundSplits s) (hk : a.kind = .sh) :
    joins (r :: s) (a, A) = 1 := by
  simp only [joins, hk]

theorem jn_afterLo {a : RAnn r} (A : RoundSplits s) (hk : a.kind = .lo) (ph : PhT) :
    jn ph.afterLo s A = jn ph (r :: s) (a, A) := by
  cases ph <;> simp only [jn, PhT.afterLo, joins_cons_lo A hk]

theorem fb_step (Ns n : ℕ) : Ns * 1 + (Ns + 1) * n ≤ (Ns + 1) * (n + 1) := by
  have : (Ns + 1) * (n + 1) = (Ns + 1) * n + (Ns + 1) := by ring
  omega

theorem fb_step1 (Ns n : ℕ) : 1 + (Ns + 1) * n ≤ (Ns + 1) * (n + 1) := by
  have : (Ns + 1) * (n + 1) = (Ns + 1) * n + (Ns + 1) := by ring
  omega

end Num

open Num

/-- A local round. -/
theorem MCh_lo (t : Tag) (ph : PhT) (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (Ns : ℕ) (hk : a.kind = .lo) (o : OracleName) :
    Ns * MLo lam K L t w.depthJ (moreOf w.grJ) o + MCh t ph.afterLo s A W Ns o ≤
      MCh t ph (r :: s) (a, A) (w, W) Ns o := by
  cases o with
  | leaf => simp [MLo, MFb, MCh, cnt1, cTrees]
  | node => simp [MLo, MFb, MCh, cnt1, cTrees]
  | rleaf => simp [MLo, MFb, MCh, cnt1, jn_afterLo A hk ph]
  | rnode => simp [MLo, MFb, MCh, cnt1, jn_afterLo A hk ph]
  | fb t' =>
    by_cases h : t' = t
    · subst h
      simpa [MLo, MFb, MCh, cnt1] using fb_step Ns s.length
    · simp [MLo, MFb, MCh, cnt1, h]
  | fbw t' k =>
    by_cases h : t' = t
    · subst h
      show Ns * (0 + 0 + (if t' = t' then (if k < moreOf w.grJ then 1 else 0) else 0)) +
          (if t' = t' then cTry k Ns s A W else 0) ≤
        (if t' = t' then
            Ns * (if k < moreOf w.grJ then 1 else 0) +
              (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W
          else 0)
      rw [if_pos rfl, if_pos rfl, if_pos rfl, Nat.zero_add]
      omega
    · simp [MLo, MFb, MCh, cnt1, h]
  | g t' => simp [MLo, MFb, MCh, cnt1, jn_afterLo A hk ph]
  | ann => simp [MLo, MFb, MCh, cnt1]
  | other => simp [MLo, MFb, MCh, cnt1]

/-- A shared round in format (F5). -/
theorem MCh_f5 (t : Tag) (tk0 tl : Tok) (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (Ns : ℕ) (o : OracleName) :
    (cnt1 (S := spec lam K L) OracleName.leaf (2 ^ w.depth0) o +
          cnt1 (S := spec lam K L) OracleName.node (2 ^ w.depth0) o + MFb t (moreOf w.gr0) o) +
        MCh t (.shr tl) s A W Ns o ≤
      MCh t (.shr tk0) (r :: s) (a, A) (w, W) Ns o := by
  cases o with
  | leaf => simp [MFb, MCh, cnt1, cTrees]
  | node => simp [MFb, MCh, cnt1, cTrees]
  | rleaf => simp [MFb, MCh, cnt1, jn]
  | rnode => simp [MFb, MCh, cnt1, jn]
  | fb t' =>
    by_cases h : t' = t
    · subst h
      simpa [MFb, MCh, cnt1] using fb_step1 Ns s.length
    · simp [MFb, MCh, cnt1, h]
  | fbw t' k =>
    by_cases h : t' = t
    · subst h
      show (0 + 0 + (if t' = t' then (if k < moreOf w.gr0 then 1 else 0) else 0)) +
          (if t' = t' then cTry k Ns s A W else 0) ≤
        (if t' = t' then
            Ns * (if k < moreOf w.grJ then 1 else 0) +
              (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W
          else 0)
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      omega
    · simp [MFb, MCh, cnt1, h]
  | g t' => simp [MFb, MCh, cnt1, jn]
  | ann => simp [MFb, MCh, cnt1]
  | other => simp [MFb, MCh, cnt1]

/-- The joining round. -/
theorem MCh_join (t : Tag) (tl : Tok) (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (Ns : ℕ) (hk : a.kind = .sh) (o : OracleName) :
    Ns * (cnt1 (S := spec lam K L) OracleName.leaf (2 ^ w.depthJ) o +
            cnt1 (S := spec lam K L) OracleName.node (2 ^ w.depthJ) o +
            cnt1 (S := spec lam K L) (OracleName.g t) 1 o) +
        (cnt1 (S := spec lam K L) OracleName.rleaf Ns o + cnt1 (S := spec lam K L) OracleName.rnode Ns o) +
        (cnt1 (S := spec lam K L) OracleName.leaf (2 ^ w.depth0) o +
          cnt1 (S := spec lam K L) OracleName.node (2 ^ w.depth0) o) +
        MFb t (moreOf w.gr0) o + MCh t (.shr tl) s A W Ns o ≤
      MCh t .loc (r :: s) (a, A) (w, W) Ns o := by
  cases o with
  | leaf => simp [MFb, MCh, cnt1, cTrees]
  | node => simp [MFb, MCh, cnt1, cTrees]
  | rleaf => simp [MFb, MCh, cnt1, jn, joins_cons_sh A hk]
  | rnode => simp [MFb, MCh, cnt1, jn, joins_cons_sh A hk]
  | fb t' =>
    by_cases h : t' = t
    · subst h
      simpa [MFb, MCh, cnt1] using fb_step1 Ns s.length
    · simp [MFb, MCh, cnt1, h]
  | fbw t' k =>
    by_cases h : t' = t
    · subst h
      show Ns * (0 + 0 + 0) + (0 + 0) + (0 + 0) +
          (if t' = t' then (if k < moreOf w.gr0 then 1 else 0) else 0) +
          (if t' = t' then cTry k Ns s A W else 0) ≤
        (if t' = t' then
            Ns * (if k < moreOf w.grJ then 1 else 0) +
              (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W
          else 0)
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      omega
    · simp [MFb, MCh, cnt1, h]
  | g t' =>
    by_cases h : t' = t
    · subst h
      simp [MFb, MCh, cnt1, jn, joins_cons_sh A hk]
    · have h' : ¬ OracleName.g t' = OracleName.g t := fun e => h (OracleName.g.inj e)
      simp [MFb, MCh, cnt1, h]
      exact fun e => absurd e h'
  | ann => simp [MFb, MCh, cnt1]
  | other => simp [MFb, MCh, cnt1]

/-- A shared round without format. -/
theorem MCh_skip (t : Tag) (ph : PhT) (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (Ns : ℕ) (hk : a.kind = .sh) (hph : ph = .first ∨ ph = .aft) (o : OracleName) :
    MCh t ph s A W Ns o ≤ MCh t ph (r :: s) (a, A) (w, W) Ns o := by
  have hj : jn ph s A ≤ jn ph (r :: s) (a, A) := by
    rcases hph with rfl | rfl
    · simp only [jn, joins_cons_sh A hk]
      exact Sum.joins_le_one s A
    · exact le_rfl
  cases o with
  | leaf => simp [MCh, cTrees]
  | node => simp [MCh, cTrees]
  | rleaf => exact Nat.mul_le_mul_right _ hj
  | rnode => exact Nat.mul_le_mul_right _ hj
  | fb t' =>
    by_cases h : t' = t
    · subst h
      simp only [MCh, if_true, List.length_cons]
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)
    · simp [MCh, h]
  | fbw t' k =>
    by_cases h : t' = t
    · subst h
      show (if t' = t' then cTry k Ns s A W else 0) ≤
        (if t' = t' then
            Ns * (if k < moreOf w.grJ then 1 else 0) +
              (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W
          else 0)
      rw [if_pos rfl, if_pos rfl]
      omega
    · simp [MCh, h]
  | g t' =>
    by_cases h : t' = t
    · subst h
      simp only [MCh, if_true]
      exact Nat.mul_le_mul_right _ hj
    · simp [MCh, h]
  | ann => exact le_rfl
  | other => exact le_rfl

end Compile.Batch.Disc
