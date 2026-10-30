-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Wr.lean: the state of the reduction T for batches, and lemmas on admissible
adversaries of the lifetime experiment. (Words of this library: lean/GLOSSARY.md.)

For the scheme of Compile/Batch/Star.lean and the lifetime experiment of
Compile/Batch/SpecLifeStar.lean.
The reduction itself is `wrapBP` of Compile/Batch/PubWr.lean with the programs of
Compile/Batch/Mirror.lean (`theWrapBP`), on the state `WτB` of this file.
It keeps the state of the experiment of Rom/DeferLate.lean itself: the table from which it answers
all oracle queries, its secret strings, the queries that it has yet to write into the table. It
never queries an oracle of the challenger behind it. It is told, of a batch, the adversary's own
requests only.
At the setup it calls the lifetime experiment once and makes the trees and the proof strings of Test
and of Link from what that experiment returns.
For a batch with own requests it samples the copy, and unless that copy has served s1 batches, it
calls the lifetime experiment with the own requests and makes the proof strings from what it
returns.
If the copy has served s1 batches, that batch alone is rejected: the reduction's reply is the empty
list, no call is made, and later batches are served. (In the experiment of the definition the
simulator that is made from the reduction, `GlueB.simOf`, fills the list up: each own request of
that batch gets one fixed proof, (0, zeros, none, none), which holds no proof string; on such a
proof V of Compile/Batch/Star.lean returns false by its definition.)
For a batch without own requests it does nothing.

  `lifeAdmB_succ`   `LifeAdmB` at n gives `LifeAdmB` at n + 1
  `lifeAdmB_bind_quiet`, `lifeAdmB_bind_halt`
      `LifeAdmB` of a program without calls and queries followed by an admissible one; of an
      admissible one followed by a function of its output
  `length_ownX_le`, `mem_pairs_of_mem_ownX`
      the own requests of a batch are no more than its pairs, and each is the request of a pair

Notation: `LifeAdmB ok s1 B c b n` (Compile/Batch/SpecLifeStar.lean): "(Life): one setup, first;
then at most s1 batches on each copy, at most n in all, each with at most maxBatchSize requests, all allowed. c
counts the batches on each copy."; `ok`: of type `X → Prop`; `b`: a `Bool`; copies: the head of
Compile/Batch/Star.lean; own requests: `Batch.ownX` (ZKCP/Gen.lean): "The instances of the
adversary's own slots, in order."; a program without calls and queries: `Adv.Quiet`
(Rom/LateAdv.lean).

This file does not define the reduction and does not prove that it makes an admissible adversary of
the lifetime experiment: see `wrapBP` and `lifeAdmB_wrapGP` in Compile/Batch/PubWr.lean.
-/
import Compile.Batch.ChallL
import Compile.Batch.SpecLifeStar
import Compile.Step1_life2_Wr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall SCall GAdm asW)
open Compile.BatchLife (LifeOutB LifeInB BRet LifeAdmB)
open Compile.Lifetime (Sess)
open Compile.DefC (virtL)
open Compile.Life2 (advBind_assoc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the reduction's private state: the key, the number of the setup's tokens, the number of batches
of each copy; and the state of the experiment of Rom/DeferLate.lean (`LSt`) -/
abbrev WτB (W : QueryLayout lam L) : Type := Option (WKey lam L × ℕ × (ℕ → ℕ)) × LSt (spec lam W.K L)

variable (W : QueryLayout lam L) (p : Params)
  (cpW : Sess L.offline → List (Sess L.link) → Lp lam W.K L (IVK lam L × WKey lam L))
  (ppW : WKey lam L → List X → ℕ → BRet L → Lp lam W.K L (List (Prf lam L)))



/-! ## Admissibility -/

section Adm

variable {S : OSpec} {α β : Type} (ok : X → Prop) (s1 : ℕ)

theorem lifeAdmB_succ (B : Adv S (LifeOutB X) (LifeInB L) α) :
    ∀ (c : ℕ → ℕ) (b : Bool) (n : ℕ), LifeAdmB ok s1 B c b n → LifeAdmB ok s1 B c b (n + 1) := by
  induction B with
  | halt a => exact fun _ _ _ _ => trivial
  | sample m k ih => exact fun c b n h r => ih r c b n (h r)
  | query o q k ih => exact fun c b n h r => ih r c b n (h r)
  | call m k ih =>
    intro c b n h
    rcases m with ⟨⟩ | ⟨j, xs⟩
    · simp only [LifeAdmB] at h ⊢
      exact ⟨h.1, fun a => ih a c true n (h.2 a)⟩
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [LifeAdmB] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun a => ih a _ b n (h.2.2.2.2 a)⟩

/-- a program without calls and queries, and then an admissible one -/
theorem lifeAdmB_bind_quiet (P : Adv S (LifeOutB X) (LifeInB L) α)
    (hP : P.Quiet) (f : α → Adv S (LifeOutB X) (LifeInB L) β) (c : ℕ → ℕ)
    (b : Bool) (n : ℕ) (h : ∀ a, LifeAdmB ok s1 (f a) c b n) :
    LifeAdmB ok s1 (P.bind f) c b n := by
  induction P with
  | halt a => exact h a
  | sample m k ih => exact fun r => ih r (hP r)
  | query o q k _ => exact hP.elim
  | call m k _ => exact hP.elim

theorem lifeAdmB_bind_halt (P : Adv S (LifeOutB X) (LifeInB L) α) (g : α → β) :
    ∀ (c : ℕ → ℕ) (b : Bool) (n : ℕ),
      LifeAdmB ok s1 P c b n → LifeAdmB ok s1 (P.bind fun a => .halt (g a)) c b n := by
  induction P with
  | halt a => exact fun _ _ _ _ => trivial
  | sample m k ih => exact fun c b n h r => ih r c b n (h r)
  | query o q k ih => exact fun c b n h r => ih r c b n (h r)
  | call m k ih =>
    intro c b n h
    rcases m with ⟨⟩ | ⟨j, xs⟩
    · simp only [Adv.bind, LifeAdmB] at h ⊢
      exact ⟨h.1, fun a => ih a c true n (h.2 a)⟩
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [Adv.bind, LifeAdmB] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun a => ih a _ b n (h.2.2.2.2 a)⟩

end Adm

theorem length_ownX_le (b : ZKCP.Gen.Batch X Unit) : b.ownX.length ≤ b.pairs.length := by
  simp only [ZKCP.Gen.Batch.ownX, ZKCP.Gen.Batch.pairs, List.length_map]
  exact List.length_filter_le _ _

theorem mem_pairs_of_mem_ownX {b : ZKCP.Gen.Batch X Unit} {x : X} (h : x ∈ b.ownX) :
    ∃ xw ∈ b.pairs, xw.1 = x := by
  simp only [ZKCP.Gen.Batch.ownX, List.mem_map, List.mem_filter] at h
  obtain ⟨s, ⟨hs, -⟩, rfl⟩ := h
  exact ⟨(s.1, s.2.1), List.mem_map.2 ⟨s, hs, rfl⟩, rfl⟩

end Compile.Batch
