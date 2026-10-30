-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SoundAsIOPClearing.lean: tools for "uniform challenges with the bits of proof of work set to 0"
(Clearing, Hiop/SoundAsIOP.lean): how a clearing of the whole run is laid together from clearings of
the three parts, and the clearing that the wires of a list of rounds declare. Definitions with their
proofs. No protocol is named here.

  Clearing.identity, Clearing.app          nothing is cleared; two lists of rounds in a row.
  Err.EachAtMost                           every number of a list is at most m.
  sumOfProbabilities_timesByRound_le       every error at most c as a probability, at most m challenges
                                           cleared to one: the sum is at most (rounds) * (m * c).
  HolographicProtocol.wholeRunClearing, HolographicProtocol.wholeRunToOne  the whole run: the identity on the five added rounds (two
                                           points, two answers, the naming of a request), a clearing
                                           on each of the three parts.
  wholeRunDraw_cleared                     what that does to the verifier's draw: the two points stay,
                                           each part's challenges are cleared by that part's clearing.
  WireRB.work, RoundsQueryLayout.mostWork             the number of test bits that a round's wire declares; the
                                           largest in a list of rounds.
  RoundsQueryLayout.clearing, RoundsQueryLayout.clearedToOne     the wires' clearing; 2^(the round's test bits), by round.
  RoundsQueryLayout.cleared_clearing                  it IS RoundsQueryLayout.zero (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean).
  RoundsQueryLayout.clearing_atMostToOne              under the wires' laws (RoundsQueryLayout.OKG: the test bits are a lens)
                                           at most 2^(test bits) challenges are cleared to one.
  RoundsQueryLayout.pass_zero                         under these laws cleared challenges pass every test.
  GrW.OK.cleared_fibre | cleared_no_fibre  the fibres are equal: a verifier message whose test bits are
                                           0 is the cleared form of exactly 2^b, any other of none.
  RoundsQueryLayout.allWork                           all test bits of a list of rounds together.
  RoundsQueryLayout.cleared_fibre | cleared_no_fibre  the same for the whole of a part's challenges: those that pass
                                           are the cleared form of exactly 2^(all test bits), the others
                                           of none. So uniform challenges, cleared, are uniform on the
                                           challenges that pass: said in counts
                                           (RoundsQueryLayout.ClearedIsUniformOnPassing).
  RoundsQueryLayout.passing_share                     of all challenges of a part one in 2^(all test bits) passes.
  RoundsQueryLayout.exists_zero_ne                    under these laws, where some round has a test bit, some
                                           challenges are not their own cleared form.

Limits. Counting alone: no conditional law is written as a probability. That a verifier rejects where
a test bit is not 0 is not said here (at the public files: E2E/SoundAsIOPWorkIsTheVerifiers.lean). A
wire's number of test bits is what the wire declares: nothing here says that it is small.
-/
import Hiop.SoundAsIOP
import Hiop.SoundAsIOPSum
import Hiop.SoundAsIOPChallenges
import Iop.Carry
import OnBytes.TypedOracleCompiler.Iop.BatchWire

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Iop
open Prob Blocks

/-! ## 1. Clearings -/

/-- Nothing is cleared. -/
def Clearing.identity : (s : Shape) → Clearing s
  | [] => ()
  | _ :: s => (id, Clearing.identity s)

/-- Two lists of rounds in a row. -/
def Clearing.app : {s t : Shape} → Clearing s → Clearing t → Clearing (s ++ t)
  | [], _, _, K' => K'
  | _ :: _, _, (k, K), K' => (k, Clearing.app K K')

theorem Clearing.cleared_identity : ∀ (s : Shape) (ρ : Rho s), (Clearing.identity s).cleared ρ = ρ
  | [], _ => rfl
  | r :: s, (c, ρ) =>
      show ((c, (Clearing.identity s).cleared ρ) : Rho (r :: s)) = (c, ρ) by
        rw [Clearing.cleared_identity s ρ]

theorem Clearing.cleared_app : ∀ {s t : Shape} (K : Clearing s) (K' : Clearing t) (ρ : Rho s)
    (ρ' : Rho t),
    (Clearing.app K K').cleared (Rho.app ρ ρ') = Rho.app (K.cleared ρ) (K'.cleared ρ')
  | [], _, _, _, _, _ => rfl
  | r :: s, t, (k, K), K', (c, ρ), ρ' =>
      show ((k c, (Clearing.app K K').cleared (Rho.app ρ ρ')) : Rho (r :: (s ++ t))) =
          (k c, Rho.app (K.cleared ρ) (K'.cleared ρ')) by
        rw [Clearing.cleared_app K K' ρ ρ']

/-- A property whose members are told apart by a map into a finite type has at most that type's
number of members. -/
theorem cnt_le_card_of_injOn {α β : Type} [Finite α] [Fintype β] (P : α → Prop) (f : α → β)
    (h : ∀ a b, P a → P b → f a = f b → a = b) : cnt P ≤ Fintype.card β := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective (fun x : {a : α // P a} => f x.1)
    fun x y e => Subtype.ext (h x.1 y.1 x.2 y.2 e)

/-- One challenge is "cleared" to one by the identity. -/
theorem cnt_id_eq_le_one {C : Type} [Finite C] (c' : C) : cnt (fun c : C => id c = c') ≤ 1 :=
  (cnt_le_card_of_injOn _ (fun _ => ()) fun a b ha hb _ =>
    (show a = c' from ha).trans (show b = c' from hb).symm).trans (le_of_eq Fintype.card_unit)

theorem Clearing.atMostToOne_identity : ∀ s : Shape,
    (Clearing.identity s).AtMostToOne (Err.ones s)
  | [] => trivial
  | _ :: s => ⟨cnt_id_eq_le_one, Clearing.atMostToOne_identity s⟩

theorem Clearing.AtMostToOne.app : ∀ {s t : Shape} {K : Clearing s} {K' : Clearing t} {M : Err s}
    {M' : Err t}, K.AtMostToOne M → K'.AtMostToOne M' →
    (Clearing.app K K').AtMostToOne (Err.app M M')
  | [], _, _, _, _, _, _, h' => h'
  | _ :: _, _, (_, _), _, (_, _), _, h, h' => ⟨h.1, Clearing.AtMostToOne.app h.2 h'⟩

/-! ## 2. The sum -/

/-- Every number of the list is at most m. -/
def Err.EachAtMost : {s : Shape} → Err s → ℕ → Prop
  | [], _, _ => True
  | _ :: _, (e, ε), m => e ≤ m ∧ Err.EachAtMost ε m

theorem Err.EachAtMost.app : ∀ {s t : Shape} {M : Err s} {M' : Err t} {m : ℕ},
    M.EachAtMost m → M'.EachAtMost m → (Err.app M M').EachAtMost m
  | [], _, _, _, _, _, h' => h'
  | _ :: _, _, (_, _), _, _, h, h' => ⟨h.1, Err.EachAtMost.app h.2 h'⟩

theorem Err.EachAtMost.mono : ∀ {s : Shape} {M : Err s} {m n : ℕ}, m ≤ n →
    M.EachAtMost m → M.EachAtMost n
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, hmn, h => ⟨h.1.trans hmn, Err.EachAtMost.mono hmn h.2⟩

theorem Err.eachAtMost_ones : ∀ (s : Shape) {m : ℕ}, 1 ≤ m → (Err.ones s).EachAtMost m
  | [], _, _ => trivial
  | _ :: s, _, h => ⟨h, Err.eachAtMost_ones s h⟩

/-- Errors at most c as probabilities, multiplied round by round by numbers that are at most m, are at
most m * c. -/
theorem Err.Below.timesByRound : ∀ {s : Shape} {toOne ε : Err s} {m : ℕ} {c : ℝ≥0∞},
    toOne.EachAtMost m → Err.Below ε c → Err.Below (Err.timesByRound toOne ε) ((m : ℝ≥0∞) * c)
  | [], _, _, _, _, _, _ => trivial
  | r :: _, (t, _), (e, _), m, c, hM, hε =>
      ⟨by
        show ((t * e : ℕ) : ℝ≥0∞) ≤ (m : ℝ≥0∞) * c * (Fintype.card r.Chal : ℝ≥0∞)
        rw [Nat.cast_mul, mul_assoc]
        exact mul_le_mul' (Nat.cast_le.2 hM.1) hε.1,
      Err.Below.timesByRound hM.2 hε.2⟩

/-- **The sum at a clearing**: every error at most c as a probability, at most m challenges cleared
to one: at most (number of rounds) * (m * c). -/
theorem sumOfProbabilities_timesByRound_le (s : Shape) (toOne ε : Err s) (m : ℕ) (c : ℝ≥0∞)
    (hM : toOne.EachAtMost m) (hε : Err.Below ε c) :
    (Err.timesByRound toOne ε).sumOfProbabilities ≤ (s.length : ℝ≥0∞) * ((m : ℝ≥0∞) * c) :=
  sumOfProbabilities_le s _ _ (Err.Below.timesByRound hM hε)

/-! ## 3. The whole run -/

variable {Index Request : Type}

namespace HolographicProtocol

/-- **The clearing of the whole run**: the identity on the five added rounds, a clearing on each of
the three parts. -/
def wholeRunClearing (L : HolographicProtocol Index Request) (fill : L.Fill) (offline : Clearing L.offline.shape)
    (link : Clearing L.link.shape) (online : Clearing L.onlineBatch.loc.shape) :
    Clearing (L.wholeRunShape fill) :=
  (id, id,
    Clearing.app (s := L.offline.shape)
      (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))
      offline
      (id, id,
        Clearing.app (s := L.link.shape) (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)
          link (id, online)))

/-- How many challenges are cleared to one, round by round: 1 in the five added rounds. -/
def wholeRunToOne (L : HolographicProtocol Index Request) (fill : L.Fill) (offline : Err L.offline.shape)
    (link : Err L.link.shape) (online : Err L.onlineBatch.loc.shape) : Err (L.wholeRunShape fill) :=
  (1, 1,
    Err.app (s := L.offline.shape)
      (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))
      offline
      (1, 1,
        Err.app (s := L.link.shape) (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)
          link (1, online)))

end HolographicProtocol

theorem wholeRunClearing_atMostToOne (L : HolographicProtocol Index Request) (fill : L.Fill)
    {offline : Clearing L.offline.shape} {link : Clearing L.link.shape}
    {online : Clearing L.onlineBatch.loc.shape} {toOneOffline : Err L.offline.shape}
    {toOneLink : Err L.link.shape} {toOneOnline : Err L.onlineBatch.loc.shape}
    (hT : offline.AtMostToOne toOneOffline) (hL : link.AtMostToOne toOneLink)
    (hB : online.AtMostToOne toOneOnline) :
    (L.wholeRunClearing fill offline link online).AtMostToOne
      (L.wholeRunToOne fill toOneOffline toOneLink toOneOnline) :=
  ⟨cnt_id_eq_le_one, cnt_id_eq_le_one,
    Clearing.AtMostToOne.app (s := L.offline.shape)
      (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) hT
      ⟨cnt_id_eq_le_one, cnt_id_eq_le_one,
        Clearing.AtMostToOne.app (s := L.link.shape)
          (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) hL
          ⟨cnt_id_eq_le_one, hB⟩⟩⟩

theorem wholeRunToOne_eachAtMost (L : HolographicProtocol Index Request) (fill : L.Fill)
    {toOneOffline : Err L.offline.shape} {toOneLink : Err L.link.shape}
    {toOneOnline : Err L.onlineBatch.loc.shape} {m : ℕ} (h1 : 1 ≤ m) (hT : toOneOffline.EachAtMost m)
    (hL : toOneLink.EachAtMost m) (hB : toOneOnline.EachAtMost m) :
    (L.wholeRunToOne fill toOneOffline toOneLink toOneOnline).EachAtMost m :=
  ⟨h1, h1,
    Err.EachAtMost.app (s := L.offline.shape)
      (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) hT
      ⟨h1, h1,
        Err.EachAtMost.app (s := L.link.shape)
          (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) hL ⟨h1, hB⟩⟩⟩

/-- **What the clearing of the whole run does to the verifier's draw**: the two points stay; each
part's challenges are cleared by that part's clearing. -/
theorem wholeRunDraw_cleared (L : HolographicProtocol Index Request) (fill : L.Fill)
    (offline : Clearing L.offline.shape) (link : Clearing L.link.shape)
    (online : Clearing L.onlineBatch.loc.shape) (ρ : Rho (L.wholeRunShape fill)) :
    L.wholeRunDraw fill ((L.wholeRunClearing fill offline link online).cleared ρ) =
      ((L.wholeRunDraw fill ρ).1,
        (offline.cleared (L.wholeRunDraw fill ρ).2.1, link.cleared (L.wholeRunDraw fill ρ).2.2.1,
          online.cleared (L.wholeRunDraw fill ρ).2.2.2)) := by
  obtain ⟨p₁, ⟨⟩, ρ⟩ := ρ
  obtain ⟨a, σ, rfl⟩ : ∃ (a : Rho L.offline.shape) (σ : Rho (L.tableRounds fill ++ (L.link.shape ++
         (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))), ρ = Rho.app a σ :=
    ⟨Rho.fst ρ, Rho.snd (s := L.offline.shape) ρ, (Rho.app_fst_snd (s := L.offline.shape) ρ).symm⟩
  obtain ⟨p₂, ⟨⟩, σ⟩ := σ
  obtain ⟨b, υ, rfl⟩ : ∃ (b : Rho L.link.shape)
      (υ : Rho (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)), σ = Rho.app b υ :=
    ⟨Rho.fst σ, Rho.snd (s := L.link.shape) σ, (Rho.app_fst_snd (s := L.link.shape) σ).symm⟩
  obtain ⟨⟨⟩, c⟩ := υ
  have h₂ : (Clearing.app (s := L.link.shape)
      (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) link (id, online)).cleared
        (Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b ((), c)) =
      Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) (link.cleared b)
        ((), online.cleared c) :=
    Clearing.cleared_app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) link
      (id, online) b ((), c)
  have h₁ : (L.wholeRunClearing fill offline link online).cleared
      ((p₁, (), Rho.app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) a
        (p₂, (), Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b
          ((), c))) : Rho (L.wholeRunShape fill)) =
      (L.wholeRunDraw fill).symm
        ((p₁, p₂), offline.cleared a, link.cleared b, online.cleared c) :=
    congrArg (fun z => ((p₁, (), z) : Rho (L.wholeRunShape fill)))
      ((Clearing.cleared_app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) offline _ a _).trans
        (congrArg (fun z => Rho.app (t := L.tableRounds fill ++ (L.link.shape ++
          (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) (offline.cleared a)
          (p₂, (), z)) h₂))
  have h₀ : ((p₁, (), Rho.app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) a
        (p₂, (), Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b
          ((), c))) : Rho (L.wholeRunShape fill)) =
      (L.wholeRunDraw fill).symm ((p₁, p₂), a, b, c) := rfl
  rw [h₁, h₀, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Iop

/-! ## 4. The clearing that the wires declare -/

namespace TypedOracleCompiler.Iop
open Prob
open _root_.Iop (Shape Round RAnn RoundSplits Rho Err Clearing cnt_le_card_of_injOn cnt_id_eq_le_one)

variable {lam K : ℕ}

/-- The number of test bits (bits of proof of work) that a round's wire declares: of the record that
the kind of the round reads; 0 in a round without a test. -/
def WireRB.work {r : Round} {a : RAnn r} (w : WireRB lam K r a) : ℕ :=
  match a.kind with
  | .lo => match w.grJ with
    | none => 0
    | some g => g.b
  | .sh => match w.gr0 with
    | none => 0
    | some g => g.b

/-- The largest number of test bits of a round. -/
def RoundsQueryLayout.mostWork : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => max w.work (RoundsQueryLayout.mostWork s A W)

/-- **The wires' clearing**: in each round, all test bits set to 0. -/
def RoundsQueryLayout.clearing : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Clearing s
  | [], _, _ => ()
  | _ :: s, (_, A), (w, W) => (w.zero, RoundsQueryLayout.clearing s A W)

/-- 2^(the round's test bits), round by round. -/
def RoundsQueryLayout.clearedToOne : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Err s
  | [], _, _ => ()
  | _ :: s, (_, A), (w, W) => (2 ^ w.work, RoundsQueryLayout.clearedToOne s A W)

/-- **It is RoundsQueryLayout.zero.** -/
theorem RoundsQueryLayout.cleared_clearing : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ρ : Rho s),
    (RoundsQueryLayout.clearing s A W).cleared ρ = RoundsQueryLayout.zero s A W ρ
  | [], _, _, _ => rfl
  | r :: s, (_, A), (w, W), (c, ρ) =>
      show ((w.zero c, (RoundsQueryLayout.clearing s A W).cleared ρ) : Rho (r :: s)) =
          (w.zero c, RoundsQueryLayout.zero s A W ρ) by
        rw [RoundsQueryLayout.cleared_clearing s A W ρ]

/-- Where the test bits are a lens, at most 2^b verifier messages have one cleared form. -/
theorem GrW.OK.cnt_set_le {C P : Type} [Finite C] {g : GrW C P} (h : g.OK) (c' : C) :
    cnt (fun c : C => g.set (fun _ => false) c = c') ≤ 2 ^ g.b := by
  refine (cnt_le_card_of_injOn _ g.tst fun x y hx hy e => ?_).trans (le_of_eq ?_)
  · have hx' : g.set (g.tst x) c' = x := by rw [← hx, h.set_set, h.set_tst]
    have hy' : g.set (g.tst y) c' = y := by rw [← hy, h.set_set, h.set_tst]
    rw [← hx', ← hy', e]
  · rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem WireRB.cnt_zero_le {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OKG)
    (c' : r.Chal) : cnt (fun c : r.Chal => w.zero c = c') ≤ 2 ^ w.work := by
  unfold WireRB.zero WireRB.work
  cases a.kind with
  | lo =>
    cases e : w.grJ with
    | none => exact (cnt_id_eq_le_one c').trans (le_of_eq (pow_zero 2).symm)
    | some g => exact (h.grJ_ok g e).cnt_set_le c'
  | sh =>
    cases e : w.gr0 with
    | none => exact (cnt_id_eq_le_one c').trans (le_of_eq (pow_zero 2).symm)
    | some g => exact (h.gr0_ok g e).cnt_set_le c'

/-- **Under the wires' laws at most 2^(test bits) challenges of a round are cleared to one.** -/
theorem RoundsQueryLayout.clearing_atMostToOne : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    RoundsQueryLayout.OKG s A W → (RoundsQueryLayout.clearing s A W).AtMostToOne (RoundsQueryLayout.clearedToOne s A W)
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), h => ⟨WireRB.cnt_zero_le h.1, RoundsQueryLayout.clearing_atMostToOne s A W h.2⟩

theorem RoundsQueryLayout.clearedToOne_eachAtMost : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    (RoundsQueryLayout.clearedToOne s A W).EachAtMost (2 ^ RoundsQueryLayout.mostWork s A W)
  | [], _, _ => trivial
  | _ :: s, (_, A), (w, W) =>
      ⟨Nat.pow_le_pow_right (by decide) (le_max_left _ _),
        _root_.Iop.Err.EachAtMost.mono (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
          (RoundsQueryLayout.clearedToOne_eachAtMost s A W)⟩

theorem WireRB.pass_zero {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OKG)
    (c : r.Chal) : w.pass (w.zero c) = true := by
  unfold WireRB.pass WireRB.zero
  cases a.kind with
  | lo =>
    cases e : w.grJ with
    | none => rfl
    | some g => exact decide_eq_true ((h.grJ_ok g e).tst_set _ c)
  | sh =>
    cases e : w.gr0 with
    | none => rfl
    | some g => exact decide_eq_true ((h.gr0_ok g e).tst_set _ c)

/-- **Under the wires' laws cleared challenges pass every test.** -/
theorem RoundsQueryLayout.pass_zero : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
    ∀ ρ : Rho s, RoundsQueryLayout.pass s A W (RoundsQueryLayout.zero s A W ρ) = true
  | [], _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), h, (c, ρ) =>
      show (w.pass (w.zero c) && RoundsQueryLayout.pass s A W (RoundsQueryLayout.zero s A W ρ)) = true by
        rw [WireRB.pass_zero h.1 c, RoundsQueryLayout.pass_zero s A W h.2 ρ]; rfl

/-! ### The fibres are equal: uniform challenges, cleared, are uniform on the challenges that pass -/

/-- **Where the test bits are a lens, a verifier message whose test bits are 0 is the cleared form of
exactly 2^b verifier messages.** -/
theorem GrW.OK.cleared_fibre {C P : Type} [Finite C] {g : GrW C P} (h : g.OK) (c' : C)
    (hc : g.tst c' = fun _ => false) :
    cnt (fun c : C => g.set (fun _ => false) c = c') = 2 ^ g.b := by
  have e : {c : C // g.set (fun _ => false) c = c'} ≃ (Fin g.b → Bool) :=
    { toFun := fun x => g.tst x.1
      invFun := fun t => ⟨g.set t c', by rw [h.set_set, ← hc, h.set_tst]⟩
      left_inv := fun ⟨c, hx⟩ => Subtype.ext (by
        show g.set (g.tst c) c' = c
        have h2 : g.set (g.tst c) (g.set (fun _ => false) c) = c := by rw [h.set_set, h.set_tst]
        rw [hx] at h2
        exact h2)
      right_inv := fun t => h.tst_set t c' }
  show Nat.card _ = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

/-- And any other is the cleared form of none. -/
theorem GrW.OK.cleared_no_fibre {C P : Type} [Finite C] {g : GrW C P} (h : g.OK) (c' : C)
    (hc : g.tst c' ≠ fun _ => false) :
    cnt (fun c : C => g.set (fun _ => false) c = c') = 0 :=
  cnt_false fun c e => hc (by rw [← e, h.tst_set])

/-- One round: a challenge that passes is the cleared form of exactly 2^(the round's test bits). -/
theorem WireRB.cleared_fibre {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OKG)
    (c' : r.Chal) (hp : w.pass c' = true) : cnt (fun c : r.Chal => w.zero c = c') = 2 ^ w.work := by
  unfold WireRB.pass at hp
  unfold WireRB.zero WireRB.work
  revert hp
  cases a.kind with
  | lo =>
    intro hp
    cases e : w.grJ with
    | none => exact (cnt_eq_const c').trans (pow_zero 2).symm
    | some g => rw [e] at hp; exact (h.grJ_ok g e).cleared_fibre c' (of_decide_eq_true hp)
  | sh =>
    intro hp
    cases e : w.gr0 with
    | none => exact (cnt_eq_const c').trans (pow_zero 2).symm
    | some g => rw [e] at hp; exact (h.gr0_ok g e).cleared_fibre c' (of_decide_eq_true hp)

/-- All test bits of a list of rounds together. -/
def RoundsQueryLayout.allWork : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => w.work + RoundsQueryLayout.allWork s A W

/-- **The whole of a part's challenges: challenges that pass every test are the cleared form of
exactly 2^(all test bits together) challenges.** -/
theorem RoundsQueryLayout.cleared_fibre : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    RoundsQueryLayout.OKG s A W → ∀ ρ' : Rho s, RoundsQueryLayout.pass s A W ρ' = true →
    cnt (fun ρ : Rho s => RoundsQueryLayout.zero s A W ρ = ρ') = 2 ^ RoundsQueryLayout.allWork s A W
  | [], A, W, _, ρ', _ => by
      haveI : Unique {ρ : Rho [] // RoundsQueryLayout.zero [] A W ρ = ρ'} :=
        ⟨⟨⟨(), rfl⟩⟩, fun _ => Subtype.ext rfl⟩
      exact Nat.card_unique
  | r :: s, (_, A), (w, W), h, (c', ρ'), hp => by
      have hp' : (w.pass c' && RoundsQueryLayout.pass s A W ρ') = true := hp
      rw [Bool.and_eq_true] at hp'
      have e : cnt (fun x : r.Chal × Rho s => w.zero x.1 = c' ∧ RoundsQueryLayout.zero s A W x.2 = ρ') =
          2 ^ w.work * 2 ^ RoundsQueryLayout.allWork s A W :=
        (cnt_and_prod (fun c : r.Chal => w.zero c = c')
          (fun ρ : Rho s => RoundsQueryLayout.zero s A W ρ = ρ')).trans
          (by rw [WireRB.cleared_fibre h.1 c' hp'.1, RoundsQueryLayout.cleared_fibre s A W h.2 ρ' hp'.2])
      refine Eq.trans (cnt_congr fun x => ?_) (e.trans (pow_add 2 _ _).symm)
      exact Prod.ext_iff

/-- **And challenges that do not pass are the cleared form of none.** -/
theorem RoundsQueryLayout.cleared_no_fibre (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (h : RoundsQueryLayout.OKG s A W) (ρ' : Rho s) (hp : RoundsQueryLayout.pass s A W ρ' = false) :
    cnt (fun ρ : Rho s => RoundsQueryLayout.zero s A W ρ = ρ') = 0 :=
  cnt_false fun ρ e => Bool.false_ne_true (hp.symm.trans (e ▸ RoundsQueryLayout.pass_zero s A W h ρ))

/-- **Uniform challenges, cleared, are uniform on the challenges that pass**, said in counts: challenges
that pass are the cleared form of exactly 2^(all test bits together) challenges, the others of none. -/
def RoundsQueryLayout.ClearedIsUniformOnPassing (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : Prop :=
  (∀ ρ' : Rho s, RoundsQueryLayout.pass s A W ρ' = true →
    cnt (fun ρ : Rho s => (RoundsQueryLayout.clearing s A W).cleared ρ = ρ') = 2 ^ RoundsQueryLayout.allWork s A W) ∧
  (∀ ρ' : Rho s, RoundsQueryLayout.pass s A W ρ' = false →
    cnt (fun ρ : Rho s => (RoundsQueryLayout.clearing s A W).cleared ρ = ρ') = 0)

theorem RoundsQueryLayout.clearedIsUniformOnPassing (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (h : RoundsQueryLayout.OKG s A W) : RoundsQueryLayout.ClearedIsUniformOnPassing s A W :=
  ⟨fun ρ' hp => (cnt_congr fun ρ => by rw [RoundsQueryLayout.cleared_clearing]).trans
      (RoundsQueryLayout.cleared_fibre s A W h ρ' hp),
    fun ρ' hp => (cnt_congr fun ρ => by rw [RoundsQueryLayout.cleared_clearing]).trans
      (RoundsQueryLayout.cleared_no_fibre s A W h ρ' hp)⟩

/-- **Of all challenges of a part, one in 2^(all test bits together) passes.** -/
theorem RoundsQueryLayout.passing_share (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (h : RoundsQueryLayout.OKG s A W) :
    cnt (fun ρ : Rho s => RoundsQueryLayout.pass s A W ρ = true) * 2 ^ RoundsQueryLayout.allWork s A W =
      Fintype.card (Rho s) := by
  have e : ∀ ρ' : Rho s, cnt (fun ρ : Rho s => RoundsQueryLayout.zero s A W ρ = ρ') =
      if RoundsQueryLayout.pass s A W ρ' = true then 2 ^ RoundsQueryLayout.allWork s A W else 0 := fun ρ' => by
    split
    · exact RoundsQueryLayout.cleared_fibre s A W h ρ' ‹_›
    · exact RoundsQueryLayout.cleared_no_fibre s A W h ρ' (Bool.eq_false_iff.2 ‹_›)
  rw [← sum_cnt_fiber (RoundsQueryLayout.zero s A W), Finset.sum_congr rfl fun ρ' _ => e ρ', Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, cnt_eq_card_filter]

/-- Where the test bits are a lens and there is a test bit, some verifier message is not its own
cleared form. -/
theorem GrW.OK.exists_set_ne {C P : Type} {g : GrW C P} (h : g.OK) (hb : 0 < g.b) (c : C) :
    ∃ c' : C, g.set (fun _ => false) c' ≠ c' :=
  ⟨g.set (fun _ => true) c, fun e => by
    have h1 := congrArg g.tst e
    rw [h.tst_set, h.tst_set] at h1
    exact Bool.false_ne_true (congrFun h1 ⟨0, hb⟩)⟩

theorem WireRB.exists_zero_ne {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OKG)
    (hb : 0 < w.work) : ∃ c : r.Chal, w.zero c ≠ c := by
  obtain ⟨c⟩ := r.neChal
  unfold WireRB.work at hb
  unfold WireRB.zero
  revert hb
  cases a.kind with
  | lo =>
    intro hb
    cases e : w.grJ with
    | none => rw [e] at hb; exact absurd hb (Nat.lt_irrefl 0)
    | some g => rw [e] at hb; exact (h.grJ_ok g e).exists_set_ne hb c
  | sh =>
    intro hb
    cases e : w.gr0 with
    | none => rw [e] at hb; exact absurd hb (Nat.lt_irrefl 0)
    | some g => rw [e] at hb; exact (h.gr0_ok g e).exists_set_ne hb c

/-- **Under the wires' laws, where some round has a test bit, the clearing is not the identity.** -/
theorem RoundsQueryLayout.exists_zero_ne : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    RoundsQueryLayout.OKG s A W → 0 < RoundsQueryLayout.mostWork s A W → ∃ ρ : Rho s, RoundsQueryLayout.zero s A W ρ ≠ ρ
  | [], _, _, _, hb => absurd hb (Nat.lt_irrefl 0)
  | r :: s, (_, A), (w, W), h, hb => by
      rcases lt_max_iff.1 hb with h1 | h1
      · obtain ⟨c, hc⟩ := WireRB.exists_zero_ne h.1 h1
        obtain ⟨ρ⟩ := _root_.Iop.instNonemptyRho s
        exact ⟨(c, ρ), fun e => hc (congrArg Prod.fst e)⟩
      · obtain ⟨ρ, hρ⟩ := RoundsQueryLayout.exists_zero_ne s A W h.2 h1
        obtain ⟨c⟩ := r.neChal
        exact ⟨(c, ρ), fun e => hρ (congrArg Prod.snd e)⟩

end TypedOracleCompiler.Iop

#print axioms Iop.Clearing.cleared_identity
#print axioms Iop.Clearing.cleared_app
#print axioms Iop.Clearing.atMostToOne_identity
#print axioms Iop.Clearing.AtMostToOne.app
#print axioms Iop.sumOfProbabilities_timesByRound_le
#print axioms Iop.wholeRunClearing_atMostToOne
#print axioms Iop.wholeRunToOne_eachAtMost
#print axioms Iop.wholeRunDraw_cleared
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.cleared_clearing
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.clearing_atMostToOne
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.clearedToOne_eachAtMost
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.pass_zero
#print axioms TypedOracleCompiler.Iop.GrW.OK.cleared_fibre
#print axioms TypedOracleCompiler.Iop.GrW.OK.cleared_no_fibre
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.cleared_fibre
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.cleared_no_fibre
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.clearedIsUniformOnPassing
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.passing_share
#print axioms TypedOracleCompiler.Iop.RoundsQueryLayout.exists_zero_ne
