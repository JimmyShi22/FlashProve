-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BeforeO
import Johnson.Desc.BlockSlot
/-
Johnson/Desc/K12/Law/BeforeMore.lean: behind BeforeK12.lean | BeforeO.lean: the pin n3 at numAt; a member with «taken» sources. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  offOf t₁ t₂ c: the number over the file of the first tree of the chain number c (from 0), as numAt counts.
  n3_numAt: THE PIN n3 AT numAt, OFF THE PLAN: under taken_below's premises, the chain's declared rounds preR ++ … with b at preR's end, and c ≤ 2: (c' + 1, n) ∈ p.before ⇒ numAt (rootsOf D.1) (rootsOf D.2.1) c (.taken c' n) < offOf … c + rootsOf preR: the stretch's base.
  word_W: opened_sent's premises are met together at the REAL piW (three sources «taken»: 0 1 · 0 21 · 1 1; the third chain) over TWO MADE-UP CHAINS IN FRONT (one round of 22 roots; one of 2): SentBy's second arm has a member. before_W_short: with 21 roots in the first chain beforeAt says no.
THE CHAINS IN FRONT ARE NOT THE FILE's.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.G.OfPlan (rootsOf)

def offOf (t₁ t₂ c : ℕ) : ℕ := if c = 0 then 0 else if c = 1 then t₁ else t₁ + t₂

theorem n3_numAt {S Cl : Type} (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (preR postR : List Fmt.DeclaredRound) (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR))
    (hlen : preR.length = from' + roundsIn pre) (hc2 : c ≤ 2) (c' n : ℕ)
    (hm : (c' + 1, n) ∈ p.before) :
    numAt (rootsOf D.1) (rootsOf D.2.1) c (.taken c' n) <
      offOf (rootsOf D.1) (rootsOf D.2.1) c + rootsOf preR := by
  have hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head? := by
    obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top p.nums rds hr
    rw [hDs, ← hlen]
    simp
  obtain ⟨h1, h2, h3⟩ := taken_below p rds hr D O c from' pre b post hbef hrd h hD c' n hm
  have e : (chainOf D (c + 1)).take (from' + roundsIn pre) = preR := by
    rw [hDs, ← hlen, List.take_left']
    rfl
  rw [e] at h3
  show (if c' = 0 then 0 else if c' = 1 then rootsOf D.1 else rootsOf D.1 + rootsOf D.2.1) + n < _
  unfold offOf
  rcases Nat.lt_or_ge c' c with hlt | hge
  · have hc' : c' = 0 ∨ c' = 1 := by omega
    rcases hc' with rfl | rfl
    · have g : n < rootsOf D.1 := h2
      have hc0 : c ≠ 0 := by omega
      simp only [if_true, hc0, if_false]
      split <;> omega
    · have g : n < rootsOf D.2.1 := h2
      have hc2' : c = 2 := by omega
      subst hc2'
      simp
      omega
  · obtain rfl : c' = c := by omega
    have := h3 rfl
    omega

end H2K.Made

namespace H2K.Member
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (opened_sent SentBy)

def rN (n : ℕ) : Fmt.DeclaredRound := ⟨{ Fmt.M1.rBat.entry with roots := n, drawE := 0 }, [], []⟩
def bW : Block T12 Unit := proximityTestKind guardedProximityTestParts piW
def dW3 : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound := ([rN 22], [rN 2], bW.rounds)

theorem fixed_W : H2K.FixedBefore.fixedOk piW = true := by decide +kernel
theorem rounds_W : H2U.roundsOfNums piW.nums = some bW.rounds := by decide +kernel
theorem bef_W : bW.before = piW.before := by decide +kernel
theorem before_W : beforeAt dW3 ([], [], []) 2 0 [bW] = true := by decide +kernel
theorem before_W_short :
    beforeAt (([rN 21], [rN 2], bW.rounds) :
      List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) ([], [], []) 2 0 [bW] = false := by
  decide +kernel

theorem word_W :
    (∀ (j : ℕ) (s : Fmt.M1.Stage), j + 1 < piW.nums.stages.length → piW.nums.stages[j]? = some s →
      ∀ r ∈ (bW.rounds.drop (H2K.FixedBefore.foldStart 1 piW.nums.stages j + 1 + s.k)).take 2,
      ∀ o ∈ r.opens, SentBy dW3 2 (0 + roundsIn ([] : List (Block T12 Unit)))
        (0 + roundsIn ([] : List (Block T12 Unit)) +
          (H2K.FixedBefore.foldStart 1 piW.nums.stages j + 1)) o) ∧
    (∀ r ∈ (bW.rounds.drop
        (H2K.FixedBefore.foldStart 1 piW.nums.stages (piW.nums.stages.length - 1))).take 2,
      ∀ o ∈ r.opens, SentBy dW3 2 (0 + roundsIn ([] : List (Block T12 Unit)))
        (0 + roundsIn ([] : List (Block T12 Unit)) +
          H2K.FixedBefore.foldStart 1 piW.nums.stages (piW.nums.stages.length - 1)) o) :=
  opened_sent piW fixed_W bW.rounds rounds_W dW3 ([], [], []) 2 0 [] bW [] bef_W rfl rfl
    before_W [] [] (by simp [chainOf, dW3]) rfl rfl

end H2K.Member

#print axioms H2K.Made.n3_numAt
#print axioms H2K.Member.before_W
#print axioms H2K.Member.before_W_short
#print axioms H2K.Member.word_W
