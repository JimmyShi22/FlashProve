-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverFront.lean: lemmas that prove the routine part of the
hypothesis `hfront` of `debt_busy` (Honest/Law/CoverBusy.lean). That hypothesis speaks of the walk
just before a sub-protocol `b`. It asks four things: that the sub-protocols still to be asked are
`b` and those after it, that no round of `b` has been collected yet, the number of the chain's first
tree, and a condition `P` on the earlier challenges and the verifier's state. The first two follow
from how a walk starts; the third is `hft`. With these lemmas only `P` is left. No sub-protocol of
the protocol is named here.

They use `front_stand` (Honest/Law/CoverPay.lean) and `walk_len` (Honest/Law/RunAtFile.lean).

  1  `front_facts`   the walk just before a sub-protocol that has a round
  2  `debt_busy_P`   `debt_busy`, with a hypothesis on `P` alone in the place of `hfront`
  3  `debt_marks`   a sub-protocol that has marks at its place and no fall near it

A fall is near a sub-protocol if it is at that sub-protocol's place, or at the place of one of the
sub-protocols without a round that follow it directly, up to the next one that has a round
(`groupOf`, Honest/Law/CoverNone.lean).

Limits.
  * The lemmas cover a sub-protocol that has a round and has a gated sub-protocol after it.
  * `hX` (every start of the chain's walk comes from `ChainProgress.start` with the prover's run in hand and
    a verifier's state, at some columns handed) and `hft` (the number of the first tree is the same
    at every start) are hypotheses.
  * `hX` is met at a file's first and shared chain; not at the second chain where an earlier chain
    can reject (the head of Honest/Law/CoverPay.lean says why).
  * The lemmas are applied to no description here.
  * No number follows from them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverBusy
import Johnson.Desc.ProofFile.Honest.Law.CoverPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- Just before a sub-protocol `b` that has a round, the walk still has to ask `b` and the
sub-protocols after it, and has collected no round of `b`. `A`: the sub-protocols before `b`;
`t`: those after it. -/
theorem front_facts (all : List (Block S Cl)) (skip : Nat)
    (X : List Fmt.Drawn → ChainAt S Cl W Y)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    {A : List (Block S Cl)} {b : Block S Cl} {t : List (Block S Cl)} (hb : all = A ++ b :: t)
    (hr : b.rounds ≠ []) {fr : List Fmt.Drawn} {a z : ChainProgress S Cl W Y}
    (h2 : (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length)
    (y1 : (X (fr.take skip)).start = some a)
    (y2 : walk (X (fr.take skip)).lay
      ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
      .ok z) : z.todo = b :: t ∧ z.own = [] := by
  obtain ⟨m₀, s₀, _, g1, g2⟩ := hX _ a y1
  have hw := walk_len _ _ _ _ _ y2
  exact front_stand _ all A t b g1 g2 hb (List.length_pos_of_ne_nil hr) y2
    (by rw [← hw, h2, Nat.zero_add])

/-- `debt_busy` with a hypothesis on `P` alone (`hP`) in the place of `hfront`. -/
theorem debt_busy_P (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds))) {A : List (Block S Cl)}
    {b b' : Block S Cl} {B : List (Block S Cl)} (e : bs = A ++ b :: b' :: B)
    (hr : b.rounds ≠ []) {ft : Nat} (hft : ∀ base, (X base).lay.firstTree = ft)
    (PM : List Fmt.Drawn → Prop) (P : List Fmt.Drawn → S → Prop) (qM : Mark → ℝ≥0∞)
    (qF : Fall S → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb PM (qM mk))
    (reps : List (Fall S))
    (hF : ∀ g ∈ reps, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g ft b (b' :: B ++ rest) dsb [] P (qF g))
    (hin : ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ rest), f.place = d.place) →
      ∃ g ∈ reps, ∀ fr s' own, P fr s' → localFall [f] ft (b :: (b' :: B ++ rest)) s' own →
        localFall [g] ft (b :: (b' :: B ++ rest)) s' own)
    (hPM : ∀ fr, skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → PM fr)
    (hP : ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' → P fr s')
    (hp : ((ms.filter fun m => m.place == b.place).map qM).sum + (reps.map qF).sum ≤
      p (0 + A.length)) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
      (0 + (A.flatMap (·.rounds)).length)
      ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
      (if (b' :: B).isEmpty then tail else []) (b' :: B).isEmpty := by
  have hb : all = A ++ b :: (b' :: B ++ rest) := by
    rw [hall, e, List.append_assoc, List.cons_append, List.cons_append]
  refine debt_busy C all bs rest fs ms skip X p tail ds hfit e PM P qM qF hM reps hF hin hPM
    (fun fr a z s' h1 h2 h3 h4 y1 y2 y3 => ?_) hp
  obtain ⟨e1, e2⟩ := front_facts all skip X hX hb hr h2 y1 y2
  exact ⟨e1, e2, hft _, hP fr a z s' h1 h2 h3 h4 y1 y2 y3⟩

/-- The bound at a sub-protocol that has marks at its place and no fall near it: the sum of the
marks' numbers. -/
theorem debt_marks (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds))) {A : List (Block S Cl)}
    {b b' : Block S Cl} {B : List (Block S Cl)} (e : bs = A ++ b :: b' :: B)
    (hr : b.rounds ≠ []) {ft : Nat} (hft : ∀ base, (X base).lay.firstTree = ft)
    (PM : List Fmt.Drawn → Prop) (qM : Mark → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb PM (qM mk))
    (hfar : ∀ d ∈ groupOf b (b' :: B ++ rest), ∀ f ∈ fs, f.place ≠ d.place)
    (hPM : ∀ fr, skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → PM fr)
    (hp : ((ms.filter fun m => m.place == b.place).map qM).sum ≤ p (0 + A.length)) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
      (0 + (A.flatMap (·.rounds)).length)
      ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
      (if (b' :: B).isEmpty then tail else []) (b' :: B).isEmpty :=
  debt_busy_P C all bs rest fs ms skip X p tail hX hall ds hfit e hr hft PM (fun _ _ => True) qM
    (fun _ => 0) hM [] (fun _ hg => by cases hg)
    (fun f hf ⟨d, hd, he⟩ => absurd he (hfar d hd f hf)) hPM
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) (by rw [List.map_nil, List.sum_nil, add_zero]; exact hp)

end ProofFile.Honest

#print axioms ProofFile.Honest.front_facts
#print axioms ProofFile.Honest.debt_busy_P
#print axioms ProofFile.Honest.debt_marks
