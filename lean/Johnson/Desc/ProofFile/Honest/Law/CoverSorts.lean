-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSorts.lean: one lemma that proves the bounds of all gated
sub-protocols of a chain (`LocalDebts`, Honest/Law/CoverHeld.lean) from statements about single
falls and marks, and asks for the statements about falls only where they are needed. Statements
about falls are asked only at a sub-protocol that has a round and whose place the test `seatF`
accepts. At a sub-protocol whose place only `seatM` accepts, statements about its marks are enough.
It is general in the chain, save `hX`, which a file's first chain meets (`at₁_from`,
Honest/Law/CoverEnd.lean) and the second, where an earlier chain can reject, does not (see
Honest/Law/CoverPay.lean). No sub-protocol of the protocol is named here.

The lemma applies `localDebts_seated` (Honest/Law/CoverSeated.lean) and proves the bound at each
busy sub-protocol by `debt_busy_P` or by `debt_marks` (Honest/Law/CoverFront.lean). That no fall is
near a sub-protocol whose place `seatF` rejects is `group_noFall` (Honest/Law/CoverGroup.lean).
`localDebts_cards` (Honest/Law/CoverCards.lean; not in the sealed library) is another form that
asks for more.

  1  `localDebts_sorts`   the bounds of one chain

The arguments. `seatF`, `seatM`: two tests on a place (for the first chain `fallSeat` and
`markSeat`, Honest/Law/CoverSeats.lean). A sub-protocol is busy if `seatM` accepts its place, or if
`seatF` accepts its place and it has a round. `hX`: every start of the walk comes from `ChainProgress.start`
with the prover's state and a verifier's state, at some columns handed. `hmr`: a sub-protocol whose
place `seatM` accepts has a round. `hend`: the last gated sub-protocol is not busy. `hft`: the
number of the first tree is the same at every start of the walk. The arguments after `hft` give, for
each sub-protocol, what the statements about it may assume, their numbers, and the falls that are
counted.

Limits.
  * The lemma is applied to no description here, and none of its hypotheses is proved here.
  * No number follows from them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSeated
import Johnson.Desc.ProofFile.Honest.Law.CoverFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

set_option maxHeartbeats 1000000 in
/-- The bounds of all gated sub-protocols of one chain. Statements about falls (`hF`, `hin`, `hP`,
`hp₁`) are asked where `seatF` accepts the place and the sub-protocol has a round. Where `seatF`
rejects the place the marks' numbers alone are added up (`hp₂`). -/
theorem localDebts_sorts (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds))) (seatF seatM : Place → Bool)
    (hfs : ∀ f ∈ fs, seatF f.place = true)
    (hsil : ∀ A b B, bs = A ++ b :: B → seatM b.place = false →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms b.place fr (drawnT C _ ρ) = none)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seatF d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ seatF c.place = true)
    (hrest : ∀ d ∈ rest, seatF d.place = false)
    (hlast : ∀ A b, bs = A ++ [b] → b.rounds = [] → tail = [])
    (hend : ∀ A b, bs = A ++ [b] →
      ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])))
    (hmr : ∀ b ∈ bs, seatM b.place = true → b.rounds ≠ [])
    {ft : Nat} (hft : ∀ base, (X base).lay.firstTree = ft)
    (PM : Block S Cl → List Fmt.Drawn → Prop) (qM : Block S Cl → Mark → ℝ≥0∞)
    (hM : ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ mk ∈ ms.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ fr, skip ≤ fr.length → (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → PM b fr)
    (P : Block S Cl → List Fmt.Drawn → S → Prop) (qF : Block S Cl → Fall S → ℝ≥0∞)
    (reps : Block S Cl → List (Fall S))
    (hF : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ g ∈ reps b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g ft b (b' :: B ++ rest) dsb [] (P b) (qF b g))
    (hin : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ rest), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, P b fr s' →
        localFall [f] ft (b :: (b' :: B ++ rest)) s' own →
        localFall [g] ft (b :: (b' :: B ++ rest)) s' own)
    (hP : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' → P b fr s')
    (hp₁ : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ((ms.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p (0 + A.length))
    (hp₂ : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = false →
      ((ms.filter fun m => m.place == b.place).map (qM b)).sum ≤ p (0 + A.length)) :
    LocalDebts C all fs ms skip X p tail (silentQ ms skip bs) bs 0 0 ds := by
  have key : ∀ (A : List (Block S Cl)) (b b' : Block S Cl) (B' : List (Block S Cl)),
      bs = A ++ b :: b' :: B' →
      (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])) →
      DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
        (0 + (A.flatMap (·.rounds)).length)
        ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
        (if (b' :: B').isEmpty then tail else []) (b' :: B').isEmpty := by
    intro A b b' B' e hb
    have hr : b.rounds ≠ [] := by
      rcases hb with h | h
      · exact hmr b (by rw [e]; simp) h
      · exact h.2
    cases hsf : seatF b.place with
    | true =>
      exact debt_busy_P (A := A) (b := b) (b' := b') (B := B') (ft := ft) C all bs rest fs ms skip X
        p tail hX hall ds hfit e hr hft (PM b) (P b) (qM b) (qF b) (hM A b b' B' e) (reps b)
        (hF A b b' B' e hsf hr) (hin A b b' B' e hsf hr) (hPM A b b' B' e)
        (hP A b b' B' e hsf hr) (hp₁ A b b' B' e hsf hr)
    | false =>
      exact debt_marks (A := A) (b := b) (b' := b') (B := B') (ft := ft) C all bs rest fs ms skip X
        p tail hX hall ds hfit e hr hft (PM b) (qM b) (hM A b b' B' e)
        (group_noFall all seatF (fun c => seatF c.place = true) H fs hfs A b (b' :: B' ++ rest)
          (by rw [hall, e, List.append_assoc, List.cons_append, List.cons_append]) hsf
          (fun (h : seatF b.place = true) => by rw [hsf] at h; cases h))
        (hPM A b b' B' e) (hp₂ A b b' B' e hsf)
  refine localDebts_seated C all bs rest fs ms skip X p tail hX hall ds hfit.length_eq seatF seatM
    hfs hsil H hrest hlast ?_
  intro A b B e hb
  cases B with
  | nil => exact absurd hb (hend A b e)
  | cons b' B' => exact key A b b' B' e hb

end ProofFile.Honest

#print axioms ProofFile.Honest.localDebts_sorts
