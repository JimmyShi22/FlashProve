-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSeated.lean: THE DEBTS OF A CHAIN WHOSE FALLS AND MARKS SIT
AT SEATS. `localDebts_sparse` (Honest/Law/CoverSparse.lean) leaves «idle» a letter on the chain's
splits; `group_noFall` (Honest/Law/CoverGroup.lean) speaks of a test on places. Here the two are
joined: seatF, seatM: two tests on a place. A member is busy where seatM takes its place, or seatF
takes it and the member has a round; every other member is idle: so a member without a round at a
seat of falls is idle too: a fall that sits there is held at the gate of the member with a round in
front of it. WHERE EVERY FALL OF THE LIST SITS AT A PLACE THAT seatF TAKES, the marks at a place
that seatM does not take are silent at typed messages, and every member without a round at a seat of
falls has right in front of it a member with a round at a seat of falls: `LocalDebts` is owed at the
busy members alone.

WHAT THIS IS. A lemma on definitions of ours: two calls. General in the chain, save hX, and in the
two tests (at the first chain: `fallSeat`, `markSeat`, Honest/Law/CoverSeats.lean). None of the
library's goals.

  `localDebts_seated`

THE PREMISES, AND WHOSE THEY ARE AT THE FIRST CHAIN. hfs: the gatherer's, on the owners' words.
hsil: the gatherer's: no owner's mark stands there; our own marks are silent at typed messages. H: a
closed fact on the written places with one fact on the members' rounds. hrest: no seat of falls
behind the gated members. hlast: the last gated member has a round, or no fixed challenge stands
behind it. hbusy: THE DEBT AT EVERY BUSY MEMBER: the content. hX: the walk starts as a frame's
start, from some state, at some columns handed (at the first chain: `at₁_from`,
Honest/Law/CoverEnd.lean; not at the second chain where an earlier chain can reject: see
Honest/Law/CoverPay.lean). hall, hlen: the cut and the data's length.

Limits. Called here at no description. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSparse
import Johnson.Desc.ProofFile.Honest.Law.CoverGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- **THE DEBTS ARE OWED AT THE BUSY MEMBERS ALONE.** -/
theorem localDebts_seated (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hlen : ds.length = (bs.flatMap (·.rounds)).length) (seatF seatM : Place → Bool)
    (hfs : ∀ f ∈ fs, seatF f.place = true)
    (hsil : ∀ A b B, bs = A ++ b :: B → seatM b.place = false →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms b.place fr (drawnT C _ ρ) = none)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seatF d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ seatF c.place = true)
    (hrest : ∀ d ∈ rest, seatF d.place = false)
    (hlast : ∀ A b, bs = A ++ [b] → b.rounds = [] → tail = [])
    (hbusy : ∀ A b B, bs = A ++ b :: B →
      (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])) →
      DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
        (0 + (A.flatMap (·.rounds)).length)
        ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
        (if B.isEmpty then tail else []) B.isEmpty) :
    LocalDebts C all fs ms skip X p tail (silentQ ms skip bs) bs 0 0 ds := by
  have far : ∀ d : Block S Cl, seatF d.place = false → ∀ f ∈ fs, f.place ≠ d.place := by
    intro d hd f hf e
    rw [← e, hfs f hf] at hd
    cases hd
  have sm : ∀ b : Block S Cl,
      ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])) →
      seatM b.place = false := by
    intro b hz
    cases h : seatM b.place with
    | false => rfl
    | true => exact absurd (Or.inl h) hz
  have sf : ∀ b : Block S Cl,
      ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])) → b.rounds ≠ [] →
      seatF b.place = false := by
    intro b hz hr
    cases h : seatF b.place with
    | false => rfl
    | true => exact absurd (Or.inr ⟨h, hr⟩) hz
  refine localDebts_sparse C all bs rest fs ms skip X p tail hX hall ds hlen
    (fun _ b _ => ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])))
    (fun A b B e hz => hsil A b B e (sm b hz)) (fun A b e _ hr => hlast A b e hr) ?_ ?_
    (fun A b B e hz => hbusy A b B e (Classical.not_not.1 hz))
  · intro A b b' B e hz hr
    have h1 := sf b hz hr
    exact group_noFall all seatF (fun c => seatF c.place = true) H fs hfs A b (b' :: B ++ rest)
      (by rw [hall, e, List.append_assoc, List.cons_append, List.cons_append]) h1
      (fun (h : seatF b.place = true) => by rw [h1] at h; cases h)
  · intro A b _ hz hr d hd
    rcases List.mem_cons.1 hd with rfl | hd'
    · exact far d (sf d hz hr)
    · exact far d (hrest d hd')

end ProofFile.Honest

#print axioms ProofFile.Honest.localDebts_seated
