-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSeat.lean: A STATED SHARE THAT IS HELD AGAINST ITS TEST PAYS
THE OWNER's SENTENCE. `Held` (Honest/Law/SharesHeld.lean) and `Fall.HeldOn`
(Honest/Law/SharesFalls.lean) say that a stated share is held against its own test, over one
member's rounds' typed messages. No law spent them. Here: for a fall that is SEATED AT A MEMBER WITH
A ROUND, and at no member without a round right behind it: `Fall.HeldOn` gives `FallDebt`
(Honest/Law/CoverJoin.lean) at that member, AT THE STATED SHARE's VALUE; for a mark: `Held` at every
front that P lets in gives `MarkDebt` at the mark's stated share's value. So these two forms land,
and with them a stated share enters a law.

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own measure. None of
the library's goals.

  `fallOf_one`, `fallDebt_of_heldOn`, `markDebt_of_held`

WHY THE WIDE EVENT IS NO WIDER THERE. With just the member's rounds, `frontsOf` lists the member, at
the state in front and its own challenges, and the members without a round right behind it: a fall
that sits at the member alone is asked at the first entry alone: its test reads the state in front
and the challenges: the rounds' items and the columns are idle.

MET FOR NOTHING. P₀ := False. A stated share of 1 or more. Limits. A fall at a member WITHOUT a
round is not served: its test is asked at a state behind another member's step. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl : Type}

/-- One fall alone says something at a place only if it sits there, and then by its own test. -/
theorem fallOf_one {f : Fall S} {a : Place} {s : S} {ds : List Fmt.Drawn}
    (h : (fallOf [f] a s ds).isSome = true) : f.place = a ∧ (f.test s ds).isSome = true := by
  unfold fallOf at h
  obtain ⟨g, hg, ht⟩ := (findSome_isSome _ _).1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hg
  obtain rfl := List.mem_singleton.1 h1
  exact ⟨eq_of_beq h2, ht⟩

/-- **A FALL SEATED AT A MEMBER WITH A ROUND: ITS STATED SHARE, HELD AGAINST ITS TEST, PAYS ITS
SENTENCE.** P₀: the letter of `Fall.HeldOn`, on the state in front. -/
theorem fallDebt_of_heldOn (C : CK) (f : Fall S) (ft : Nat) (b : Block S Cl)
    (t : List (Block S Cl)) (dsb : List RDT) (hlen : dsb.length = b.rounds.length)
    (hq : ∀ d ∈ t.takeWhile (fun d => d.rounds.isEmpty), f.place ≠ d.place) (P₀ : S → Prop)
    (h : f.HeldOn C dsb P₀) (P : List Fmt.Drawn → S → Prop) (hP : ∀ fr s', P fr s' → P₀ s') :
    FallDebt C f ft b t dsb [] P f.share.val := by
  intro fr s' hp
  refine le_trans (pr_mono _ ?_) (h s' (hP fr s' hp)).2
  rintro ρ ⟨rs, cols, h1, h2⟩
  rw [List.append_nil] at h1
  have hl : rs.length = b.rounds.length := by
    have e := congrArg List.length h1
    rw [List.length_map, drawnT_len, hlen] at e
    exact e
  rcases chainFall_cons [f] ft b t s' rs cols h2 with g | ⟨s'', k, -, g⟩
  · rw [← hl, List.take_length, h1] at g
    exact (fallOf_one g).2
  · exfalso
    rw [← hl, List.drop_length] at g
    obtain ⟨e, he, hf⟩ := (chainFall_iff _ _ _ _ _).1 g
    obtain ⟨d, hd, hpl⟩ := fronts_quiet ft t s'' _ e he
    exact hq d hd ((fallOf_one hf).1.trans hpl.symm)

/-- **A MARK: ITS STATED SHARE, HELD AGAINST ITS TEST AT EVERY FRONT THAT P LETS IN, PAYS ITS
SENTENCE.** -/
theorem markDebt_of_held (C : CK) (mk : Mark) (dsb : List RDT) (P : List Fmt.Drawn → Prop)
    (h : ∀ fr, P fr → Held C dsb (fun own => (mk.test fr own).isSome) mk.share) :
    MarkDebt C mk dsb P mk.share.val :=
  fun fr hp => (h fr hp).2

end ProofFile.Honest

#print axioms ProofFile.Honest.fallOf_one
#print axioms ProofFile.Honest.fallDebt_of_heldOn
#print axioms ProofFile.Honest.markDebt_of_held
