-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpNamedEarlierMessages.lean: THEOREMS: THE NAMED READER OF THE ORACLE MESSAGES'
OUT-OF-DOMAIN SAMPLES (smpNamed cs seats, Johnson/Desc/Sound/SmpNamed.lean) IS LEFT, INSIDE THE
PROMISE IN FRONT, BY EVERY BLOCK WHOSE YES LEAVES THE OLDER MESSAGES (K1.KeepsOld), UNDER ONE TEST
ON THE PLAN.
Why a fence. The reader finds a member's message by A FIXED NUMBER: the place of the member's seat
in the plan's list of seats. A sending gives its new messages the next numbers, with their sample
rows. So at a state that holds just so many messages as that fixed number, the reader answers
nothing in front and may answer behind: "the block leaves the members' samples" is false of such a
state (part_without_fence: the like at two statements). Inside the promise the state holds as many
messages as the plan says of the blocks in front (First.bookAt).
  smpNamed_old     at two states of which the second has the first's messages (K1.OldMsgs): at a
                   member whose fixed number lies below the messages in front. By the kind's own
                   formsAt_old and ansAt_old (GoodSendStays.lean) and smpNamed_stays.
  bookAt_of_onAt   inside the promise, at a state without a mark: First.bookAt.
  smpLeft_named    **THE STATEMENT**: over a yes of a block with KeepsOld, inside the promise in
                   front, at a state without a mark: at every tenant of T, every member of ms that
                   sits there has the same sample behind. THE ONE TEST ON THE PLAN: the list of
                   seats gives every tenant of T a number below the plan's count of messages in
                   front of the place.
  smpLeft_later    its member: a segment's later sending (keepsOld_commitAtS).
What is not claimed. The test on the plan. That the block of the reads has KeepsOld. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.GoodSendStays
import Johnson.Desc.K1.Places
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (Mem Sending SitsAt smpNamed smpNamed_stays numAt seatOf)

variable {Cl Pp W : Type}

/-- At two states of which the second has the first's messages. -/
theorem smpNamed_old (cs : Codes) (seats : List (ℕ × ℕ)) (a b : Pp × S)
    (h : OldMsgs a.2.st b.2.st) (m : Mem) (hn : numAt seats m < a.2.st.oracles.size) :
    smpNamed cs seats b m.1 m.2 = smpNamed cs seats a m.1 m.2 :=
  smpNamed_stays cs seats a b m.1 m.2 (formsAt_old cs _ h _ hn) (ansAt_old h _ hn)

/-- Inside the promise, at a state without a mark: where the book stands. -/
theorem bookAt_of_onAt (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (p : Option Place)
    (O : List Item) (Q : List Pub) (x : Pp × S) (y : Strs) (h : First.onAt N Mg links p O Q x y)
    (hf : x.2.failed = none) : First.bookAt N p x.2 = true := by
  rcases h.2 with hm | hk
  · exact absurd hf hm
  · have h1 := hk.1
    simp only [Bool.and_eq_true] at h1
    exact h1.2

/-- **The block leaves the members' samples**, inside the promise in front. -/
theorem smpLeft_named (cs : Codes) (seats : List (ℕ × ℕ)) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (p : Option Place) (O : List Item) (Q : List Pub) (B : Block S Cl)
    (hB : KeepsOld (fun s : S => s.st) B) (ms : List Mem) (T : List (ℕ × ℕ))
    (hn : ∀ u ∈ T, seats.idxOf u < N.msgsAt p) (x x' : Pp × S) (y : Strs) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide x.2 rs gs = .ok x'.2)
    (hin : First.onAt N Mg links p O Q x y) (hf : x.2.failed = none) :
    ∀ u ∈ T, ∀ m ∈ ms, SitsAt m u.1 u.2 →
      smpNamed cs seats x' m.1 m.2 = smpNamed cs seats x m.1 m.2 := by
  intro u hu m _ hs
  have hb := bookAt_of_onAt N Mg links p O Q x y hin hf
  unfold First.bookAt at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have hs' : m.1.seat m.2 = u := hs
  refine smpNamed_old cs seats x x' (hB x.2 x'.2 rs gs h) m ?_
  rw [hb.2]
  unfold numAt seatOf
  rw [hs']
  exact hn u hu

/-- Its member: a segment's later sending. -/
theorem smpLeft_later (cs : Codes) (seats : List (ℕ × ℕ)) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (p : Option Place) (O : List Item) (Q : List Pub) (q : Params.First)
    (gp : GPar) (link piece moment : Nat) (arrays : Option (List Nat)) (ms : List Mem)
    (T : List (ℕ × ℕ)) (hn : ∀ u ∈ T, seats.idxOf u < N.msgsAt p) (x x' : Pp × S) (y : Strs)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (laterAt (Cl := Cl) q gp link piece moment arrays).decide x.2 rs gs = .ok x'.2)
    (hin : First.onAt N Mg links p O Q x y) (hf : x.2.failed = none) :
    ∀ u ∈ T, ∀ m ∈ ms, SitsAt m u.1 u.2 →
      smpNamed cs seats x' m.1 m.2 = smpNamed cs seats x m.1 m.2 :=
  smpLeft_named cs seats N Mg links p O Q _ (keepsOld_commitAtS _ link moment arrays) ms T hn x x'
    y rs gs h hin hf

/-- A statement without a message, and one with one message, sampled, with one sample row. -/
def noMsg : Statement := { codes := {}, oracles := #[], groups := #[] }

def oneMsg : Statement :=
  { codes := {}, oracles := #[{ shape := {}, sampled := true, sampleRows := #[default] }]
    groups := #[] }

/-- **Without the fence it fails**: the second statement has all the first's messages, and the
target read at the number 0 is nothing at the first and something at the second. -/
theorem part_without_fence :
    OldMsgs noMsg oneMsg ∧ ansAt noMsg 0 = none ∧ (ansAt oneMsg 0).isSome = true := by
  refine ⟨⟨rfl, fun j hj => ?_⟩, rfl, rfl⟩
  exact absurd hj (Nat.not_lt_zero j)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.smpNamed_old
#print axioms VerifiableInference.Desc.K1.bookAt_of_onAt
#print axioms VerifiableInference.Desc.K1.smpLeft_named
#print axioms VerifiableInference.Desc.K1.smpLeft_later
#print axioms VerifiableInference.Desc.K1.part_without_fence
