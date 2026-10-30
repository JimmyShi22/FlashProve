-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptLots.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: THE TEXTS OF K1's LOTS FOR A LAYING OF THE THREADS' SCRIPT: of ALL a run's
coins, the input and the challenges: in the types that the laying by lots asks. Definitions with
code, and three small laws.

  msgTxt        the place's message number n, entry by entry, INTO Option: scriptMsg
                (Honest/K1/ScriptAt.lean) at the part's own cut; NOTHING where the book has not the
                part's coins
  padTxt        the pad's own component: at padB's places scriptPad at that cut; nothing elsewhere,
                and nothing where the book has not the part's coins
  treeTbl       the place's tree number tau: scriptTable at that cut; TOTAL, as the laying asks:
                where the book has not the part's coins THE TABLE OF NO WORD: it stands for no coin
  msgTxt_some, padTxt_some, treeTbl_some   where the cut is there each is the term at that cut;
                padTxt_some: at a place that padB names

Each reads of the run's coins the part's own cut alone, through ONE reader: lentCut k ch A d, at
A := the place's part 0 and d := the part's own count.

Limits. NO DEFAULT IS LAID HERE FOR A COIN. IT HAS MOVED, NOT GONE: A LAYING THAT LAYS 0 WHERE NO
LOT ANSWERS LAYS, AT A BOOK THAT IS SHORT AT A, 0 AT EVERY ENTRY OF THESE MESSAGES, AT ALL COINS:
THERE THE PAD IS 0 AND AN ANSWER IS THE BARE SUM. SO bookCovers Bk ch A d = true IS TO BE A NAMED
PUBLIC PREMISE OF EVERY LAW THAT IS STATED OVER WHAT IS LAID FROM THESE TEXTS. msgTxt answers at
EVERY entry, beyond the message's ranges too (there rowsR holds 0): that it agrees with another lot
wherever both answer is proved nowhere here. Nothing here holds these texts against any Script.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {W Wl X : Type}

/-- **The place's message number n, entry by entry**: nothing where the book has not the part's
coins. -/
def msgTxt (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n : Nat) :
    Coins Bk → Wl → List Fmt.Drawn → Bool → Nat → Nat → Option GE :=
  fun k w h mask r j =>
    (lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride)).map fun c =>
      scriptMsg J own₀ n c (wit w) h mask r j

/-- **The pad's own component**: at padB's places alone. -/
def padTxt (ch : Nat) (J : SendJob W X) (n : Nat) : Coins Bk → Bool → Nat → Nat → Option GE :=
  fun k mask r j =>
    if padB J.P.codes (shapeAt J.P n) mask r j then
      (lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride)).map fun c => scriptPad J n c mask r j
    else none

/-- **The place's tree number τ**: total; the table of no word where the book has not the part's
coins. -/
def treeTbl (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) :
    Nat → Coins Bk → Wl → List Fmt.Drawn → Place × Table :=
  fun τ k w h =>
    match lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) with
    | some c => scriptTable J own₀ τ c (wit w) h
    | none => (J.P.place, wordlessTable)

theorem msgTxt_some (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n : Nat)
    (k : Coins Bk) (c : Cs (dueR J.P J.ride))
    (hc : lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c) (w : Wl) (h : List Fmt.Drawn)
    (mask : Bool) (r j : Nat) :
    msgTxt ch wit J own₀ n k w h mask r j = some (scriptMsg J own₀ n c (wit w) h mask r j) := by
  unfold msgTxt
  rw [hc]
  rfl

theorem padTxt_some (ch : Nat) (J : SendJob W X) (n : Nat) (k : Coins Bk)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (mask : Bool) (r j : Nat) (hp : padB J.P.codes (shapeAt J.P n) mask r j = true) :
    padTxt ch J n k mask r j = some (scriptPad J n c mask r j) := by
  unfold padTxt
  rw [if_pos hp, hc]
  rfl

theorem treeTbl_some (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (τ : Nat)
    (k : Coins Bk) (c : Cs (dueR J.P J.ride))
    (hc : lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c) (w : Wl) (h : List Fmt.Drawn) :
    treeTbl ch wit J own₀ τ k w h = scriptTable J own₀ τ c (wit w) h := by
  unfold treeTbl
  rw [hc]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.msgTxt
#print axioms ProofFile.Honest.K1.padTxt
#print axioms ProofFile.Honest.K1.treeTbl
#print axioms ProofFile.Honest.K1.msgTxt_some
#print axioms ProofFile.Honest.K1.padTxt_some
#print axioms ProofFile.Honest.K1.treeTbl_some
