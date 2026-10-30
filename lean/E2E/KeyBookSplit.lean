-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookSplit.lean: the public test `bookSplitFits` (Johnson/Desc/ProofFile/Honest/K14/
Thread2Full.lean) at the key file's book of coins, at the written sizes of the full size.

Why. The linear claim's sub-protocol "SPLIT" spends a coin of the second sending. The test asks the
book for an entry by which that part spends coins, and asks that every such entry names the second
sending's part as its owner and starts at the first coin of the message o_sp. The key file's book
(`keyBook`, E2E/KeyBook.lean) writes its entry from its own count of coins and the linear claim
reads the coin by another count, so the two can disagree. This file asks Lean which it is.

Main names.
  `book_full`: the test accepts `keyBook K` at `QK`, at the value K of `fullPub`.
  `book_asked`: so it accepts at every K that `fullPub` returns.
  `book_field`: the sentence on the book's entries that the field `book` of `K14Asks` asks.
  `bentStart`, `book_bent`, `book_empty`: two negative tests. The test refuses the same book with
    the entry's first coin moved by one, and with no entry. `atFull` is false where `fullPub`
    returns nothing, so these two say something only beside `book_full`.

WHAT IS CLOSED BY EVALUATION. `book_full`, `book_bent`, `book_empty`: closed Bools, evaluated by
Lean's kernel, at one written size. The other two follow by proof.

WHAT IS NOT CLOSED HERE. That the parameters of a key file in the goals' scope are `QK` is another
file's (`par_sourced`, E2E/KeyShapeSharedTies.lean). That a run's book is `keyBook K` is not said
here. The test reads neither an entry's name nor its count, so how many coins the entry lends, and
whether the part's own text takes that coin, are not tested here. Nothing of a run, of a prover or
of any coin's value. Nothing on soundness, completeness or hiding.

-/
import E2E.KeyBookAtWritten
import E2E.KeyShapeSharedFull
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyBookSplit
open ProofFile.Honest ProofFile.Honest.K14
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull)
open AtPublicFiles.AtFiles.Full (QK)

/-- **The test accepts the key file's book at the written sizes.** By Lean's kernel. -/
theorem book_full : atFull (fun K => bookSplitFits (keyBook K) QK) = true := by decide +kernel

/-- So it accepts at every value of `fullPub`. -/
theorem book_asked (K : KeyPub) (hK : fullPub = some K) : bookSplitFits (keyBook K) QK = true := by
  have h := book_full
  unfold atFull at h
  rw [hK] at h
  exact h

/-- **The sentence that the field `book` of `K14Asks` asks**, at the key file's book. -/
theorem book_field (K : KeyPub) (hK : fullPub = some K) :
    ∀ e ∈ (keyBook K).ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨QK, 0⟩).Q.codes
        (jobOmega ⟨QK, 0⟩).Q.sent (jobOmega ⟨QK, 0⟩).sort 1⟩ :=
  book_of_fits (book_asked K hK)

/-- The entry by which "SPLIT" spends coins, with its first coin moved by one. -/
def bentStart (K : KeyPub) : ProverCoinCounts :=
  { keyBook K with
    ahead := (keyBook K).ahead.map fun e =>
      if e.spender == ⟨place 8, 0⟩ && e.once then { e with start := ⟨0, e.start.e + 1⟩ } else e }

/-- **A negative test**: the test refuses that book. -/
theorem book_bent : atFull (fun K => bookSplitFits (bentStart K) QK) = false := by decide +kernel

/-- **A negative test**: the test refuses a book without such an entry. -/
theorem book_empty :
    atFull (fun K => bookSplitFits { keyBook K with ahead := [] } QK) = false := by decide +kernel

end AtPublicFiles.KeyBookSplit

#print axioms AtPublicFiles.KeyBookSplit.book_full
#print axioms AtPublicFiles.KeyBookSplit.book_asked
#print axioms AtPublicFiles.KeyBookSplit.book_field
#print axioms AtPublicFiles.KeyBookSplit.book_bent
#print axioms AtPublicFiles.KeyBookSplit.book_empty
