-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesOwn.lean: `SenderLays` (Law/Rule/TiesFall.lean) FROM A
SENTENCE AT TYPED COINS. The authors of a sender's kind have its rows typed over its part's own
coins, `Cs d` at the part's own count d; `SenderLays` speaks of what the book's look hands at the
sender's address, whose count stands in a pair. So that nobody has to cast: their sentence is asked
AT ITS OWN TYPE (`SenderLaysOwn`: after "the core at typed coins" of the authors of K1's part), and
the passage is made here, under one sentence on the book (`OwnIs`).

  1  `SenderLaysOwn`   THE SENDER's AUTHORS': at every coins cs of the part's own count: the row's
     entry number ν is coin number base + ν of cs
  2  `OwnIs`   THE BOOK's MAKER's: what the frame lends the part as its own (the first d of what
     the look hands at its address) is there at every run's coins: own k
  3  `senderLays_of_own`   the two give `SenderLays` at the row "rowOf (own k)", where base + ν
     lies inside the count
  4  `ownIs_of_due`   `OwnIs` holds, at some own, wherever the look's count at the address is d
     at every coins

Limits. Premises' forms; neither 1 nor 2 is shown at any book. THE SENDER IS OF THE KIND K1 AT THE
CHAIN's FIRST SEGMENT AND AT THE INDEX MASKS' MESSAGE, OF THE KIND K2 AT THE 24 OTHER SEGMENTS. THE
base OF 1 IS A COUNT OF THE SENDER's AUTHORS' OWN TEXT (so there are two such texts); the book's
maker has
a count of its own text (`maskStart`, Honest/BookRows.lean) in `RowIsStretch`: that the two are one
number is a further sentence, on closed numbers, which a test with code is to print; no lemma says
it; and the book's maker's count takes one k for all fresh tables of a sending: a sending with two
fresh tables of different k would be miscounted by it. Coins of the extension field alone. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)

/-- **The sender's authors', at its own type.** d: the part's own count. rowOf: the mask row, of the
part's own coins. A premise's form. -/
def SenderLaysOwn {d : Due} (rowOf : Cs d → Nat → E) (base : Nat) (N : Nat → Prop) : Prop :=
  ∀ cs ν, N ν → rowOf cs ν = (coinsE cs).getD (base + ν) zeroE

/-- **The book's maker's.** own: the part's own coins, of a run's. A premise's form. -/
def OwnIs (Bk : ProverCoinCounts) (ch : Nat) (o : Addr) (d : Due) (own : Coins Bk → Cs d) : Prop :=
  ∀ k, (k.look ch o).2.cut ⟨0, 0⟩ d = some (own k)

theorem senderLays_of_own {Bk : ProverCoinCounts} {W : Type} {ch : Nat} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {base : Nat} {N : Nat → Prop} {own : Coins Bk → Cs d}
    (h : SenderLaysOwn rowOf base N) (ho : OwnIs Bk ch o d own)
    (hin : ∀ ν, N ν → base + ν < d.e) :
    SenderLays (W := W) Bk ch o base (fun k _ _ ν => rowOf (own k) ν) N := by
  intro k _ _ ν hν
  show rowOf (own k) ν = _
  rw [h (own k) ν hν, cut_coinsE (ho k), getD_stretch _ _ _ _ _ (hin ν hν), Nat.zero_add]

theorem ownIs_of_due {Bk : ProverCoinCounts} {ch : Nat} {o : Addr} {d : Due}
    (h : ∀ k : Coins Bk, (k.look ch o).1 = d) : ∃ own, OwnIs Bk ch o d own := by
  have hs : ∀ k : Coins Bk, ∃ c, (k.look ch o).2.cut ⟨0, 0⟩ d = some c := by
    intro k
    unfold Cs.cut
    rw [dif_pos (by rw [h k]; exact ⟨Nat.le_of_eq (Nat.zero_add _), Nat.le_of_eq (Nat.zero_add _)⟩)]
    exact ⟨_, rfl⟩
  exact ⟨fun k => Classical.choose (hs k), fun k => Classical.choose_spec (hs k)⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.senderLays_of_own
#print axioms ProofFile.Honest.ownIs_of_due
