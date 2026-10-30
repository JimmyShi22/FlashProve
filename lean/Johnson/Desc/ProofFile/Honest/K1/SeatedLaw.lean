-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/SeatedLaw.lean: TWO SMALL LAWS BESIDE THE RECORD K1Seated
(Honest/K1/Seated.lean): WHAT ITS PUBLIC COUNT GIVES: where the book's count at an address IS a
count d, the public test bookCovers accepts there, and the cut of d out of a run's coins at that
address is there at every run, at the chain numbers 0 and 1 (lentCut, bookCovers, lentCut_isSome:
Honest/K1/ScriptAt.lean, ScriptAtLaw.lean). Statements and proofs; no definition.

  covers_of_count    the count gives the public test
  cut_of_count       and so the cut, at all coins, at ch ≤ 1
  K1Seated.covers, K1Seated.cut   the two at the record's field hasCoins

Limits. Which values the cut holds is not said. Nothing here proves that the record can be met.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seated
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}

/-- Where the book's count at an address of a chain is d, the public test accepts. -/
theorem covers_of_count {ch : Nat} {a : Addr} {d : Due} (h : dueAt (Bk.rowsOf ch) a = d) :
    bookCovers Bk ch a d = true := by
  unfold bookCovers
  rw [h]
  exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- And the cut is there, at every run's coins: in the first chain and in the shared one. -/
theorem cut_of_count {ch : Nat} (hc : ch ≤ 1) {a : Addr} {d : Due}
    (h : dueAt (Bk.rowsOf ch) a = d) (k : Coins Bk) : ∃ c, lentCut k ch a d = some c :=
  Option.isSome_iff_exists.1 (by rw [lentCut_isSome k ch hc a d]; exact covers_of_count h)

variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

theorem K1Seated.covers (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) :
    bookCovers Bk 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true := covers_of_count R.hasCoins

theorem K1Seated.cut (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) (k : Coins Bk) :
    ∃ c, lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c :=
  cut_of_count (Nat.zero_le 1) R.hasCoins k

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.covers_of_count
#print axioms ProofFile.Honest.K1.cut_of_count
#print axioms ProofFile.Honest.K1.K1Seated.covers
#print axioms ProofFile.Honest.K1.K1Seated.cut
