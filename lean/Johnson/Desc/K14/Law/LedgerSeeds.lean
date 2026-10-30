-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeeds.lean: THE FIRST WRITTEN ROUND OF EACH OF THE SHARED CHAIN's TWO
SENDINGS IS ITS ROUND OF SEEDS, FROM ONE TEST WITH CODE ON THE WRITTEN LIST. Four binders of
ledger_at_cap (Johnson/Desc/K14/Law/LedgerAtCap.lean: he12, hk12, he15, hk15) are had from its t2,
t5 and hUw and the test sendsLB (Johnson/Goal/Numbers/K14OwnAt.lean).

  seeds_written   what sendsLB's yes says of the written list's rounds 1 and 4, at every item and
                  every list of messages fixed before the point (parU_free, parO_free)
  seeds_two       d21.entry = seedEntry (parU Q sentU) ∧ d21.kind = .seeds
  seeds_five      d51.entry = seedEntry (parO Q) ∧ d51.kind = .seeds
THE TEST IS ASKED AT THE ITEM 0 AND THE LIST [(1, 0)], as real_testL and key_testL (the same file)
evaluate it; Q's own item and list are free.
What is not claimed. That the test says yes at a description's own Q and Wr. Nothing on soundness.

-/
import Johnson.HB.LLHARD.K14Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.K1 (seedEntry)

/-- What the test's yes says of the written rounds 1 and 4. -/
theorem seeds_written {fl : ℕ} (Q : P14) {Wr : Rounds} {sentU : Array OracleNotice}
    (hUw : withU Q.S = some sentU)
    (hs : sendsLB fl ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩ Wr = true) :
    atW Wr 1 = some (seedEntry (parU Q sentU), .seeds) ∧
      atW Wr 4 = some (seedEntry (parO Q), .seeds) := by
  unfold sendsLB at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s1, s2⟩, -⟩, -⟩ := hs
  have hU' : withU (P14.S ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩) = some sentU := hUw
  rw [hU', Option.all_some] at s1
  exact ⟨of_decide_eq_true s1, of_decide_eq_true s2⟩

/-- **he12, hk12.** -/
theorem seeds_two {fl : ℕ} (Q : P14) {Wr : Rounds} {sentU : Array OracleNotice}
    (hUw : withU Q.S = some sentU)
    (hs : sendsLB fl ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩ Wr = true) (d21 d22 : RDT)
    (t2 : Ties Wr 2 [d21, d22]) :
    d21.entry = seedEntry (parU Q sentU) ∧ d21.kind = .seeds := by
  have e := Option.some.inj ((t2.1 d21 d22 rfl rfl).symm.trans (seeds_written Q hUw hs).1)
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- **he15, hk15.** -/
theorem seeds_five {fl : ℕ} (Q : P14) {Wr : Rounds} {sentU : Array OracleNotice}
    (hUw : withU Q.S = some sentU)
    (hs : sendsLB fl ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩ Wr = true) (d51 d52 : RDT)
    (t5 : Ties Wr 5 [d51, d52]) :
    d51.entry = seedEntry (parO Q) ∧ d51.kind = .seeds := by
  have e := Option.some.inj ((t5.2.2.1 d51 d52 rfl rfl).symm.trans (seeds_written Q hUw hs).2)
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.seeds_written
#print axioms Desc.K14.Law.seeds_two
#print axioms Desc.K14.Law.seeds_five
