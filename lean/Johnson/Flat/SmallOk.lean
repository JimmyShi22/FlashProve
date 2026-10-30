-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SmallOk.lean: a public test on a chain's finished plan: its rounds that draw matrix
entries are rounds of the smallness test as Johnson/Flat/NoRoomSmall.lean takes them.

A plan's round has an entry: a name and numbers. It has no kind: a round's kind is its name's
(`kindOf`, OnBytes/Params/Names.lean). What a written round draws depends on its entry and on its
kind (`Fmt.dsOf`): a round of the kind "sealed" draws a seal behind its matrix entries. So the step
from a plan's entry to a written round's draws asks that the written round's kind is its name's.

Main names:
  `isSmall e`: the entry's name is of the kind "entries", or the entry draws matrix entries.
  `smallE e`: if so, then: the name is of that kind; it draws no position and no element of the
    extension field; the number of its matrix entries is above 0 and a multiple of 128; no work;
    logN ≤ 64.
  `smallOk P`: `smallE` at every round of the plan P.
  `smallCount P`: the number of rounds of P with `isSmall`.
  `dsOf_entries`: an entry without positions and elements, at the kind "entries", draws its matrix
    entries alone.
  `smallE_entriesOnly`: from `smallE` and `isSmall` at a written round's entry, where the round's
    kind is its name's: `EntriesOnly d (c * 128)` for some c ≥ 1.
  `SmallRounds P`: for written rounds ds whose entries are those of the plan's rounds of the chain,
    one by one (`Aligned`, OnBytes/Flat/HeldAll.lean), each d of them with `isSmall` whose kind is
    its name's has `EntriesOnly d (c * 128)` for some c ≥ 1.
  `smallOk_entriesOnly`: `smallOk P` = true gives `SmallRounds P`.
  `smallOk_below`: with `no_room_small`: at such a round, for that c, the count
    4 ^ (c * 128) / 2 ^ 128 is a share of at most 2 ^ -128 of the written verifier messages.

The test says no (each a theorem, at a plan of one round under the name RNG): `no_elem`: 128 matrix
entries and an element; `no_zero`: no matrix entry; `no_127`: 127 of them; `no_work`: one bit of
work; `no_name`: 128 matrix entries under a name of another kind; `no_pos`: a position;
`no_nz`: an element marked as never 0; `no_logN`: logN = 65. `yes_128`: it says yes at 128
matrix entries alone, and counts one round. `yes_idle`: it says yes at a plan without rounds, and
counts none: so a row that uses the test also says how many rounds it counts.

Limits. The test reads the plan's record alone, whatever routine made it. Nothing on a round's count
of bad typed values. That a description's written rounds are aligned with a plan, and that their
kinds are their names', is not said here.

-/
import Johnson.Flat.NoRoomSmall
import OnBytes.Flat.HeldAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Number
open Iop Prob Run OnBytes.Params OnBytes.Slice OnBytes.Flat.Held

/-- The entry's name is of the kind "entries", or the entry draws matrix entries. -/
def isSmall (e : Fmt.Entry) : Bool := kindOf e.name == some .entries || e.trits != 0

/-- The test on an entry. -/
def smallE (e : Fmt.Entry) : Bool :=
  !isSmall e ||
    (kindOf e.name == some .entries && e.poss == 0 && e.drawE == 0 && e.drawNZ == 0 &&
      decide (0 < e.trits) && e.trits % 128 == 0 && e.work == 0 && decide (e.logN ≤ 64))

/-- The public test on one chain's finished plan. -/
def smallOk (P : Planned) : Bool := P.rounds.all fun r => smallE r.entry

/-- The rounds that the test looks at. -/
def smallCount (P : Planned) : ℕ := (P.rounds.filter fun r => isSmall r.entry).length

/-- An entry without positions and elements, at the kind "entries". -/
theorem dsOf_entries (e : Fmt.Entry) (h1 : e.poss = 0) (h2 : e.drawE = 0) (h3 : e.drawNZ = 0) :
    Fmt.dsOf e .entries = [.trits e.trits] := by
  simp [Fmt.dsOf, Fmt.dsElems, h1, h2, h3]

/-- From the test on the entry to the written round's draws. -/
theorem smallE_entriesOnly (d : PQ.RD) (hk : kindOf d.entry.name = some d.kind)
    (hs : isSmall d.entry = true) (h : smallE d.entry = true) :
    ∃ c, 1 ≤ c ∧ EntriesOnly d (c * 128) := by
  simp only [smallE, hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨k, p⟩, e⟩, z⟩, t0⟩, tm⟩, w⟩, l⟩ := h
  have hkind : d.kind = .entries := Option.some.inj (hk.symm.trans k)
  refine ⟨d.entry.trits / 128, by omega, ?_, w, l⟩
  rw [hkind, dsOf_entries d.entry p e z, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero tm)]

/-- What the test gives of one plan. -/
def SmallRounds (P : Planned) : Prop :=
  ∀ ds : List PQ.RD, Aligned ds P → ∀ d ∈ ds, kindOf d.entry.name = some d.kind →
    isSmall d.entry = true → ∃ c, 1 ≤ c ∧ EntriesOnly d (c * 128)

/-- **The test gives it.** -/
theorem smallOk_entriesOnly (P : Planned) (h : smallOk P = true) : SmallRounds P := by
  intro ds ha d hd hk hs
  have h1 : d.entry ∈ (chainRounds P).map (·.entry) := by
    have ha' : ds.map (·.entry) = (chainRounds P).map (·.entry) := ha
    rw [← ha']
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.1 h1
  have hr' : r ∈ P.rounds := (List.mem_filter.1 hr).1
  have h2 : smallE r.entry = true := List.all_eq_true.1 h r hr'
  have he' : r.entry = d.entry := he
  rw [he'] at h2
  exact smallE_entriesOnly d hk hs h2

/-- With the rule on such rounds. -/
theorem smallOk_below (P : Planned) (h : smallOk P = true) (ds : List PQ.RD) (ha : Aligned ds P)
    (d : PQ.RD) (hd : d ∈ ds) (hk : kindOf d.entry.name = some d.kind)
    (hs : isSmall d.entry = true) :
    ∃ c, 1 ≤ c ∧ d.entry.trits = c * 128 ∧
      RoundBelow (4 ^ (c * 128) / 2 ^ 128) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨c, hc, he⟩ := smallOk_entriesOnly P h ds ha d hd hk hs
  refine ⟨c, hc, ?_, no_room_small c d he⟩
  have h1 : d.entry ∈ (chainRounds P).map (·.entry) := by
    have ha' : ds.map (·.entry) = (chainRounds P).map (·.entry) := ha
    rw [← ha']
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  obtain ⟨r, hr, her⟩ := List.mem_map.1 h1
  have h2 : smallE r.entry = true := List.all_eq_true.1 h r (List.mem_filter.1 hr).1
  have her' : r.entry = d.entry := her
  rw [her'] at h2
  simp only [smallE, hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨k, p⟩, e⟩, z⟩, _⟩, _⟩, _⟩, _⟩ := h2
  have hkind : d.kind = .entries := Option.some.inj (hk.symm.trans k)
  have h3 := he.1
  rw [hkind, dsOf_entries d.entry p e z] at h3
  injection h3 with h4 _
  injection h4

/-! ## Where the test says no, and where yes -/

/-- A plan of one round. -/
def onePlan (s : Setting) (e : Fmt.Entry) : Planned := ⟨s, [{ entry := e }]⟩

theorem smallOk_one (s : Setting) (e : Fmt.Entry) : smallOk (onePlan s e) = smallE e := by
  simp [smallOk, onePlan]

theorem smallCount_one (s : Setting) (e : Fmt.Entry) (h : isSmall e = true) :
    smallCount (onePlan s e) = 1 := by
  simp [smallCount, onePlan, h]

theorem no_elem (s : Setting) :
    smallOk (onePlan s { name := "RNG", trits := 128, drawE := 1 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_zero (s : Setting) : smallOk (onePlan s { name := "RNG" }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_127 (s : Setting) : smallOk (onePlan s { name := "RNG", trits := 127 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_work (s : Setting) :
    smallOk (onePlan s { name := "RNG", trits := 128, work := 1 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_name (s : Setting) : smallOk (onePlan s { name := "LINK", trits := 128 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem yes_128 (s : Setting) : smallOk (onePlan s { name := "RNG", trits := 128 }) = true ∧
    smallCount (onePlan s { name := "RNG", trits := 128 }) = 1 :=
  ⟨by rw [smallOk_one]; decide +kernel, smallCount_one s _ (by decide +kernel)⟩

theorem yes_idle (s : Setting) : smallOk ⟨s, []⟩ = true ∧ smallCount ⟨s, []⟩ = 0 := ⟨rfl, rfl⟩

theorem no_pos (s : Setting) :
    smallOk (onePlan s { name := "RNG", trits := 128, poss := 1 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_nz (s : Setting) :
    smallOk (onePlan s { name := "RNG", trits := 128, drawNZ := 1 }) = false := by
  rw [smallOk_one]
  decide +kernel

theorem no_logN (s : Setting) :
    smallOk (onePlan s { name := "RNG", trits := 128, logN := 65 }) = false := by
  rw [smallOk_one]
  decide +kernel

end VerifiableInference.Number

#print axioms VerifiableInference.Number.dsOf_entries
#print axioms VerifiableInference.Number.smallE_entriesOnly
#print axioms VerifiableInference.Number.smallOk_entriesOnly
#print axioms VerifiableInference.Number.smallOk_below
#print axioms VerifiableInference.Number.no_elem
#print axioms VerifiableInference.Number.no_zero
#print axioms VerifiableInference.Number.no_127
#print axioms VerifiableInference.Number.no_work
#print axioms VerifiableInference.Number.no_name
#print axioms VerifiableInference.Number.yes_128
#print axioms VerifiableInference.Number.yes_idle
#print axioms VerifiableInference.Number.no_pos
#print axioms VerifiableInference.Number.no_nz
#print axioms VerifiableInference.Number.no_logN
#print axioms VerifiableInference.Number.smallOk_one
#print axioms VerifiableInference.Number.smallCount_one
