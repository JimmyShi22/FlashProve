-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/ReadNorm.lean: what Given.read returns on the parameter bytes of a plan is the
plan with every number taken modulo 2^64, if the names fit and there are fewer than 2^64 entries.

OnBytes/Params/ReadBackPlan.lean (Given.read_plan) says: Given.read returns the plan that was
spelled, if the plan fits the format's words (Fmt.Plan.fit: every number below 2^64). A number is
spelled modulo 2^64 (Fmt.u64n). So a plan and the plan with every number reduced spell the same
bytes, and the reduced plan fits. Hence the numbers need no bound.

Main definitions: normE, normP (an entry, a plan, with every number modulo 2^64; the names, the
field and the number of entries stay).
Main theorems: u64n_mod, bytes_normE, bytes_normP, paramsBytes_norm, fit_normP, Given.read_norm,
read_entries, rounds_norm.

What is asked: each entry's name fits (Fmt.nameFit), and the plan has fewer than 2^64 entries (hl).
Without hl: OnBytes/Params/Fit/ReadPrefix.lean. Nothing on soundness. For proofs only;
the program does not import this file.


-/
import OnBytes.Params.ReadBackPlan

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- A number is spelled modulo 2^64. -/
theorem u64n_mod (x : Nat) : u64n (x % 2 ^ 64) = u64n x := by
  unfold u64n
  have h : UInt64.ofNat (UInt64.ofNat x).toNat = UInt64.ofNat x := UInt64.ofNat_toNat
  rw [UInt64.toNat_ofNat'] at h
  rw [h]

/-- An entry with its eleven words modulo 2^64. -/
def normE (e : Entry) : Entry where
  name := e.name
  count := e.count % 2 ^ 64
  work := e.work % 2 ^ 64
  msg := e.msg % 2 ^ 64
  roots := e.roots % 2 ^ 64
  answers := e.answers % 2 ^ 64
  drawE := e.drawE % 2 ^ 64
  drawNZ := e.drawNZ % 2 ^ 64
  poss := e.poss % 2 ^ 64
  logN := e.logN % 2 ^ 64
  trits := e.trits % 2 ^ 64
  rows := e.rows % 2 ^ 64

/-- A plan with its five numbers and its entries' words modulo 2^64. -/
def normP (P : Plan) : Plan where
  field := P.field
  salt := P.salt % 2 ^ 64
  nonce := P.nonce % 2 ^ 64
  posB := P.posB % 2 ^ 64
  samples := P.samples % 2 ^ 64
  saved := P.saved % 2 ^ 64
  entries := P.entries.map normE

theorem bytes_normE (e : Entry) : (normE e).bytes = e.bytes := by
  unfold Entry.bytes normE
  simp only [u64n_mod]

theorem bytes_normP (P : Plan) : (normP P).bytes = P.bytes := by
  have e : (P.entries.map normE).map Entry.bytes = P.entries.map Entry.bytes := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => bytes_normE x
  unfold Plan.bytes normP
  simp only [u64n_mod, List.length_map, e]

/-- The two plans spell the same parameter bytes. -/
theorem paramsBytes_norm (P : Plan) (cfg : ByteArray) (others : List (String × ByteArray)) :
    paramsBytes (normP P) cfg others = paramsBytes P cfg others := by
  unfold paramsBytes paramsHead
  rw [bytes_normP]
  rfl

theorem words_normE (e : Entry) : (normE e).words = e.words.map (· % 2 ^ 64) := rfl

theorem fit_normE {e : Entry} (h : nameFit e.name = true) : (normE e).fit = true := by
  unfold Entry.fit
  rw [Bool.and_eq_true]
  refine ⟨h, List.all_eq_true.2 fun n hn => decide_eq_true ?_⟩
  rw [words_normE] at hn
  obtain ⟨m, _, rfl⟩ := List.mem_map.1 hn
  exact Nat.mod_lt _ (Nat.two_pow_pos 64)

/-- The reduced plan fits the format's words. -/
theorem fit_normP {P : Plan} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hl : P.entries.length < 2 ^ 64) : (normP P).fit = true := by
  unfold Plan.fit
  rw [Bool.and_eq_true]
  constructor
  · refine List.all_eq_true.2 fun n h => decide_eq_true ?_
    simp only [normP, List.length_map, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
    · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
    · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
    · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
    · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
    · exact hl
  · refine List.all_eq_true.2 fun e he => ?_
    obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
    exact fit_normE (hn e0 h0)

/-- **Given.read returns the reduced plan.** -/
theorem Given.read_norm {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hl : P.entries.length < 2 ^ 64) (h : Given.read (paramsBytes P cfg others) = some g) :
    g.plan = normP P := by
  rw [← paramsBytes_norm] at h
  exact Given.read_plan (fit_normP hn hl) h

/-- The entries as read back. -/
theorem read_entries {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hl : P.entries.length < 2 ^ 64) (h : Given.read (paramsBytes P cfg others) = some g) :
    g.plan.entries = P.entries.map normE := by
  rw [Given.read_norm hn hl h]
  rfl

/-- The rounds of the reduced plan are the plan's rounds, reduced. -/
theorem rounds_norm (P : Plan) : (normP P).rounds = P.rounds.map normE := by
  show (P.entries.map normE).filter (fun r => r.name != recordName) =
    (P.entries.filter fun r => r.name != recordName).map normE
  rw [List.filter_map]
  rfl

end OnBytes.Params
