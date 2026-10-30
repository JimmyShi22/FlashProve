-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Writes.lean: the sending of oracle messages with an out-of-domain sample (kind
K1): the term that its decision writes, and first tools.

Main names: tag, fresh, wr, outs (the messages behind a sending, one by one), fitB (the counts fit);
toList_modify_mid, get_mid; rowsOf_size; admitP_iff (when the statement's page admits a sample, and
what it then writes).
Plain records and pure functions of the verifier program are named, none that takes a context or
runs: Send.pad, Slice.admitted, Slice.freshLedger.

What is not claimed. Nothing on what a row means, on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.OwnLaws
import Johnson.Desc.Own.SendAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-! ## The written term -/

/-- Shapes with their numbers, from o on. -/
def tag : Nat → List OracleShape → List (Nat × OracleShape)
  | _, [] => []
  | o, s :: l => (o, s) :: tag (o + 1) l

/-- A message as it is received: its shape, and nothing else. -/
def fresh (s : OracleShape) : OnBytes.Oracle := { shape := s }

/-- A message behind the sending: one that is not sampled is as it was received; a sampled one has
its sample rows, at the first seeds and its own answers, its pad's places and its ledger. -/
def wr (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape) (ys : List E) :
    OnBytes.Oracle :=
  if s.answers = 0 then fresh s else
    { shape := s, sampled := true, sampleRows := rowsOf codes seeds o s ys
      pad := ((Send.pad codes s).getD []).map fun p => (p.part, p.index)
      ledger := Slice.freshLedger codes s }

/-- The messages behind the sending, in the order of sending: each takes its next answers. -/
def outs (codes : Codes) (seeds : List (List E × E)) :
    Nat → List OracleShape → List E → List OnBytes.Oracle
  | _, [], _ => []
  | o, s :: l, ys => wr codes seeds o s ys :: outs codes seeds (o + 1) l (ys.drop s.answers)

/-- The counts fit: each sampled message has a seed for each answer, its answers, and a row long
enough for its pad; no answer is left. n: the number of seeds. -/
def fitB (codes : Codes) (n : Nat) : List OracleShape → List E → Bool
  | [], ys => ys.isEmpty
  | s :: l, ys => if s.answers = 0 then fitB codes n l ys else
      decide (s.answers ≤ n) && decide (s.answers ≤ ys.length) && (Send.pad codes s).isSome &&
        fitB codes n l (ys.drop s.answers)

/-! ## Tools on arrays -/

theorem toList_modify_mid {α : Type} (A : Array α) (pre rest : List α) (x : α) (f : α → α)
    (h : A.toList = pre ++ x :: rest) : (A.modify pre.length f).toList = pre ++ f x :: rest := by
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList, Array.getElem?_modify, ← Array.getElem?_toList, h]
  by_cases hj : pre.length = j
  · subst hj
    simp
  · rw [if_neg hj]
    rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
    · obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + (k + 1) := ⟨j - pre.length - 1, by omega⟩
      simp [List.getElem?_append_right]
    · simp [List.getElem?_append_left hgt]

theorem get_mid {α : Type} (A : Array α) (pre rest : List α) (x : α)
    (h : A.toList = pre ++ x :: rest) : A[pre.length]? = some x := by
  rw [← Array.getElem?_toList, h]
  simp

/-! ## The statement's page admits a sample -/

theorem rowsOf_size (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (h1 : s.answers ≤ seeds.length) (h2 : s.answers ≤ ys.length) :
    (rowsOf codes seeds o s ys).size = s.answers := by
  simp [rowsOf, h1, h2]

theorem admitP_iff (d d₁ : DState L) (o : Nat) (s : OracleShape) (rows : Array OnBytes.Row)
    (hx : d.st.oracles[o]? = some (fresh s)) (hr : rows.size = s.answers) (h0 : s.answers ≠ 0) :
    Ground.admitP d o rows = some d₁ ↔ ∃ places, Send.pad d.st.codes s = some places ∧
      d₁ = { d with st := Slice.admitted d.st o s places rows } := by
  have h1 : 1 ≤ s.answers := Nat.pos_of_ne_zero h0
  unfold Ground.admitP Ground.admitL Ground.ok
  -- the list's clauses on a value that may be missing: under either of the page's two names
  first | unfold Ground.has | unfold Ground.on
  simp only [Own.padMade_eq]
  cases hp : Send.pad d.st.codes s with
  | none => simp [hx, fresh, hp]
  | some places => simp [hx, fresh, hp, hr, h1, eq_comm]

end VerifiableInference.Desc.K1
