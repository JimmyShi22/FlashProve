-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SmpNamed.lean: THE READER OF SAMPLES, NAMED: NO LETTER BUT THE CODES AND THE
PLAN's LIST OF SEATS. Definitions and theorems, proved.

Why. `PinAt`, `CfAt` and the fields that MeaningSig.lean fills take the reader of samples as a
letter smp. A law at a letter says little: at smp := "nothing" every pin is false. Here one reader
is named.
  `numAt seats x`: the FIXED number of the member x's message in the first chain's statement: the
    place of x's seat (tree, tenant) in seats: the plan's seats in the order of sending.
  `smpNamed cs seats`: a : P × S, a sending s, a member i ↦ `K1.smpAt cs ‹the member's shape› ‹its
    radius› a.2.st (numAt seats ⟨s, i⟩)` (Johnson/Desc/K1/Law/GoodSendForms.lean: the first
    sample row that the statement holds of that message, read as a linear form, with its target: a
    sample at some seed whose matrix is that form); AT A MEMBER WHOSE SEAT IS NOT IN seats: NOTHING
    (`smpNamed_none`; else the place "beyond the list" would be read as a message's number). At a
    seat of the list (`smpNamed_at`) it is `smpByNumber cs (·.2.st) (numAt seats)` of
    Johnson/Desc/Sound/SendSeam.lean, by the two texts.
  `smpNamed_bySeat` (proved): it hangs on the member's entry (shape and radius) and seat alone, not
    on the list in which the member stands: `SmpBySeat` (PinMove.lean).
  `smpNamed_stays` (proved): two records whose statements read the same form and the same target at
    the member's number have the same sample there. `smpNamed_same` (proved): so two records with
    one statement.
  `smpNamed_of` (proved): where the member's seat is in seats (hq) and the statement's sample rows
    of that message are the kind's one row
    at a seed ρ with the answer y (`K1.SeedIs`) and `K1.Tie` holds of the shape: the record HOLDS a
    sample z; its answers are y; its seed has ρ's sample map. (`K1.smpAt_of`, carried over.)
Limits. seats is a letter for a plain list. That the record's book places the message number k at
seats[k] is a test on a record: not here. One answer a message. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- The fixed number of a member's message: the place of its seat in the plan's list. -/
def numAt (seats : List (ℕ × ℕ)) (x : Mem) : ℕ := seats.idxOf (seatOf x)

/-- At an entry p (shape and radius) and a seat q: NOTHING where q is no seat of the list. -/
def smp1At (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (St : OnBytes.Statement)
    (p : OnBytes.OracleShape × ℕ) (q : ℕ × ℕ) : Option (portOmZ cs p.1 p.2).Smp :=
  if q ∈ seats then K1.smpAt cs p.1 p.2 St (seats.idxOf q) else none

/-- **The reader of samples.** -/
def smpNamed {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a : P × S) (s : Sending)
    (i : Fin s.l.length) : Option ((sigOf cs s.l).om i).Smp :=
  smp1At cs seats a.2.st (s.l.get i) (s.seat i)

/-- At a seat of the list it is the kind's own reading at the fixed number. -/
theorem smpNamed_at {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a : P × S)
    (s : Sending) (i : Fin s.l.length) (hq : s.seat i ∈ seats) :
    smpNamed cs seats a s i =
      K1.smpAt cs (s.l.get i).1 (s.l.get i).2 a.2.st (numAt seats ⟨s, i⟩) :=
  if_pos hq

/-- At any other seat: nothing. -/
theorem smpNamed_none {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a : P × S)
    (s : Sending) (i : Fin s.l.length) (hq : s.seat i ∉ seats) : smpNamed cs seats a s i = none :=
  if_neg hq

theorem smp1At_heq (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (St : OnBytes.Statement)
    (p p₂ : OnBytes.OracleShape × ℕ) (q q₂ : ℕ × ℕ) (hp : p = p₂) (hq : q = q₂) :
    HEq (smp1At cs seats St p q) (smp1At cs seats St p₂ q₂) := by
  subst hp
  subst hq
  rfl

/-- **It hangs on the entry and the seat alone.** -/
theorem smpNamed_bySeat {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) :
    SmpBySeat cs (smpNamed (P := P) cs seats) := by
  intro a x x₂ h
  exact smp1At_heq cs seats a.2.st _ _ _ _ h.1 h.2

theorem smpAt_stays (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e : ℕ)
    (St St' : OnBytes.Statement) (o : ℕ) (hf : K1.formsAt cs sh St' o = K1.formsAt cs sh St o)
    (ha : K1.ansAt St' o = K1.ansAt St o) : K1.smpAt cs sh e St' o = K1.smpAt cs sh e St o := by
  unfold K1.smpAt
  simp only [hf, ha]

/-- **It stays** where the form and the target at the member's number stay. -/
theorem smpNamed_stays {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a b : P × S)
    (s : Sending) (i : Fin s.l.length)
    (hf : K1.formsAt cs (s.l.get i).1 b.2.st (numAt seats ⟨s, i⟩) =
      K1.formsAt cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩))
    (ha : K1.ansAt b.2.st (numAt seats ⟨s, i⟩) = K1.ansAt a.2.st (numAt seats ⟨s, i⟩)) :
    smpNamed cs seats b s i = smpNamed cs seats a s i := by
  by_cases hq : s.seat i ∈ seats
  · rw [smpNamed_at cs seats b s i hq, smpNamed_at cs seats a s i hq]
    exact smpAt_stays cs _ _ _ _ _ hf ha
  · rw [smpNamed_none cs seats b s i hq, smpNamed_none cs seats a s i hq]

theorem smpNamed_same {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a b : P × S)
    (h : b.2.st = a.2.st) (s : Sending) (i : Fin s.l.length) :
    smpNamed cs seats b s i = smpNamed cs seats a s i := by
  unfold smpNamed
  rw [h]

/-- **The record holds the sample** where its rows are the kind's one row at a seed. -/
theorem smpNamed_of {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a : P × S)
    (s : Sending) (i : Fin s.l.length) (hq : s.seat i ∈ seats)
    (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE) (hT : K1.Tie cs (s.l.get i).1)
    (h : K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y) :
    ∃ z : ((sigOf cs s.l).om i).Smp, smpNamed cs seats a s i = some z ∧ z.2 = (fun _ => y) ∧
      ((sigOf cs s.l).om i).Z.val z.1 = ((sigOf cs s.l).om i).Z.val ρ := by
  obtain ⟨z, h1, h2, h3⟩ := K1.smpAt_of cs (s.l.get i).1 (s.l.get i).2 a.2.st _ ρ y hT h
  exact ⟨z, (smpNamed_at cs seats a s i hq).trans h1, h3, h2⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.smpNamed_at
#print axioms VerifiableInference.Desc.Sound.smpNamed_none
#print axioms VerifiableInference.Desc.Sound.smpNamed_bySeat
#print axioms VerifiableInference.Desc.Sound.smpNamed_stays
#print axioms VerifiableInference.Desc.Sound.smpNamed_same
#print axioms VerifiableInference.Desc.Sound.smpNamed_of
