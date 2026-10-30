-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheKOfRecord.lean: THE ROWS THAT THE KINDS LAY, FROM WHAT EACH KIND HANDS IN. One entry a lot: the
lot, that a lot of the filling bears its name, and that it has that lot's sides. The rows of the two
later chains come as lists, with the proofs that KindRows asks.

  LotEntry               what a kind hands in for a lot
  KindRows.ofEntries     the rows of the kinds, from the entries
  mem_ofEntries          an entry's lot is among the lots
  TheThirteen, LaterRows, theK, mem_theK   the K of record, at an entry for each of the filling's
                         thirteen lots and the later chains' rows

Limits. Definitions and one law. Nothing here says that a kind's lot pays. This file proves nothing
about completeness, soundness or zero knowledge.
-/
import E2E.TheSides

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open ProofFile.Honest

variable {W₀ Rc Tr X₀ X : Type}

/-- **What a kind hands in for a lot.** -/
structure LotEntry (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) where
  slot : SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst
  named : P.lots.any (fun L => L.name == slot.name) = true
  fit : ∀ L ∈ P.lots, L.name = slot.name → (slot.rows Z Gr).map (·.half) = L.halves Z Gr

variable {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : ProofFile.Pub} {Gr : ProofFile.Ground}

/-- **The rows of the kinds, from the entries.** -/
def KindRows.ofEntries (es : List (LotEntry P Z Gr)) (apart : (es.map (·.slot.name)).Nodup)
    (shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey))
    (shared_named : ∀ r ∈ shared, (P.shared Z Gr).any (fun h => h.place == r.place) = true)
    (shared_apart : (shared.map (·.place)).Nodup)
    (shared_fit : ∀ h ∈ P.shared Z Gr, ∀ r, (shared.find? fun r => r.place == h.place) = some r →
      r.half = h)
    (second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (second_named : ∀ r ∈ second, (P.second Z Gr).any (fun h => h.place == r.place) = true)
    (second_apart : (second.map (·.place)).Nodup)
    (second_fit : ∀ h ∈ P.second Z Gr, ∀ r, (second.find? fun r => r.place == h.place) = some r →
      r.half = h) : KindRows P Z Gr where
  lots := es.map (·.slot)
  named := by
    intro s hs
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hs
    exact e.named
  apart := by
    rw [List.map_map]
    exact apart
  lots_fit := by
    intro L hL s hs
    have hm := List.mem_of_find?_eq_some hs
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hm
    have hb := List.find?_some hs
    have hb' : e.slot.name = L.name := by simpa using hb
    exact e.fit L hL hb'.symm
  shared := shared
  shared_named := shared_named
  shared_apart := shared_apart
  shared_fit := shared_fit
  second := second
  second_named := second_named
  second_apart := second_apart
  second_fit := second_fit

/-- **An entry's lot is among the lots.** -/
theorem mem_ofEntries {es : List (LotEntry P Z Gr)} {e : LotEntry P Z Gr} (he : e ∈ es)
    (apart : (es.map (·.slot.name)).Nodup) {shared} {a b c} {second} {d f g} :
    e.slot ∈ (KindRows.ofEntries es apart shared a b c second d f g).lots :=
  List.mem_map.2 ⟨e, he, rfl⟩

/-- **The entries of record, one for each of the filling's thirteen lots.** -/
structure TheThirteen (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) where
  k1 : LotEntry P Z Gr
  k2 : LotEntry P Z Gr
  k7 : LotEntry P Z Gr
  k11 : LotEntry P Z Gr
  k13 : LotEntry P Z Gr
  k3 : LotEntry P Z Gr
  k4 : LotEntry P Z Gr
  k5 : LotEntry P Z Gr
  k6 : LotEntry P Z Gr
  k8 : LotEntry P Z Gr
  k10 : LotEntry P Z Gr
  k12 : LotEntry P Z Gr
  w : LotEntry P Z Gr

/-- The thirteen as a list, in the filling's order. -/
def TheThirteen.entries (E : TheThirteen P Z Gr) : List (LotEntry P Z Gr) :=
  [E.k1, E.k2, E.k7, E.k11, E.k13, E.k3, E.k4, E.k5, E.k6, E.k8, E.k10, E.k12, E.w]

/-- **The rows of the two later chains, with what KindRows asks of them.** -/
structure LaterRows (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) where
  shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)
  shared_named : ∀ r ∈ shared, (P.shared Z Gr).any (fun h => h.place == r.place) = true
  shared_apart : (shared.map (·.place)).Nodup
  shared_fit : ∀ h ∈ P.shared Z Gr, ∀ r, (shared.find? fun r => r.place == h.place) = some r →
    r.half = h
  second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  second_named : ∀ r ∈ second, (P.second Z Gr).any (fun h => h.place == r.place) = true
  second_apart : (second.map (·.place)).Nodup
  second_fit : ∀ h ∈ P.second Z Gr, ∀ r, (second.find? fun r => r.place == h.place) = some r →
    r.half = h

/-- **The K of record**, at the thirteen entries and the later rows. -/
def theK (E : TheThirteen P Z Gr) (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows P Z Gr) : KindRows P Z Gr :=
  KindRows.ofEntries E.entries apart R.shared R.shared_named R.shared_apart R.shared_fit R.second
    R.second_named R.second_apart R.second_fit

/-- **Each entry's lot is in the K of record.** -/
theorem mem_theK {E : TheThirteen P Z Gr} {e : LotEntry P Z Gr} (he : e ∈ E.entries)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows P Z Gr) :
    e.slot ∈ (theK E apart R).lots :=
  mem_ofEntries he apart

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.mem_theK
#print axioms AtPublicFiles.TheSides.KindRows.ofEntries
#print axioms AtPublicFiles.TheSides.mem_ofEntries
