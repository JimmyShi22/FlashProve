-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/RideKeyD.lean: THE PREMISES
ON WHAT RIDES THROUGH A LOOKUP'S LINK CAN BE MET TOGETHER, AND NOT IDLY: a riding part of the record
with Rides; a form of riding joints with Pins and ReadsLow whose relation is not empty by its make.

Main names:
  stK p₀ i: the riding part: the statement's codes; every message's record but for its ledger of
    mask entries (so: its shape, its sample's rows, its pad); the first i lookups' rows and claims
    on the keys; and, last, p₀: what was handed to the chain at its start, which lies in no block's
    record.
  rides_stK: Rides (stK p₀ i) i.
  rideBy dec cond items: the riding joint "the messages are what the decoder dec gives at the
    statement; and the riding items hold". Its condition is cond.
  pins_rideBy: Pins, by its make. low_rideBy: ReadsLow, where dec and cond read the oracles below c.
  rideBy_some: its relation has a witness wherever dec returns and the items hold of what it
    returns.

Limits. dec, cond and items are letters: no decoder of a file's messages is given. That "no
collision at the samples' seeds" makes the decoder's value the one near message is not this file's
law.

-/
import Johnson.RunOne.Law.SeatsKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RideKeyD
open Iop OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState LookupRecord)
open Johnson.RunOne.Law.SeatsKeyD
open Lk6 (Dat)

/-- A message's record without its ledger of mask entries. -/
def bareO (x : Oracle) : Oracle := { x with ledger := none }

/-- The type of the riding part. P: the type of what is handed to the chain at its start and lies in
no block's record; it stands last. -/
abbrev TK (P : Type) : Type :=
  Codes × Array Oracle × List (List Row) × List (List Lkp.Keys) × P

/-- **The riding part of the record at the link of lookup number i**, with what was handed to the
chain beside it. -/
def stK {P : Type} (p₀ : P) (i : ℕ) (s : FirstState) : TK P :=
  (s.d.st.codes, s.d.st.oracles.map bareO, s.base.rows.take i, s.base.keys.take i, p₀)

theorem takeMaskP_bare {L : Type} {d d' : _root_.Desc.Plain.DState L} {o n : ℕ}
    (h : takeMaskP d o = some (n, d')) :
    d'.st.codes = d.st.codes ∧ d'.st.oracles.map bareO = d.st.oracles.map bareO := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      cases h
      refine ⟨rfl, Array.ext_getElem? fun j => ?_⟩
      simp only [Array.getElem?_map, Array.getElem?_modify]
      by_cases ho : o = j
      · subst ho
        cases d.st.oracles[o]? <;> simp [bareO]
      · simp [ho]
  · cases h

theorem takeMasksInto_bare {L : Type} (o : ℕ) : ∀ (n : ℕ) (d d' : _root_.Desc.Plain.DState L)
    (acc : Array ℕ) (r : List ℕ), takeMasksInto o n d acc = some (r, d') →
    d'.st.codes = d.st.codes ∧ d'.st.oracles.map bareO = d.st.oracles.map bareO
  | 0, d, d', acc, r, h => by
    cases h
    exact ⟨rfl, rfl⟩
  | n + 1, d, d', acc, r, h => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h
      obtain ⟨a1, a2⟩ := takeMaskP_bare (n := x.1) (d' := x.2) h1
      obtain ⟨b1, b2⟩ := takeMasksInto_bare o n x.2 d' _ r h
      exact ⟨b1.trans a1, b2.trans a2⟩

/-- **It rides.** -/
theorem rides_stK {P : Type} (p₀ : P) (i : ℕ) : Rides (stK p₀ i) i where
  base := fun _ _ _ _ => rfl
  hand := fun s o n x h => by
    obtain ⟨a, b⟩ := takeMasksInto_bare o n s.d x.2 #[] x.1 h
    show (x.2.st.codes, x.2.st.oracles.map bareO, _, _, _) = _
    rw [a, b]
    rfl
  app := fun s r k hr hk => by
    have e1 : (s.base.rows ++ [r]).take i = s.base.rows.take i := by
      rw [← hr, List.take_left, List.take_length]
    have e2 : (s.base.keys ++ [k]).take i = s.base.keys.take i := by
      rw [← hk, List.take_left, List.take_length]
    show (s.d.st.codes, s.d.st.oracles.map bareO, (s.base.rows ++ [r]).take i,
      (s.base.keys ++ [k]).take i, p₀) = _
    rw [e1, e2]
    rfl

variable {Fr : VerifiableInference.Desc.Sound.Frame} {A : Dat GE} {M Wp : Type}

/-- **A riding joint by a decoder**: the messages are what dec gives at the statement; the riding
items hold of the riding part and the witness. -/
def rideBy (dec : A.St × Fr.E.Str → Option M) (cond : A.St × Fr.E.Str → Prop)
    (items : A.St → M × Wp → Prop) : IOR.Rels Unit A.St Fr.E (M × Wp) :=
  ⟨fun x y w => dec (x, y) = some w.1 ∧ items x w, fun a w => dec a = some w.1 ∧ items a.1 w, cond,
    fun _ => ()⟩

theorem pins_rideBy (dec : A.St × Fr.E.Str → Option M) (cond : A.St × Fr.E.Str → Prop)
    (items : A.St → M × Wp → Prop) : Pins A Fr.E (rideBy dec cond items) :=
  fun _ _ _ _ _ _ _ h h' => Option.some.inj (h.1.symm.trans h'.1)

theorem low_rideBy (dec : A.St × Fr.E.Str → Option M) (cond : A.St × Fr.E.Str → Prop)
    (items : A.St → M × Wp → Prop) (c : ℕ)
    (hd : ∀ (x : A.St) (y y' : Fr.E.Str), y.1 = y'.1 →
      (∀ q : OnBytes.Maker.PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) →
      dec (x, y) = dec (x, y') ∧ (cond (x, y) ↔ cond (x, y'))) :
    ReadsLow A (rideBy dec cond items) c :=
  fun x y y' h1 h2 => ⟨(hd x y y' h1 h2).2, fun w => by
    show (dec (x, y) = some w.1 ∧ items x w) ↔ (dec (x, y') = some w.1 ∧ items x w)
    rw [(hd x y y' h1 h2).1]⟩

/-- Its relation is not empty by its make. -/
theorem rideBy_some (dec : A.St × Fr.E.Str → Option M) (cond : A.St × Fr.E.Str → Prop)
    (items : A.St → M × Wp → Prop) (a : A.St × Fr.E.Str) (u : M) (wp : Wp) (h : dec a = some u)
    (hi : items a.1 (u, wp)) : (rideBy dec cond items).relR a (u, wp) :=
  ⟨h, hi⟩

end Johnson.RunOne.Law.RideKeyD

#print axioms Johnson.RunOne.Law.RideKeyD.rides_stK
#print axioms Johnson.RunOne.Law.RideKeyD.pins_rideBy
#print axioms Johnson.RunOne.Law.RideKeyD.low_rideBy
