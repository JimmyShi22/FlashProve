-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersFwd.lean: AT K1's LATER PLACES THE
READERS ARE ASKED ONE DIRECTION ALONE: what a reader answers at the state in front of the
sub-protocol it answers at the state behind it (Reads.Pass.Fwd, Johnson/Desc/Reads/FormsPass.lean;
K1's ReadersStay is that sentence at each run of an item). Statements with their proofs.

Why. go_forms_later and aForms_of (Johnson/Desc/K1/Law/GoAtLaterForms.lean, Johnson/Desc/K1/Law/AFormsOf.lean) asked an
equation: the reader gives one answer at both states. Where the ledger grows, a reader that is
silent in front may answer behind, so the equation asked of every pair of states is more than holds.
It is not needed: the item's public test in front (formsIn, formsInA, formsInT) is true only where
the reader answers in front, and the promise in front holds that test. At such a state one
direction gives the equation.

OBJECT. Any readers, run and two states of the chain; then any sub-protocol B with LaterSend P B and
LaterGrows B (members: laterAt, IM.k1Reads).
USER. k01_law (Johnson/Desc/K1/Law/K01Law.lean): its binder hRd (Johnson/Desc/K1/Law/CallsF.lean has
the call). Reads.Pass.forms_back | formsIn_fwd at a commitment: rides_more_later pays their
premises Rides and More.

PROVED HERE.
  readersStay_iff_fwd: ReadersStay is Fwd at each run of the item (by definition).
  answers_of_formsIn | _formsInA | _formsInT: a true test says that the reader answers.
  one_of_fwd: an answer in front and Fwd give the equation.
  one_of_stay: **the equation at each run of forms m k r**, from the public item formsIn m k r in
    front and ReadersStay.
  go_forms_later_fwd: **go_forms_later with ReadersStay in hl's place.**
  aForms_of_fwd: **aForms_of with ReadersStay in hl's place.**
  more_of_part · more_of_rec: **Reads.Pass.More** from PartRides | RecRides: across a
    commitment the ledger's slots are left, so five fields are equations; the sixth (the late slots'
    test behind) is the same test in front.
  rides_more_later: **Rides and More over the sub-protocol's own accept.**
  formsQ_later_pass · formsIn_later_pass: Reads.Pass.forms_back and formsIn_fwd called at
    a commitment: both can be used there as they stand.
PREMISES THAT STAY, BY NAME. hRd (ReadersStay, asked behind the accept, the promise in front and
"the item is open"): each run's kind's law. hwt, hmeet: as in aForms_of.
IS IT EMPTY HERE? That a sub-protocol accepts, or that a reader with Fwd is laid in: not shown.
What is not claimed. Fwd of any reader. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.AFormsOf
import Johnson.Desc.Reads.FormsPass

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning PubData pubAll)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K9 (Read Readers segAt? mergeOf lateOk formsIn formsInT formsInA)
open VerifiableInference.Desc.Sound (Stated Rides MsgQ formsQ)
open VerifiableInference.Reads.Pass (Fwd)

variable {Pp Cells Tok Cl : Type}

/-! ## 1 One direction is enough where the test in front is true -/

/-- ReadersStay is Reads.Pass.Fwd at each run that the item names. -/
theorem readersStay_iff_fwd (D : PubData) (m k : ℕ) (r : String) (s s' : S) :
    ReadersStay D m k r s s' ↔ ∀ p ∈ D.runs m k r, Fwd (D.Rd m) p.1 p.2 s s' := Iff.rfl

section
variable (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)

theorem answers_of_formsIn (h : formsIn Rd own piece run s = true) :
    ∃ X, Rd.forms piece run s = some X := by
  unfold formsIn at h
  cases er : Rd.forms piece run s with
  | some X => exact ⟨X, rfl⟩
  | none =>
    rw [er] at h
    cases ea : segAt? s with
    | none =>
      rw [ea] at h
      cases h
    | some a =>
      rw [ea] at h
      cases h

theorem answers_of_formsInT (h : formsInT Rd own piece run s = true) :
    ∃ X, Rd.forms piece run s = some X := by
  unfold formsInT at h
  cases er : Rd.forms piece run s with
  | some X => exact ⟨X, rfl⟩
  | none =>
    rw [er] at h
    cases ea : segAt? s with
    | none =>
      rw [ea] at h
      cases h
    | some a =>
      rw [ea] at h
      cases h

theorem answers_of_formsInA (sent : ℕ → List (ℕ × ℕ))
    (h : formsInA Rd sent own piece run s = true) : ∃ X, Rd.forms piece run s = some X := by
  unfold formsInA at h
  cases er : Rd.forms piece run s with
  | some X => exact ⟨X, rfl⟩
  | none =>
    rw [er] at h
    cases ea : segAt? s with
    | none =>
      rw [ea] at h
      cases h
    | some a =>
      rw [ea] at h
      cases h

/-- An answer in front and one direction give the equation. -/
theorem one_of_fwd (s' : S) (hf : Fwd Rd piece run s s') (h : ∃ X, Rd.forms piece run s = some X) :
    Rd.forms piece run s' = Rd.forms piece run s := by
  obtain ⟨X, hX⟩ := h
  rw [hX]
  exact hf X hX

end

/-- **The equation at each run of forms m k r**, from the public item in front and one direction. -/
theorem one_of_stay (D : PubData) (base : Pub → Pp × S → Bool) (m k : ℕ) (r : String) (x : Pp × S)
    (s' : S) (hin : pubAll D base (.formsIn m k r) x = true) (hRd : ReadersStay D m k r x.2 s') :
    ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 x.2 := by
  rw [pubAll_formsIn, List.all_eq_true] at hin
  intro p hp
  have h1 := hin p hp
  refine one_of_fwd _ _ _ _ _ (hRd p hp) ?_
  by_cases ha : D.ah p.1 p.2 = true
  · rw [if_pos ha] at h1
    exact answers_of_formsInA _ _ _ _ _ _ h1
  · rw [if_neg ha] at h1
    exact answers_of_formsIn _ _ _ _ _ h1

/-! ## 2 The riding item "forms" over the sub-protocol's own accept -/

/-- **go_forms_later with one direction in the equation's place.** -/
theorem go_forms_later_fwd {P : Par} {B : Block S Cl} (hB : LaterSend P B) (hG : LaterGrows B)
    (D : PubData) (arr : ℕ → ℕ → ℕ) (ms : List Sound.Mem) (St : Stated)
    (after : ℕ → S → Except String S) (wt : ℕ → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop)
    (rwB : ℕ → S → Bool) (Mg : Meaning Pp (Wit Cells Tok Sound.MsgT))
    (base : Pub → Pp × S → Bool) (x x' : Pp × S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h2 : rs.length = 2)
    (h : B.decide x.2 rs gs = .ok x'.2) (hfull : x.2.book.place.size = x.2.st.oracles.size)
    (m k : ℕ) (r : String) (hRd : ReadersStay D m k r x.2 x'.2)
    (y y' : Strs) (w : Wit Cells Tok Sound.MsgT) (hwt : r = "weights" → wt m x' y' w → wt m x y w)
    (hin : pubAll D base (.formsIn m k r) x = true)
    (hmeet : ∀ p ∈ D.runs m k r, D.ah p.1 p.2 = true →
      AheadMeets (D.N.sent m) (D.N.group m) (idsOf P x.2.st.oracles.size).toList x.2 x'.2)
    (h0 : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x'
      y' w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x y w :=
  go_forms_later hB hG D arr ms St after wt rwB Mg base x x' rs gs h2 h hfull m k r
    (one_of_stay D base m k r x x'.2 hin hRd) y y' w hwt hin hmeet h0

/-- **aForms_of with one direction in the equation's place**: the top's binder aForms at one later
place. -/
theorem aForms_of_fwd (D : PubData) (base0 : Pub → Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (ms : List Sound.Mem) (St : Stated) (after : ℕ → S → Except String S)
    (wt : ℕ → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop) (rwB : ℕ → S → Bool)
    (Mg0 Mg : Meaning Pp (Wit Cells Tok Sound.MsgT)) (hpub : Mg.pub = pubAll D base0)
    (hforms : Mg.forms =
      (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg0).forms)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (P : Par) (B : Block S Unit)
    (hS : LaterSend P B) (hG : LaterGrows B) (h2 : B.rounds.length = 2) (base : ℕ)
    (hRd : ∀ x x' y m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      Item.forms m j r ∈ openAt links ps k → ReadersStay D m j r x.2 x'.2)
    (hwt : ∀ x x' y y' w m j, YesOf B x x' → InAt D.N Mg links ps k x y → KeptBelow base y y' →
      Item.forms m j "weights" ∈ openAt links ps k → wt m x' y' w → wt m x y w)
    (hmeet : ∀ x x' y m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      Item.forms m j r ∈ openAt links ps k → ∀ p ∈ D.runs m j r, D.ah p.1 p.2 = true →
      AheadMeets (D.N.sent m) (D.N.group m) (idsOf P x.2.st.oracles.size).toList x.2 x'.2) :
    ∀ (x x' : Pp × S) y y' w m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      KeptBelow base y y' → Item.forms m j r ∈ openAt links ps k → Mg.forms m j r x' y' w →
      Mg.forms m j r x y w :=
  aForms_of D base0 arr ms St after wt rwB Mg0 Mg hpub hforms links ps k P B hS hG h2 base
    (fun x x' y m j r hy hIn ho =>
      one_of_stay D base0 m j r x x'.2
        (by rw [← hpub]; exact inAt_pub hIn _ (formsIn_open _ _ m j r ho))
        (hRd x x' y m j r hy hIn ho))
    hwt hmeet

/-! ## 3 Rides and More across a commitment -/

/-- **More**, from what the tests on forms read of the part: the slots are left. -/
theorem more_of_part {new : List ℕ} {a b : K9.Part} (R : PartRides new a b) {s s' : S}
    (hm : mergeOf s' = mergeOf s) {late : List (ℕ × E × E)} (hl : lateOk late a = true) :
    Reads.Pass.More late a b s s' := by
  refine ⟨R.slots.ns, fun j hj => ?_, ?_, ?_, Or.inl hm, ?_⟩
  · rw [R.slots.gotF]
    exact hj
  · exact Nat.le_of_eq (congrArg Array.size R.slots.vp).symm
  · exact Nat.le_of_eq (congrArg Array.size R.slots.mf).symm
  · rw [lateOk_rides R]
    exact hl

/-- The same of two states of the chain. -/
theorem more_of_rec {new : List ℕ} {s s' : S} (R : RecRides new s s') {a : K9.Part}
    (ha : segAt? s = some a) :
    ∃ b, segAt? s' = some b ∧
      ∀ late : List (ℕ × E × E), lateOk late a = true → Reads.Pass.More late a b s s' := by
  obtain ⟨b, hb, hR⟩ := R.seg a ha
  exact ⟨b, hb, fun _ hl => more_of_part hR R.merge hl⟩

section
variable {P : Par} {B : Block S Cl} (hB : LaterSend P B) (hG : LaterGrows B) (s s' : S)
  (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (h2 : rs.length = 2)
  (h : B.decide s rs gs = .ok s') (hfull : s.book.place.size = s.st.oracles.size)
include hB hG h2 h hfull

/-- **Rides and More over the sub-protocol's own accept.** -/
theorem rides_more_later (own : List (ℕ × ℕ)) {a : K9.Part} (ha : segAt? s = some a) :
    ∃ b, segAt? s' = some b ∧ Rides own a b ∧
      ∀ late : List (ℕ × E × E), lateOk late a = true → Reads.Pass.More late a b s s' := by
  have R := (hB _ _ _ _ h2 h).2.1
  obtain ⟨b, hb, hR, hr, _⟩ := rides_of_rec R (hG _ _ _ _ h) hfull own ha
  exact ⟨b, hb, hr, fun _ hl => more_of_part hR R.merge hl⟩

/-- Reads.Pass.forms_back, called at a commitment. -/
theorem formsQ_later_pass (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (rd : ℕ × ℕ → MsgQ) (hf : Fwd Rd piece run s s') (hin : formsIn Rd own piece run s = true)
    (h0 : formsQ Rd own piece run s' rd) : formsQ Rd own piece run s rd := by
  cases ea : segAt? s with
  | none =>
    unfold formsIn at hin
    rw [ea] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, hr, _⟩ := rides_more_later hB hG s s' rs gs h2 h hfull own ea
    exact Reads.Pass.forms_back Rd own piece run s s' a b rd ea hb hf hin hr h0

/-- Reads.Pass.formsIn_fwd, called at a commitment. -/
theorem formsIn_later_pass (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (hf : Fwd Rd piece run s s') (hin : formsIn Rd own piece run s = true) :
    formsIn Rd own piece run s' = true := by
  cases ea : segAt? s with
  | none =>
    unfold formsIn at hin
    rw [ea] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, hr, hM⟩ := rides_more_later hB hG s s' rs gs h2 h hfull own ea
    refine Reads.Pass.formsIn_fwd Rd own piece run s s' a b ea hb hf hr (fun X hX => hM _ ?_) hin
    have h1 := hin
    unfold formsIn at h1
    rw [ea, hX] at h1
    exact (Eq.mp (Bool.and_eq_true _ _) h1).1

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.readersStay_iff_fwd
#print axioms VerifiableInference.Desc.K1.answers_of_formsIn
#print axioms VerifiableInference.Desc.K1.answers_of_formsInT
#print axioms VerifiableInference.Desc.K1.answers_of_formsInA
#print axioms VerifiableInference.Desc.K1.one_of_fwd
#print axioms VerifiableInference.Desc.K1.one_of_stay
#print axioms VerifiableInference.Desc.K1.go_forms_later_fwd
#print axioms VerifiableInference.Desc.K1.aForms_of_fwd
#print axioms VerifiableInference.Desc.K1.more_of_part
#print axioms VerifiableInference.Desc.K1.more_of_rec
#print axioms VerifiableInference.Desc.K1.rides_more_later
#print axioms VerifiableInference.Desc.K1.formsQ_later_pass
#print axioms VerifiableInference.Desc.K1.formsIn_later_pass
