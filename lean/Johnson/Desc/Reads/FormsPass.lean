-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FormsPass.lean: how the sentence "forms" and its public test pass a sub-protocol
that stands between the place where a run's claims are first read and the batching: for every kind
of sub-protocol and every run.

Why. In the table of open claims the sentence "forms" at a border speaks of that border's state: of
the open segment's part and of the reader's answer there (`formsQ`, Johnson/Desc/Sound/FormsQ.lean;
its test `formsIn`, Johnson/Desc/First/Batch/FormsIn.lean). A sub-protocol that the sentence passes
owes two things: the test behind from the test in front; the sentence in front from the sentence
behind. `formsQ_rides` has the second under the equation "the reader answers the same at both
states". Where the ledger grows that equation is more than holds: a reader that is silent in front
may answer behind. One direction is enough, since the test in front says that the reader answers
there.

What is stated and shown. All of it is general in the readers, the seats, the run and the two
states.
  `Fwd Rd piece run s s'`: what the reader answers at s it answers at s'.
  `forms_back`: **"forms" at s' gives "forms" at s**, under: both states have their parts; `Fwd`;
    the test at s; `Rides`. The worth of a form is carried by `value_rides`.
  `formsT_back`: the like for "formsT", with `formsTQ_rides`' premise on the stated data kept.
  `More late a b s s'`: what the test reads behind and `Rides` does not hold, one field a clause: as
    many slots; a filled slot stays filled; the two arrays under the slots do not shrink; the slot
    of the merge's end value is the same, or it is a slot that is free in front and is not late; the
    late slots pass their test behind.
  `more_of_later`: four of the six fields from the library's "later ledger" (`OnBytes.PscRun.Later`,
    OnBytes/Tie/Pv/Psc/PscLater.lean) at a ledger of the right sizes; the two others from "the slot
    of the merge's end value is the same" and from the late slots' test.
  `arrayIn_rides`, `entIn_rides`, `maskSeat_rides`, `slotIn_more`, `affIn_more`: the test's clauses,
    one by one.
  `formsIn_fwd`: **the test at s gives the test at s'**, under: both parts; `Fwd`; `Rides`; `More`
    at the reader's late slots.

Limits. `Fwd`, `Rides` and `More` are premises: they are shown here of no sub-protocol. The test of
"formsT" is not carried forward here. Nothing on soundness.


-/
import Johnson.Desc.Sound.FormsQ
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes (E zeroE)
open OnBytes.Model (Aff Ent Reading)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Part segAt? seatAt seatAt_rides arrayIn arrayIn_some entIn maskAt
  maskSeat lateAt lateOk slotIn affIn affInT Read Readers formsIn formsInT mergeOf)
open VerifiableInference.Desc.Sound (MsgQ dataQ Rides Stated formsQ formsTQ value_rides value_ridesW
  maskAt_eq)

/-- What the reader answers at s it answers at s'. -/
def Fwd (Rd : Readers) (piece : ℕ) (run : String) (s s' : S) : Prop :=
  ∀ R, Rd.forms piece run s = some R → Rd.forms piece run s' = some R

/-- **"forms" behind gives "forms" in front.** -/
theorem forms_back (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S)
    (a b : Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hf : Fwd Rd piece run s s') (hin : formsIn Rd own piece run s = true) (hr : Rides own a b)
    (h : formsQ Rd own piece run s' rd) : formsQ Rd own piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hfm⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  unfold formsIn at hin
  cases hR : Rd.forms piece run s with
  | none =>
    rw [ha, hR] at hin
    cases hin
  | some R₀ =>
    rw [ha, hR] at hin
    obtain rfl : R = R₀ := Option.some.inj (hs'.symm.trans (hf R₀ hR))
    obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    refine ⟨a, R, ha, hR, hlate, fun f hm => ?_⟩
    have hi : affIn own (mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
    refine ⟨hi, ?_⟩
    rw [← value_rides own (mergeOf s) R.late a b' rd hr f hi]
    exact (hfm f hm).2

/-- The like for "formsT". -/
theorem formsT_back (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (s s' : S) (a b : Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hf : Fwd Rd piece run s s')
    (hin : formsInT Rd own piece run s = true) (hr : Rides own a b)
    (hat : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      (∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (St.at1 s' (dataQ own b rd)).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx) ∧
      ∀ x ∈ f.slots.toList,
        (St.at1 s' (dataQ own b rd)).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1)
    (h : formsTQ Rd St own piece run s' rd) : formsTQ Rd St own piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hfm⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  unfold formsInT at hin
  cases hR : Rd.forms piece run s with
  | none =>
    rw [ha, hR] at hin
    cases hin
  | some R₀ =>
    rw [ha, hR] at hin
    obtain rfl : R = R₀ := Option.some.inj (hs'.symm.trans (hf R₀ hR))
    obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    refine ⟨a, R, ha, hR, hlate, fun f hm => ?_⟩
    have hi : affInT own (mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
    refine ⟨hi, ?_⟩
    have h2 := hi
    unfold affInT at h2
    obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
    rw [← value_ridesW own (mergeOf s) R.late a b' (St.at1 s (dataQ own a rd))
      (St.at1 s' (dataQ own b' rd)) hr.arrays hr.filled f (List.all_eq_true.1 h3)
      (hat R hR f hm).1 (hat R hR f hm).2]
    exact (hfm f hm).2

/-- What the test reads behind and Rides does not hold. -/
structure More (late : List (ℕ × E × E)) (a b : Part) (s s' : S) : Prop where
  ns : b.F.ns = a.F.ns
  got : ∀ j, a.F.gotF.getD j false = true → b.F.gotF.getD j false = true
  vp : a.F.vp.size ≤ b.F.vp.size
  mf : a.F.mf.size ≤ b.F.mf.size
  merge : mergeOf s' = mergeOf s ∨
    ∃ j, mergeOf s' = some j ∧ a.F.gotF.getD j false = false ∧ lateAt late j = none
  late : lateOk late b = true

/-- From the library's "later ledger". -/
theorem more_of_later {late : List (ℕ × E × E)} {a b : Part} {s s' : S} (hL : Later a.F b.F)
    (hS : Sized a.F) (hm : mergeOf s' = mergeOf s) (hl : lateOk late b = true) :
    More late a b s s' := by
  have hS' := hL.sized hS
  refine ⟨hL.ns, fun j hj => (hL.keep j hj).1, ?_, ?_, Or.inl hm, hl⟩
  · rw [hS.1, hS'.1, hL.ns]
  · rw [hS.2.1, hS'.2.1, hL.ns]

section
variable (own : List (ℕ × ℕ))

theorem arrayIn_rides {a b : Part} (hr : Rides own a b) {t : ℕ} {A : OnBytes.Params.ReqArray}
    (h : arrayIn own a t = some A) : arrayIn own b t = some A := by
  obtain ⟨c, o, x, hc, hq, ho, hx⟩ := arrayIn_some own a t A h
  unfold arrayIn
  rw [hr.arrays, hc, Option.bind_some, hr.rows, hq, Option.bind_some, hr.sent c.1 A.message o ho,
    Option.bind_some, seatAt_rides own a.d.book b.d.book o x (hr.book o) hx, Option.map_some]

theorem entIn_rides {a b : Part} (hr : Rides own a b) {x : Ent} (h : entIn own a x = true) :
    entIn own b x = true := by
  unfold entIn at h ⊢
  cases e : arrayIn own a x.tree with
  | none =>
    rw [e] at h
    cases h
  | some A =>
    rw [e] at h
    rw [arrayIn_rides own hr e]
    exact h

theorem maskSeat_rides {a b : Part} (hr : Rides own a b) (h : (maskSeat own a).isSome = true) :
    (maskSeat own b).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  unfold maskSeat at hx
  rw [maskAt_eq] at hx
  obtain ⟨o, ho, hs⟩ := Option.bind_eq_some_iff.1 hx
  unfold maskSeat
  rw [maskAt_eq, hr.mask o ho, Option.bind_some,
    seatAt_rides own a.d.book b.d.book o x (hr.book o) hs]
  rfl

/-- A slot that is there in front is there behind. -/
theorem slotIn_more {late : List (ℕ × E × E)} {a b : Part} {s s' : S} (hr : Rides own a b)
    (M : More late a b s s') {j : ℕ} (h : slotIn own (mergeOf s) late a j = true) :
    slotIn own (mergeOf s') late b j = true := by
  unfold slotIn at h ⊢
  obtain ⟨h1, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h2, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have g4 : ((lateAt late j).isSome ||
      (b.F.gotF.getD j false && (decide (j < b.F.vp.size) && decide (j < b.F.mf.size)))) =
      true := by
    rcases Eq.mp (Bool.or_eq_true _ _) h4 with h5 | h5
    · rw [h5]
      rfl
    · obtain ⟨k1, k⟩ := Eq.mp (Bool.and_eq_true _ _) h5
      obtain ⟨k2, k3⟩ := Eq.mp (Bool.and_eq_true _ _) k
      rw [M.got j k1, decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true k2) M.vp),
        decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true k3) M.mf)]
      exact Bool.or_true _
  have g3 : (mergeOf s' != some j) = true := by
    rcases M.merge with e | ⟨j0, e, f0, l0⟩
    · rw [e]
      exact h3
    · rw [e]
      by_cases hj : j0 = j
      · exfalso
        subst hj
        rw [l0, f0] at h4
        cases h4
      · simpa using hj
  rw [M.ns, h1, maskSeat_rides own hr h2, g3, g4]
  rfl

/-- A form that names only what is there in front names only what is there behind. -/
theorem affIn_more {late : List (ℕ × E × E)} {a b : Part} {s s' : S} (hr : Rides own a b)
    (M : More late a b s s') {f : Aff} (h : affIn own (mergeOf s) late a f = true) :
    affIn own (mergeOf s') late b f = true := by
  unfold affIn at h ⊢
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact Eq.mpr (Bool.and_eq_true _ _)
    ⟨List.all_eq_true.2 fun x hx => entIn_rides own hr (List.all_eq_true.1 h1 x hx),
      List.all_eq_true.2 fun x hx => slotIn_more own hr M (List.all_eq_true.1 h2 x hx)⟩

end

/-- **The test in front gives the test behind.** -/
theorem formsIn_fwd (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S)
    (a b : Part) (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hf : Fwd Rd piece run s s') (hr : Rides own a b)
    (hM : ∀ R, Rd.forms piece run s = some R → More R.late a b s s')
    (hin : formsIn Rd own piece run s = true) : formsIn Rd own piece run s' = true := by
  unfold formsIn at hin ⊢
  cases hR : Rd.forms piece run s with
  | none =>
    rw [ha, hR] at hin
    cases hin
  | some R =>
    rw [ha, hR] at hin
    rw [hb, hf R hR]
    obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨(hM R hR).late,
      List.all_eq_true.2 fun f hm => affIn_more own hr (hM R hR) (List.all_eq_true.1 hall f hm)⟩

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.forms_back
#print axioms VerifiableInference.Reads.Pass.formsT_back
#print axioms VerifiableInference.Reads.Pass.more_of_later
#print axioms VerifiableInference.Reads.Pass.arrayIn_rides
#print axioms VerifiableInference.Reads.Pass.entIn_rides
#print axioms VerifiableInference.Reads.Pass.maskSeat_rides
#print axioms VerifiableInference.Reads.Pass.slotIn_more
#print axioms VerifiableInference.Reads.Pass.affIn_more
#print axioms VerifiableInference.Reads.Pass.formsIn_fwd
