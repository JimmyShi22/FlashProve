-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsPassK3.lean: HOW THE SENTENCE "forms" OF ANOTHER RUN AND ITS PUBLIC TEST
PASS A SUB-PROTOCOL THAT TURNS NO MORE THAN THE LOOKUP's DOES: the premises Rides, More and Fwd of
the kind-free lemmas forms_back and formsIn_fwd (Johnson/Desc/Reads/FormsPass.lean)
and Comes of formsInA_on (Johnson/Desc/Sound/FormsAheadOn.lean),
from ONE SMALL STRUCTURE ON TWO STATES OF THE VERIFIER, K3Pass, and, for Fwd, from one
property of the run, RunSame. Definitions, statements and proofs. No run's text and no
sub-protocol's text is read here.

OBJECT: K9.segAt?, K9.lateOk, K9.readerOf, K9.readersOfLink; Sound.Rides, Sound.Comes; Pass.More,
  Pass.Fwd.
USER: Johnson/Top/H/Keep/K3PassOf.lean.
LETTERS: s, s': the states in front of and behind the sub-protocol; F, G: their ledgers; own, Rd,
  piece, run, rd, late, states, b, name, H, l free.
Compiled with the whole library.

Main names:
  K3Pass s s' F G: all but the open link's own part is the same (SameBut); the ledgers; G is later
    than F; both have their sizes; the same arrays in the ledger; NOTHING IS FILLED BELOW F.next
    THAT WAS FREE; a debt that is not marked as paid stays so; the slot of the merge's end value is
    the same; the approximate range proof's parameters are still there. K3Pass.trans.
  K3Pass.part: the open segment's part behind, and in what it agrees with the part in front.
  rides_of_parts, K3Pass.rides: Rides.
  lateOk_behind: the late slots' test behind, for late slots below F.next. K3Pass.more: More.
  comes_of_parts: Comes: nothing is sent.
  RunSame r s s': what the run answers at s it answers at s', with the same late slots, over the
    same arrays. reader_test, reader_make, reader_fwd, link_fwd: Fwd at a link's readers.
  k3_formsIn_fwd, k3_forms_back: THE TWO ENDS.

Limits. hlow (every late slot of the reader's answer lies below F.next) and RunSame are BY RUN:
premises here. link_fwd asks besides that the link's second hole is silent at (b, name, s): WHERE
THE RUN IS SILENT AT s AND THAT HOLE ANSWERS, Fwd CAN FAIL (behind, the run may speak). The name
"K8.equations" is read by the link's first hole: nothing on it here.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Reads.FormsPass
import Johnson.Desc.Sound.FormsAheadOn
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Desc.First.Look.K3DigitsSeatedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? lateOk lateOf mergeOf Read Readers RunOf readerOf
  readersOfLink statesOfLink LinkHoles ownRow aheadIn aheadOf formsIn)
open VerifiableInference.Desc.Sound (Rides Comes MsgQ formsQ)
open VerifiableInference.Reads.Pass (Fwd More more_of_later forms_back formsIn_fwd)

/-- **What a sub-protocol that the sentences pass may turn.** -/
structure K3Pass (s s' : S) (F G : Fork) : Prop where
  same : SameBut s s'
  front : s.fork? = some F
  behind : s'.fork? = some G
  later : _root_.Fo.Later F G
  sizedF : Sized F
  sizedG : Sized G
  trees : G.trees = F.trees
  below : ∀ j, j < F.next → Filled G j → Filled F j
  owed : ∀ i, Desc.K3.unpaid F i = true → Desc.K3.unpaid G i = true
  merge : mergeOf s' = mergeOf s
  tl : s.tl?.isSome = true → s'.tl?.isSome = true

theorem K3Pass.trans {s t u : S} {F G H : Fork} (P : K3Pass s t F G) (Q : K3Pass t u G H) :
    K3Pass s u F H where
  same := P.same.trans Q.same
  front := P.front
  behind := Q.behind
  later := P.later.trans Q.later
  sizedF := P.sizedF
  sizedG := Q.sizedG
  trees := Q.trees.trans P.trees
  below := fun j hj h => P.below j hj (Q.below j (Nat.lt_of_lt_of_le hj P.later.next) h)
  owed := fun i h => Q.owed i (P.owed i h)
  merge := Q.merge.trans P.merge
  tl := fun h => Q.tl (P.tl h)

/-! ## The parts -/

theorem segAt_cut {s : S} {a : Desc.K9.Part} (h : segAt? s = some a) :
    s.link? = some a.L ∧ s.fork? = some a.F ∧ s.tl?.isSome = true ∧ a.d.st = s.st ∧
      a.d.book = s.book := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        rw [← h]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem segAt_make {s : S} {L : LinkCtx} {F : Fork} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl?.isSome = true) :
    ∃ a, segAt? s = some a ∧ a.L = L ∧ a.F = F ∧ a.d.st = s.st ∧ a.d.book = s.book := by
  obtain ⟨tl, ht⟩ := Option.isSome_iff_exists.1 ht
  unfold segAt?
  rw [hL, hF, ht]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **The part behind.** -/
theorem K3Pass.part {s s' : S} {F G : Fork} (P : K3Pass s s' F G) {a : Desc.K9.Part}
    (ha : segAt? s = some a) :
    ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ a.F = F ∧ b.F = G ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := segAt_cut ha
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := segAt_make (P.same.link.trans h1) P.behind (P.tl h3)
  exact ⟨b, hb, e1, Option.some.inj (h2.symm.trans P.front), e2, by rw [e3, P.same.st, h4],
    by rw [e4, P.same.book, h5]⟩

/-! ## Rides, More, Comes -/

theorem rides_of_parts (own : List (ℕ × ℕ)) {a b : Desc.K9.Part} (hL : b.L = a.L)
    (hst : b.d.st = a.d.st) (hbk : b.d.book = a.d.book) (hl : _root_.Fo.Later a.F b.F) :
    Rides own a b where
  arrays := by rw [hL]
  rows := by rw [hL]
  sent := fun _ _ _ h => by rw [hL]; exact h
  mask := fun _ h => by rw [hL]; exact h
  book := fun _ _ h => by rw [hbk]; exact h
  bits := fun _ _ _ _ => by rw [hst]; exact ⟨rfl, rfl⟩
  filled := fun j _ hj => (hl.keep j hj).2

/-- The late slots' test behind. -/
theorem lateOk_behind {late : List (ℕ × E × E)} {a b : Desc.K9.Part} (hl : _root_.Fo.Later a.F b.F)
    (hbel : ∀ j, j < a.F.next → Filled b.F j → Filled a.F j)
    (hlow : ∀ x ∈ late, x.1 < a.F.next) (h : lateOk late a = true) : lateOk late b = true := by
  unfold lateOk at h ⊢
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h x hx)
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨by rw [hl.ns]; exact h1, ?_⟩
  by_cases hf : a.F.gotF.getD x.1 false = true
  · obtain ⟨_, k2, k3⟩ := hl.keep x.1 hf
    rw [hf] at h2
    simp only [Bool.not_true, Bool.false_or] at h2
    rw [k2, k3, h2]
    exact Bool.or_true _
  · have hb : b.F.gotF.getD x.1 false = false := by
      cases e : b.F.gotF.getD x.1 false with
      | false => rfl
      | true => exact absurd (hbel x.1 (hlow x hx) e) hf
    rw [hb]
    rfl

theorem comes_of_parts (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) {a b : Desc.K9.Part}
    (hL : b.L = a.L) : Comes sent own a b := by
  intro t c q _ hq
  refine Or.inl ⟨q, ?_, rfl⟩
  unfold aheadIn aheadOf at hq ⊢
  rw [hL]
  exact hq

section
variable {s s' : S} {F G : Fork} (P : K3Pass s s' F G)
include P

theorem K3Pass.rides (own : List (ℕ × ℕ)) {a b : Desc.K9.Part} (ha : segAt? s = some a)
    (hb : segAt? s' = some b) : Rides own a b := by
  obtain ⟨b', hb', e1, e2, e3, e4, e5⟩ := P.part ha
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact rides_of_parts own e1 e4 e5 (by rw [e2, e3]; exact P.later)

theorem K3Pass.more {late : List (ℕ × E × E)} {a b : Desc.K9.Part} (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hlow : ∀ x ∈ late, x.1 < F.next) (h : lateOk late a = true) :
    More late a b s s' := by
  obtain ⟨b', hb', _, e2, e3, _, _⟩ := P.part ha
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hl : _root_.Fo.Later a.F b'.F := by rw [e2, e3]; exact P.later
  refine more_of_later ⟨hl.next, hl.ns, fun _ => by rw [e3]; exact P.sizedG, hl.keep⟩
    (by rw [e2]; exact P.sizedF) P.merge
    (lateOk_behind hl (by rw [e2, e3]; exact P.below) (by rw [e2]; exact hlow) h)

theorem K3Pass.comes (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) {a b : Desc.K9.Part}
    (ha : segAt? s = some a) (hb : segAt? s' = some b) : Comes sent own a b := by
  obtain ⟨b', hb', e1, _⟩ := P.part ha
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact comes_of_parts sent own e1

/-- **THE TEST GOES FORWARD.** -/
theorem k3_formsIn_fwd (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (hf : Fwd Rd piece run s s')
    (hlow : ∀ R, Rd.forms piece run s = some R → ∀ x ∈ R.late, x.1 < F.next)
    (hin : formsIn Rd own piece run s = true) : formsIn Rd own piece run s' = true := by
  cases ha : segAt? s with
  | none =>
    unfold formsIn at hin
    rw [ha] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, _⟩ := P.part ha
    refine formsIn_fwd Rd own piece run s s' a b ha hb hf (P.rides own ha hb) (fun R hR => ?_) hin
    refine P.more ha hb (hlow R hR) ?_
    have h := hin
    unfold formsIn at h
    rw [ha, hR] at h
    exact (Eq.mp (Bool.and_eq_true _ _) h).1

/-- **THE SENTENCE GOES BACK.** -/
theorem k3_forms_back (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (rd : ℕ × ℕ → MsgQ) (hf : Fwd Rd piece run s s') (hin : formsIn Rd own piece run s = true)
    (h : formsQ Rd own piece run s' rd) : formsQ Rd own piece run s rd := by
  cases ha : segAt? s with
  | none =>
    unfold formsIn at hin
    rw [ha] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, _⟩ := P.part ha
    exact forms_back Rd own piece run s s' a b rd ha hb hf hin (P.rides own ha hb) h

end

/-! ## The reader -/

/-- What the run answers at s it answers at s', with the same late slots, over the same arrays. -/
def RunSame (r : ℕ → S → Except String (List Claim × S)) (s s' : S) : Prop :=
  ∀ cl t F G, r 0 s = .ok (cl, t) → s.fork? = some F → t.fork? = some G →
    ∃ t' F' G', r 0 s' = .ok (cl, t') ∧ s'.fork? = some F' ∧ t'.fork? = some G' ∧
      lateOf F' G' = lateOf F G ∧ F'.trees = F.trees

theorem ownRow_trees {F F' : Fork} (h : F'.trees = F.trees) : ownRow F' = ownRow F := by
  funext x
  unfold ownRow
  rw [h]

/-- What the reader's answer is made of, with its test on the claims. -/
theorem reader_test {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s : S} {R : Read}
    (h : readerOf states b name s = some R) :
    ∃ nm run cl t F G, (states b).find? (fun r => r.1 == name) = some (nm, run) ∧
      run 0 s = .ok (cl, t) ∧ s.fork? = some F ∧ t.fork? = some G ∧
      (cl.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true ∧
      R = { forms := cl.map (·.form), late := lateOf F G } := by
  unfold readerOf at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨nm, run⟩ := r
  cases hz : run 0 s with
  | error e => simp [hz] at h
  | ok z =>
    cases hF : s.fork? with
    | none => simp [hz, hF] at h
    | some F =>
      simp only [hz, hF] at h
      obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · rename_i ht
        exact ⟨nm, run, z.1, z.2, F, G, hr, hz, rfl, hG, ht, (Option.some.inj h).symm⟩
      · exact nomatch h

/-- And back. -/
theorem reader_make {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s t : S} {nm : String}
    {run : ℕ → S → Except String (List Claim × S)} {cl : List Claim} {F G : Fork}
    (hf : (states b).find? (fun r => r.1 == name) = some (nm, run))
    (hr : run 0 s = .ok (cl, t)) (hF : s.fork? = some F) (hG : t.fork? = some G)
    (ht : (cl.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) =
      true) :
    readerOf states b name s = some { forms := cl.map (·.form), late := lateOf F G } := by
  unfold readerOf
  rw [hf]
  simp only [Option.bind, hr, hF, hG, ht, if_true]

/-- **The run's reader goes forward.** -/
theorem reader_fwd {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s s' : S}
    (h : ∀ nm r, (states b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r s s')
    (R : Read) (hR : readerOf states b name s = some R) : readerOf states b name s' = some R := by
  obtain ⟨nm, run, cl, t, F, G, hf, hr, hF, hG, ht, rfl⟩ := reader_test hR
  obtain ⟨t', F', G', e1, e2, e3, e4, e5⟩ := h nm run hf cl t F G hr hF hG
  rw [← e4]
  exact reader_make hf e1 e2 e3 (by rw [ownRow_trees e5]; exact ht)

/-- **Fwd at a link's readers.** -/
theorem link_fwd (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String} {s s' : S}
    (hn : (name == "K8.equations") = false) (hs : H.silent b name s = none)
    (h : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r s s') :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  have h' : (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := hR
  rw [hn] at h'
  cases hr : readerOf (statesOfLink l) b name s with
  | none =>
    simp only [hr] at h'
    have h2 : H.silent b name s = some R := h'
    rw [hs] at h2
    exact nomatch h2
  | some R0 =>
    simp only [hr] at h'
    have h2 : some R0 = some R := h'
    obtain rfl := Option.some.inj h2
    show (if name == "K8.equations" then H.small s'
      else match readerOf (statesOfLink l) b name s' with
        | some R => some R
        | Option.none => H.silent b name s') = some R0
    rw [hn, reader_fwd h R0 hr]
    rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.K3Pass.trans
#print axioms VerifiableInference.OnPublicFiles.K3Pass.rides
#print axioms VerifiableInference.OnPublicFiles.K3Pass.more
#print axioms VerifiableInference.OnPublicFiles.K3Pass.comes
#print axioms VerifiableInference.OnPublicFiles.k3_formsIn_fwd
#print axioms VerifiableInference.OnPublicFiles.k3_forms_back
#print axioms VerifiableInference.OnPublicFiles.link_fwd
