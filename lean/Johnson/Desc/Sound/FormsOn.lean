-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsOn.lean: THE PUBLIC TEST `formsIn` (Johnson/Desc/First/Batch/FormsIn.lean)
RIDES FORWARD: from a record of the segment to a later one. Theorems. (The like for `formsInT`:
Johnson/Desc/Sound/FormsT.lean.)

Why. The table of joints ties a public item formsIn m k r to every open item forms m k r: a block
that the item rides past owes "the test holds behind me". The sentences ride BACKWARD
(Johnson/Desc/Sound/FormsQ.lean, `formsQ_rides`); the tests ride forward.
  `Grows a b`: what the later ledger b.F owes the earlier a.F beside `Rides`: as many slots; a
    filled slot stays filled; the two arrays of what is shown and of the factors do not shrink.
  `arrayIn_on`, `entIn_on`, `maskSeat_on`, `slotIn_on`, `affIn_on`: each test at a gives the test
    at b.
  `formsIn_on`: **where the test holds at s, the reader gives ONE ANSWER at s and s', the later part
    rides on the earlier and grows, the slot of the merge's end value is the same, and the late
    slots are still free at s' or hold just what the reader said (`lateOk`): the test holds at s'.**
Limits: (1) ONE ANSWER IS A PREMISE: the reader is the run itself, and that a run gives the same
forms and late slots at a later ledger is a fact on that run's own text. (2) `lateOk` at the later
record is a premise: the block that fills a late slot owes it. (3) "THE SLOT OF THE MERGE's END
VALUE
IS THE SAME" FAILS BY THE MAKE ACROSS THE MERGE's OWN BLOCK, where that slot comes to be: so this
theorem does not carry the test across that block. (4) No block is shown to meet `Rides` or `Grows`.
Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? seatAt seatAt_rides arrayIn entIn maskSeat maskAt lateAt
  lateOk slotIn affIn Read Readers formsIn mergeOf)

section
variable (own : List (ℕ × ℕ))

/-- What the later ledger owes the earlier beside `Rides`. -/
structure Grows (a b : K9.Part) : Prop where
  ns : b.F.ns = a.F.ns
  got : ∀ j : ℕ, a.F.gotF.getD j false = true → b.F.gotF.getD j false = true
  vp : a.F.vp.size ≤ b.F.vp.size
  mf : a.F.mf.size ≤ b.F.mf.size

theorem arrayIn_on (a b : K9.Part) (h : Rides own a b) (t : ℕ) (A : Params.ReqArray)
    (e : arrayIn own a t = some A) : arrayIn own b t = some A := by
  obtain ⟨c, o, x, hc, hA, ho, hx⟩ := K9.arrayIn_some own a t A e
  unfold arrayIn
  rw [h.arrays, hc]
  simp only [Option.bind_some]
  rw [h.rows, hA]
  simp only [Option.bind_some]
  rw [h.sent c.1 A.message o ho]
  simp only [Option.bind_some]
  rw [seatAt_rides own a.d.book b.d.book o x (h.book o) hx]
  rfl

theorem entIn_on (a b : K9.Part) (h : Rides own a b) (x : Ent) (e : entIn own a x = true) :
    entIn own b x = true := by
  obtain ⟨A, hA⟩ := K9.entIn_some own a x e
  unfold entIn at e ⊢
  rw [hA] at e
  rw [arrayIn_on own a b h x.tree A hA]
  exact e

theorem maskSeat_on (a b : K9.Part) (h : Rides own a b) (e : (maskSeat own a).isSome = true) :
    (maskSeat own b).isSome = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 e
  unfold maskSeat at hy ⊢
  rw [maskAt_eq] at hy ⊢
  obtain ⟨o, ho, hx⟩ := Option.bind_eq_some_iff.1 hy
  rw [h.mask o ho]
  simp only [Option.bind_some]
  rw [seatAt_rides own a.d.book b.d.book o y (h.book o) hx]
  rfl

theorem slotIn_on (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (h : Rides own a b)
    (g : Grows a b) (j : ℕ) (e : slotIn own free late a j = true) :
    slotIn own free late b j = true := by
  unfold slotIn at e ⊢
  obtain ⟨s1, e⟩ := Eq.mp (Bool.and_eq_true _ _) e
  obtain ⟨s2, e⟩ := Eq.mp (Bool.and_eq_true _ _) e
  obtain ⟨s3, e⟩ := Eq.mp (Bool.and_eq_true _ _) e
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨by rw [g.ns]; exact s1, ?_⟩
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨maskSeat_on own a b h s2, ?_⟩
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨s3, ?_⟩
  rcases Eq.mp (Bool.or_eq_true _ _) e with e | e
  · exact Eq.mpr (Bool.or_eq_true _ _) (Or.inl e)
  · obtain ⟨t1, e⟩ := Eq.mp (Bool.and_eq_true _ _) e
    obtain ⟨t2, t3⟩ := Eq.mp (Bool.and_eq_true _ _) e
    refine Eq.mpr (Bool.or_eq_true _ _) (Or.inr ?_)
    refine Eq.mpr (Bool.and_eq_true _ _) ⟨g.got j t1, ?_⟩
    exact Eq.mpr (Bool.and_eq_true _ _)
      ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true t2) g.vp),
       decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true t3) g.mf)⟩

theorem affIn_on (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (h : Rides own a b)
    (g : Grows a b) (f : Aff) (e : affIn own free late a f = true) :
    affIn own free late b f = true := by
  unfold affIn at e ⊢
  obtain ⟨e1, e2⟩ := Eq.mp (Bool.and_eq_true _ _) e
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · exact List.all_eq_true.2 fun x hx => entIn_on own a b h x (List.all_eq_true.1 e1 x hx)
  · exact List.all_eq_true.2 fun x hx =>
      slotIn_on own free late a b h g x.1 (List.all_eq_true.1 e2 x hx)

/-- **The public test rides forward.** -/
theorem formsIn_on (Rd : Readers) (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (R : Read)
    (ha : segAt? s = some a) (hb : segAt? s' = some b) (hs : Rd.forms piece run s = some R)
    (hs' : Rd.forms piece run s' = some R) (hm : mergeOf s' = mergeOf s) (h : Rides own a b)
    (g : Grows a b) (hl : lateOk R.late b = true) (hin : formsIn Rd own piece run s = true) :
    formsIn Rd own piece run s' = true := by
  unfold formsIn at hin ⊢
  rw [ha, hs] at hin
  rw [hb, hs', hm]
  obtain ⟨_, e⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hf =>
    affIn_on own (mergeOf s) R.late a b h g f (List.all_eq_true.1 e f hf)⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.arrayIn_on
#print axioms VerifiableInference.Desc.Sound.entIn_on
#print axioms VerifiableInference.Desc.Sound.maskSeat_on
#print axioms VerifiableInference.Desc.Sound.slotIn_on
#print axioms VerifiableInference.Desc.Sound.affIn_on
#print axioms VerifiableInference.Desc.Sound.formsIn_on
