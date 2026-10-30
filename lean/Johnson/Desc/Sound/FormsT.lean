-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsT.lean: THE SENTENCE "formsT" (Johnson/Desc/Sound/FormsQ.lean) IN FRONT OF A
SEGMENT's SECOND SENDING: its letter `Stated` as a term, THE EXCHANGE with "forms" across that
sending,
and its public test's riding forward. Definitions and theorems.

Why. `formsTQ` reads the witness at the first sending's seats alone, and passes the data through
`Stated.at1`: each array of the second sending is set to its STATED FUNCTION of the first sending's
arrays. That letter was bare. Each hearing kind knows its own formula.
  `second s c`: a test on the record: the array of the name c is of the open segment's own second
    sending (`K9.atMoment1`).
  `Stated.of u`: THE TERM: at1 s D := D, but at the cells of an array of the second sending: cell
    (r, i) := u s D c r i. u: one letter: the stated function: left, sort by sort of segment, to the
    kind that hears there, over D's own cells: `uBySort` (Johnson/Desc/Sound/StatedAll.lean) joins
    the sorts. THE MASK ROW IS LEFT ALONE BY THE MAKE.
  `of_mask`, `of_second`, `of_else`: what it gives, by unfolding.
  `formsTQ_of_formsQ`: **THE EXCHANGE**: from "forms" at the record s' behind the second sending
  (own':
    the seats read there) to "formsT" at the record s in front (own: the first sending's seats), at
    one
    witness, where: the reader gives ONE ANSWER at both · the public test `formsInT` holds at s ·
    the
    arrays' names are the same and what lay under a filled slot has stayed · AT THE CELLS THAT THE
    FORMS NAME THE DATA READ AT s' ARE THE STATED DATA AT s (hcell) · and the mask row's entries
    that
    they name are the same (hmask).
  `entInT_on`, `affInT_on`, `formsInT_on`: the public test rides forward, as `formsIn_on` does
    (Johnson/Desc/Sound/FormsOn.lean), where also the live frame's link and shape stay.
Limits: (1) hcell IS THE WHOLE WEIGHT OF THE EXCHANGE: at an array of the first sending it is "a
seated
cell stays" (`cell_rides`); AT AN ARRAY OF THE SECOND SENDING IT SAYS "THE COMMITTED CELL IS ITS
STATED
FUNCTION": that is what the smallness test's equations of the reads say: NOT SHOWN HERE. (2) u is a
letter. (3) One answer is a premise on the run's own text. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FormsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.K9 (segAt? lateOk slotIn affIn affInT entIn entInT atMoment1 Read
  Readers formsIn formsInT mergeOf)

/-- The array of the name c is of the open segment's own second sending. -/
def second (s : S) (c : ℕ × String) : Bool :=
  match segAt? s with
  | some a =>
    match reqArray a.L.check.rows.layout c.1 c.2 with
    | some A => atMoment1 a c A
    | none => false
  | none => false

/-- **The letter `Stated` as a term.** u: the stated function of an array of the second sending. -/
def Stated.of (u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ) : Stated :=
  ⟨fun s D =>
    { cell := fun l n r i => if second s (l, n) = true then u s D (l, n) r i else D.cell l n r i
      mask := D.mask }⟩

theorem of_mask (u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ) (s : S) (D : Bound GQ) :
    ((Stated.of u).at1 s D).mask = D.mask := rfl

theorem of_second (u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ) (s : S) (D : Bound GQ)
    (c : ℕ × String) (r i : ℕ) (h : second s c = true) :
    ((Stated.of u).at1 s D).cell c.1 c.2 r i = u s D c r i := by
  show (if second s (c.1, c.2) = true then u s D (c.1, c.2) r i else D.cell c.1 c.2 r i) = _
  rw [if_pos h]

theorem of_else (u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ) (s : S) (D : Bound GQ)
    (c : ℕ × String) (r i : ℕ) (h : second s c = false) :
    ((Stated.of u).at1 s D).cell c.1 c.2 r i = D.cell c.1 c.2 r i := by
  show (if second s (c.1, c.2) = true then u s D (c.1, c.2) r i else D.cell c.1 c.2 r i) = _
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- **THE EXCHANGE: "forms" behind the second sending gives "formsT" in front of it.** -/
theorem formsTQ_of_formsQ (Rd : Readers) (St : Stated) (own own' : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInT Rd own piece run s = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hcell : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (dataQ own' b rd).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx)
    (hmask : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQ own' b rd).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1)
    (h : formsQ Rd own' piece run s' rd) : formsTQ Rd St own piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hf⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs : Rd.forms piece run s = some R := hl ▸ hs'
  unfold formsInT at hin
  rw [ha, hs] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨a, R, ha, hs, hlate, fun f hm => ?_⟩
  have hi : affInT own (mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
  refine ⟨hi, ?_⟩
  have h2 := hi
  unfold affInT at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [← value_ridesW own (mergeOf s) R.late a b' (St.at1 s (dataQ own a rd)) (dataQ own' b' rd)
    harr hfill f (List.all_eq_true.1 h3) (hcell R hs f hm) (hmask R hs f hm)]
  exact (hf f hm).2

section
variable (own : List (ℕ × ℕ))

theorem entInT_on (a b : K9.Part) (h : Rides own a b)
    (hk : b.L.check.frame.link = a.L.check.frame.link)
    (hsh : b.L.check.frame.shape = a.L.check.frame.shape) (x : Ent)
    (e : entInT own a x = true) : entInT own b x = true := by
  unfold entInT at e ⊢
  rcases Eq.mp (Bool.or_eq_true _ _) e with e | e
  · exact Eq.mpr (Bool.or_eq_true _ _) (Or.inl (entIn_on own a b h x e))
  · refine Eq.mpr (Bool.or_eq_true _ _) (Or.inr ?_)
    unfold atMoment1 at e ⊢
    rw [h.arrays, h.rows, hk, hsh]
    exact e

theorem affInT_on (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (h : Rides own a b)
    (g : Grows a b) (hk : b.L.check.frame.link = a.L.check.frame.link)
    (hsh : b.L.check.frame.shape = a.L.check.frame.shape) (f : Aff)
    (e : affInT own free late a f = true) : affInT own free late b f = true := by
  unfold affInT at e ⊢
  obtain ⟨e1, e2⟩ := Eq.mp (Bool.and_eq_true _ _) e
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · exact List.all_eq_true.2 fun x hx =>
      entInT_on own a b h hk hsh x (List.all_eq_true.1 e1 x hx)
  · exact List.all_eq_true.2 fun x hx =>
      slotIn_on own free late a b h g x.1 (List.all_eq_true.1 e2 x hx)

/-- **The public test of "formsT" rides forward.** -/
theorem formsInT_on (Rd : Readers) (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (R : Read)
    (ha : segAt? s = some a) (hb : segAt? s' = some b) (hs : Rd.forms piece run s = some R)
    (hs' : Rd.forms piece run s' = some R) (hm : mergeOf s' = mergeOf s) (h : Rides own a b)
    (g : Grows a b) (hk : b.L.check.frame.link = a.L.check.frame.link)
    (hsh : b.L.check.frame.shape = a.L.check.frame.shape) (hl : lateOk R.late b = true)
    (hin : formsInT Rd own piece run s = true) : formsInT Rd own piece run s' = true := by
  unfold formsInT at hin ⊢
  rw [ha, hs] at hin
  rw [hb, hs', hm]
  obtain ⟨_, e⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hf =>
    affInT_on own (mergeOf s) R.late a b h g hk hsh f (List.all_eq_true.1 e f hf)⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.of_mask
#print axioms VerifiableInference.Desc.Sound.of_second
#print axioms VerifiableInference.Desc.Sound.of_else
#print axioms VerifiableInference.Desc.Sound.formsTQ_of_formsQ
#print axioms VerifiableInference.Desc.Sound.entInT_on
#print axioms VerifiableInference.Desc.Sound.affInT_on
#print axioms VerifiableInference.Desc.Sound.formsInT_on
