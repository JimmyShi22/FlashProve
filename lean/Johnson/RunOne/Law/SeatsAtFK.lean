-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/SeatsAtFK.lean: THE THREE
SEATS OF A LOOKUP'S LINK AS SEATS THAT ARE FILLED (SeatGood, Johnson/Desc/Sound/KeySeatsAt.lean) in
a row of pieces over the pair of what was handed to the chain and the chain's own record.

Main names:
  up P R: a row over the chain's own record, as a row over the pair. upF R: a family of such rows,
    one for each value that is handed to the chain, as one row over the pair.
  quietOwn_up: a tie over the record is a tie over the pair.
  low_rowIn, low_rowOut, low_row3: the rows read, of the oracles, what the riding joint reads.
  tie_seat, law_seat: A SEAT OF A TIE, AND THE SEAT OF A PROVED TYPED BLOCK, ARE FILLED where the
    rows at the borders are ours, lifted, and the piece holds the link's block.
  upF_on, upF_rel: the family's row at (p, s) has row p's condition and relation at s.
  quietOwn_upF, low_upF, tie_seatF, relLaw_upF: the like of quietOwn_up, of the readings, of
    tie_seat and of law_seat's step for a family.
  Since the links' rows go up as a family, up_atP, quietOwn_up, tie_seat and law_seat have no user
  outside this file; up serves the readings (low_…), which low_upF gathers.

Limits. Those of SeatsKeyD.lean. Besides, as premises: which rows stand at the borders; what each
piece holds (its block, its stretch, its errors along the maps); that the errors lie below the
bound.

-/
import Johnson.RunOne.Law.SeatsKeyD
import Johnson.Desc.Sound.KeySeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.SeatsAtFK
open Iop OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Block claimsIn viewWordsBelowPrime)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim LookupRecord lookupSeat caller layer layerOrder
  lookupPlace)
open Johnson.RunOne.Law.SeatsKeyD
open Lk6 (Dat pubOf)

variable {Fr : Frame} (P : Type)

/-- A row over the chain's own record, as a row over the pair. -/
def up (R : JointRow FirstState Fr) : JointRow (P × FirstState) Fr :=
  ⟨R.J, fun a => R.rd (a.1.2, a.2), fun a => R.inv (a.1.2, a.2)⟩

theorem up_atP (R : JointRow FirstState Fr) (p : P) : (up P R).atP p = R := rfl

/-- A tie over the record is a tie over the pair. -/
theorem quietOwn_up {b : Block FirstState Claim} {A B : JointRow FirstState Fr} (h : QuietTie b A B)
    :
    QuietOwn b (up P A) (up P B) :=
  fun _ s s' y rs gs ha hd => h s s' y rs gs ha hd

variable {P} {A : Dat GE} {sl : Slot → A.J} {stOf : FirstState → A.St} {I : FirstState → Prop} {Kc M
    Wp : Type}
  {R0 : IOR.Rels Kc A.St Fr.E (M × Wp)} {msg : M → A.J → GE} {c : ℕ}

theorem low_rowIn (h : ReadsLow A R0 c) :
    ReadsBelow c (up P (rowIn lookupSeat A stOf I R0 msg)).on ∧
      ReadsBelow c (up P (rowIn lookupSeat A stOf I R0 msg)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).1
  · exact exists_congr fun w => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).2 w

theorem low_rowOut {p : PG} {home : ℕ → Slot} (h : ReadsLow A R0 c) :
    ReadsBelow c (up P (rowOut lookupSeat p A sl home stOf I R0 msg)).on ∧
      ReadsBelow c (up P (rowOut lookupSeat p A sl home stOf I R0 msg)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact and_congr_left fun _ => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).1
  · exact exists_congr fun w => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).2 w

theorem low_row3 {one : OneTime} {i id : ℕ} {m : Wf.Matrix} {l : WfLookup} {oL kL : List ℕ}
    {idxN : ℕ} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ →
    GE}
    (h : ReadsLow A R0 c) :
    ReadsBelow c (up P (row3 one i id m l oL kL idxN A stOf R0 wd mx)).on ∧
      ReadsBelow c (up P (row3 one i id m l oL kL idxN A stOf R0 wd mx)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact and_congr_left fun _ => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).1
  · exact exists_congr fun w => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).2 w

variable {W : Type} (εs : ℝ≥0∞) (A0 : JointRow (P × FirstState) Fr)
  (ps : List (Piece (ckP .two) Fr (P × FirstState) Claim W)) (rs : List (JointRow (P × FirstState)
      Fr)) (j : ℕ)

/-- **A seat of a tie is filled**: the rows at its borders are two rows of ours, lifted. -/
theorem tie_seat {b : Block FirstState Claim} {X Y : JointRow FirstState Fr} (h : QuietTie b X Y)
    (hX : keyRowAt A0 rs j = up P X) (hY : keyRowAt A0 rs (j + 1) = up P Y)
    (hnd : (Fr.all.map (·.no)).Nodup)
    (hb : ∀ p, ps[j]? = some p → p.b = liftP P (below b) ∧ Err.Below p.err εs ∧
      ReadsBelow p.base (up P Y).on ∧ ReadsBelow p.base (up P Y).rel) :
    SeatGood εs A0 ps rs j :=
  seat_of_quiet εs A0 ps rs j b hnd (by rw [hY]; exact hb) (by rw [hX, hY]; exact quietOwn_up P h)

/-- **The seat of a proved typed block is filled**: the rows at its borders are two rows of ours,
lifted. -/
theorem law_seat {b : Block FirstState Claim} {X Y : JointRow FirstState Fr} (base : ℕ) (ds : List
    RDT) {JA JB : JK}
    (k : BK JA JB) (Mp : Maps ds k.R.red.shape) (rdA : FirstState × Fr.E.Str → JA.X × JA.E.Str)
    (h : RelLaw b base ds [] k Mp rdA X Y) (hX : keyRowAt A0 rs j = up P X)
    (hY : keyRowAt A0 rs (j + 1) = up P Y) (hk : k.Good) (hB : Nonempty JB.W) (hM : Mp.OK)
    (hp : ∀ p, ps[j]? = some p → ∃ ext,
      p = ⟨liftP P (below b), base, ds, [], ext, Mp.err k.err⟩)
    (hε : Err.Below (Mp.err k.err) εs) : SeatGood εs A0 ps rs j :=
  seat_of_relLaw εs A0 ps rs j b base ds [] k Mp (fun a => rdA (a.1.2, a.2)) hk hB hM rfl hp hε
    fun p => by
      rw [hX, hY, up_atP, up_atP]
      exact h

/-! ## A family of rows over what is handed to the chain -/

/-- **A family of rows over the chain's own record, one for each value that is handed to the chain,
as one row over the pair.** Its condition and its relation at (p, s) are those of row p at s. -/
def upF (R : P → JointRow FirstState Fr) : JointRow (P × FirstState) Fr :=
  JointRow.ofBorder (W := Unit) (fun a => (R a.1.1).on (a.1.2, a.2))
    fun a _ => (R a.1.1).rel (a.1.2, a.2)

theorem upF_on (R : P → JointRow FirstState Fr) (p : P) (s : FirstState) (y : Fr.E.Str) :
    (upF R).on ((p, s), y) ↔ (R p).on (s, y) :=
  ofBorder_on _ _ _

theorem upF_rel (R : P → JointRow FirstState Fr) (p : P) (s : FirstState) (y : Fr.E.Str) :
    (upF R).rel ((p, s), y) ↔ (R p).rel (s, y) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

/-- Ties over the record, one for each value, are a tie over the pair. -/
theorem quietOwn_upF {b : Block FirstState Claim} {X Y : P → JointRow FirstState Fr}
    (h : ∀ p, QuietTie b (X p) (Y p)) : QuietOwn b (upF X) (upF Y) :=
  fun p s s' y rs gs ha hd => by
    obtain ⟨h1, h2⟩ := h p s s' y rs gs ((upF_on X p s y).1 ha) hd
    exact ⟨(upF_on Y p s' y).2 h1, fun hr => (upF_rel X p s y).2 (h2 ((upF_rel Y p s' y).1 hr))⟩

/-- What each row of the family reads of the oracles, the family's row reads. -/
theorem low_upF {R : P → JointRow FirstState Fr} {c : ℕ}
    (h : ∀ p, ReadsBelow c (up P (R p)).on ∧ ReadsBelow c (up P (R p)).rel) :
    ReadsBelow c (upF R).on ∧ ReadsBelow c (upF R).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact ((upF_on R t.1 t.2 y).trans (iff_of_eq ((h t.1).1 t y y' h1 h2))).trans
      (upF_on R t.1 t.2 y').symm
  · exact ((upF_rel R t.1 t.2 y).trans (iff_of_eq ((h t.1).2 t y y' h1 h2))).trans
      (upF_rel R t.1 t.2 y').symm

/-- **A seat of a tie is filled**: the rows at its borders are two families of ours, lifted. -/
theorem tie_seatF {b : Block FirstState Claim} {X Y : P → JointRow FirstState Fr}
    (h : ∀ p, QuietTie b (X p) (Y p)) (hX : keyRowAt A0 rs j = upF X)
    (hY : keyRowAt A0 rs (j + 1) = upF Y) (hnd : (Fr.all.map (·.no)).Nodup)
    (hb : ∀ p, ps[j]? = some p → p.b = liftP P (below b) ∧ Err.Below p.err εs ∧
      ReadsBelow p.base (upF Y).on ∧ ReadsBelow p.base (upF Y).rel) :
    SeatGood εs A0 ps rs j :=
  seat_of_quiet εs A0 ps rs j b hnd (by rw [hY]; exact hb)
    (by rw [hX, hY]; exact quietOwn_upF h)

/-- A proved typed block between two rows of the families stands between the lifted rows at that
value: the law reads a row through its condition and its relation alone. -/
theorem relLaw_upF {b : Block FirstState Claim} {base : ℕ} {ds : List RDT} {back : List Fmt.RoundView}
    {JA JB : JK} {k : BK JA JB} {Mp : Maps ds k.R.red.shape}
    {rdA : FirstState × Fr.E.Str → JA.X × JA.E.Str} {X Y : P → JointRow FirstState Fr} (p : P)
    (h : RelLaw b base ds back k Mp rdA (X p) (Y p)) :
    RelLaw b base ds back k Mp rdA ((upF X).atP p) ((upF Y).atP p) where
  onIn := fun a ha => h.onIn a ((upF_on X p a.1 a.2).1 ha)
  relIn := fun a w ha hw => (upF_rel X p a.1 a.2).2 (h.relIn a w ((upF_on X p a.1 a.2).1 ha) hw)
  step := fun s s' y τ ha h1 hv h2 hd => by
    obtain ⟨b', e1, e2, e3⟩ := h.step s s' y τ ((upF_on X p s y).1 ha) h1 hv h2 hd
    exact ⟨b', e1, fun g => (upF_on Y p _ _).2 (e2 g), fun hr => e3 ((upF_rel Y p _ _).1 hr)⟩

end Johnson.RunOne.Law.SeatsAtFK

#print axioms Johnson.RunOne.Law.SeatsAtFK.low_rowOut
#print axioms Johnson.RunOne.Law.SeatsAtFK.tie_seat
#print axioms Johnson.RunOne.Law.SeatsAtFK.law_seat
#print axioms Johnson.RunOne.Law.SeatsAtFK.quietOwn_upF
#print axioms Johnson.RunOne.Law.SeatsAtFK.low_upF
#print axioms Johnson.RunOne.Law.SeatsAtFK.tie_seatF
#print axioms Johnson.RunOne.Law.SeatsAtFK.relLaw_upF
