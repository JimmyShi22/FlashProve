-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsFwd.lean: THE EXCHANGE ACROSS A SEGMENT's SECOND SENDING,
FORWARD: from "the forms of a run are worth 0, in front of the second sending" (formsTQ,
Johnson/Desc/Sound/FormsQ.lean) to "the forms of a run are worth 0" behind it (formsQ). The library
has the other direction (formsTQ_of_formsQ, Johnson/Desc/Sound/FormsT.lean). Statements and proofs,
over files of the library alone. No definition.

WHY IT GOES. The library's proof rests on an EQUATION of two worths (value_ridesW,
Johnson/Desc/Sound/FormsQ.lean). ONE PREMISE CHANGES SIDES: the public test in front (formsInT) is
no premise here: the sentence formsTQ holds it (formsTQ_in, Johnson/Desc/Sound/BordersForms.lean);
the public test BEHIND (formsIn, at the wider list of seats) is one: the sentence formsQ must hold
it, and without it the end fails (formsQ_outside, Johnson/Desc/Sound/FormsQ.lean).

  formsQ_of_formsTQ   the library's binders, with that one change
  formsQ_of_arm       the premise on the cells cut in three (Johnson/Desc/Sound/StatedCell.lean)
  formsQ_of_step      over a step that rides (Rides): as Johnson/Desc/K1/Law/ExchangeStep.lean
  formsQ_over_send    over a sending: every public premise in the form in which a forward law lies
                      (rides_of_rec, formsIn_new: Johnson/Desc/K1/Law/GoAtLaterForms.lean)
  forms_of_formsT     THE ITEM, at the library's filling meaningForms, general in its letters:
                      formsT m k r at x gives forms m k r at x', under formsQ_over_send's premises
                      at each run of the item and two more: hah (no run of the item bears the mark
                      "ahead", D.ah) and hwt (at r = "weights" the letter wt goes from x to x')
  segRow_reads, early_no_eq, reads_shuts   the table's row at a segment's reads: every item forms
                      that it owes has its item formsT among those that it shuts, and none of its
                      runs bears the name "K8.equations"
  late_has_eq         early_no_eq's test can fail: at the run "small" of the piece behind the reads

Wherever a witness stands in a statement (rd, w) it is a bound variable.

Limits. THE WEIGHT IS A PREMISE: ArmCell | ArmCellIn (Johnson/Desc/Sound/StatedCell.lean,
Johnson/Desc/Sound/StatedCellIn.lean): at each entry of an array of the second sending that a form
names, the committed cell, read behind, is the kind's stated function in front. It is proved here
of no state and no witness; asked of every witness it cannot hold (armCellIn_not_both,
Johnson/Desc/K1/Law/ArmHalves.lean). No pair of states is given at which the premises hold
together. At a reader that answers nothing formsTQ is false and these lemmas say nothing. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ExchangeStep
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.Sound.StatedCellIn
import Johnson.Desc.Sound.BordersForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart Item PubData Meaning segRow shift earlyRuns runsOf)
open VerifiableInference.Desc.K9 (segAt? seatAt Read Readers formsIn formsInT affInT mergeOf)
open VerifiableInference.Desc.Sound (MsgQ dataQ Rides Stated UFn StatedIs ArmCell ArmCellIn
  OtherCells formsQ formsTQ value_ridesW hcell_of_arm formsTQ_in armCell_of_in seatTab)
open VerifiableInference.Desc.K1 (RecRides SecondFound ReadersStay rides_of_rec formsIn_new
  otherCells_of_rides hmask_of_rides)

/-- **THE EXCHANGE, FORWARD.** The binders of formsTQ_of_formsQ, but: formsInT at s is gone; hin' is
new; the sentence in hand and the end change places. -/
theorem formsQ_of_formsTQ (Rd : Readers) (St : Stated) (own own' : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin' : formsIn Rd own' piece run s' = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hcell : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (dataQ own' b rd).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx)
    (hmask : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQ own' b rd).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1)
    (h : formsTQ Rd St own piece run s rd) : formsQ Rd own' piece run s' rd := by
  obtain ⟨a', R, ha', hs, _, hf⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hs' : Rd.forms piece run s' = some R := hl.trans hs
  unfold formsIn at hin'
  rw [hb, hs'] at hin'
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin'
  refine ⟨b, R, hb, hs', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  have h2 := (hf f hm).1
  unfold affInT at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [value_ridesW own (mergeOf s) R.late a' b (St.at1 s (dataQ own a' rd)) (dataQ own' b rd)
    harr hfill f (List.all_eq_true.1 h3) (hcell R hs f hm) (hmask R hs f hm)]
  exact (hf f hm).2

/-- With the premise on the cells cut as in formsTQ_of_arm. -/
theorem formsQ_of_arm (Rd : Readers) (St : Stated) (u : UFn) (own own' : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (hSt : StatedIs St u s)
    (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin' : formsIn Rd own' piece run s' = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (h2 : ArmCell Rd own own' piece run s a b rd u) (h1 : OtherCells Rd own own' piece run s a b rd)
    (hmask : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQ own' b rd).mask x.1 = (dataQ own a rd).mask x.1)
    (h : formsTQ Rd St own piece run s rd) : formsQ Rd own' piece run s' rd :=
  formsQ_of_formsTQ Rd St own own' piece run s s' a b rd ha hb hl hin' harr hfill
    (hcell_of_arm Rd own own' piece run s a b rd St u hSt h2 h1)
    (fun R hR f hf x hx => by rw [hSt.mask]; exact hmask R hR f hf x hx) h

/-- Over a step that rides: formsTQ_of_step turned. -/
theorem formsQ_of_step (Rd : Readers) (St : Stated) (u : UFn) (own own' : List (ℕ × ℕ))
    (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (hsub : ∀ x ∈ own, x ∈ own') (hSt : StatedIs St u s) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin' : formsIn Rd own' piece run s' = true) (hr : Rides own a b)
    (h2 : ArmCell Rd own own' piece run s a b rd u) (h : formsTQ Rd St own piece run s rd) :
    formsQ Rd own' piece run s' rd :=
  have hin : formsInT Rd own piece run s = true := formsTQ_in St Rd own piece run s rd h
  formsQ_of_arm Rd St u own own' piece run s s' a b rd hSt ha hb hl hin' hr.arrays hr.filled h2
    (otherCells_of_rides own own' Rd piece run s a b rd hsub ha hin hr)
    (hmask_of_rides own own' Rd piece run s a b rd hsub ha hin hr) h

/-- Over a sending: every public premise in the form in which a forward law lies. -/
theorem formsQ_over_send {new : List ℕ} (Rd : Readers) (St : Stated) (u : UFn)
    (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S) (rd : ℕ × ℕ → MsgQ)
    (hsub : ∀ x ∈ own, x ∈ own') (hSt : StatedIs St u s) (R : RecRides new s s')
    (g : Grows s.st s'.st) (hfull : s.book.place.size = s.st.oracles.size)
    (hRd : ∀ X, Rd.forms piece run s = some X → Rd.forms piece run s' = some X)
    (hseat : ∀ o ∈ new, (seatAt own' s'.book o).isSome = true) (hfound : SecondFound new s s')
    (hArm : ∀ a b, segAt? s = some a → segAt? s' = some b →
      ArmCellIn Rd own own' piece run s a b rd u)
    (h : formsTQ Rd St own piece run s rd) : formsQ Rd own' piece run s' rd := by
  have hin : formsInT Rd own piece run s = true := formsTQ_in St Rd own piece run s rd h
  obtain ⟨a, R₀, ha, hs, _, _⟩ := id h
  obtain ⟨b, hb, _, hr, _⟩ := rides_of_rec R g hfull own ha
  have hl : Rd.forms piece run s' = Rd.forms piece run s := by rw [hs, hRd R₀ hs]
  exact formsQ_of_step Rd St u own own' piece run s s' a b rd hsub hSt ha hb hl
    (formsIn_new R Rd hsub piece run hRd hseat hfound hin) hr
    (armCell_of_in Rd own own' piece run s a b rd u ha hin (hArm a b ha hb)) h

/-- **THE ITEM**, at the library's filling, general in its letters: formsT m k r at x gives forms m
k r at x'. Beside formsQ_over_send's premises at each run of the item: hah: no run of the item bears
the mark "ahead" (D.ah); hwt: at r = "weights" the letter wt goes from x to x'. -/
theorem forms_of_formsT {new : List ℕ} (D : PubData) {Cells Tok Pp : Type} (arr : ℕ → ℕ → ℕ)
    (ms : List Sound.Mem) (St : Stated) (u : UFn) (after : ℕ → S → Except String S)
    (wt : ℕ → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop) (rwB : ℕ → S → Bool)
    (Mg : Meaning Pp (Wit Cells Tok Sound.MsgT)) (x x' : Pp × S) (y y' : Strs)
    (w : Wit Cells Tok Sound.MsgT) (m k : ℕ) (r : String) (hSt : StatedIs St u x.2)
    (R : RecRides new x.2 x'.2) (g : Grows x.2.st x'.2.st)
    (hfull : x.2.book.place.size = x.2.st.oracles.size)
    (hah : ∀ p ∈ D.runs m k r, D.ah p.1 p.2 = false) (hRd : ReadersStay D m k r x.2 x'.2)
    (hseat : ∀ o ∈ new, (seatAt (D.N.group m) x'.2.book o).isSome = true)
    (hfound : SecondFound new x.2 x'.2)
    (hArm : ∀ p ∈ D.runs m k r, ∀ a b, segAt? x.2 = some a → segAt? x'.2 = some b →
      ArmCellIn (D.Rd m) (D.N.sent m 0) (D.N.group m) p.1 p.2 x.2 a b (seatTab D.cs arr ms w) u)
    (hwt : r = "weights" → wt m x y w → wt m x' y' w)
    (h0 : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).formsT
      m k r x y w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms
      m k r x' y' w := by
  have hsub : ∀ z ∈ D.N.sent m 0, z ∈ D.N.group m := fun z hz => by
    unfold First.Numbers.group
    exact List.mem_append_left _ (List.mem_append_left _ hz)
  refine ⟨fun p hp => ?_, fun e => hwt e (h0.2 e)⟩
  rw [if_neg (by rw [hah p hp]; exact Bool.false_ne_true)]
  exact formsQ_over_send (D.Rd m) St u (D.N.sent m 0) (D.N.group m) p.1 p.2 x.2 x'.2 _ hsub hSt R
    g hfull (hRd p hp) hseat hfound (hArm p hp) (h0.1 p hp)

/-! ## The table's row at a segment's reads -/

/-- What the row shuts and what it owes, by the table's text. -/
theorem segRow_reads (sub : ModelPart) (m : ℕ) :
    (segRow sub m (4 + shift sub)).ins = (earlyRuns sub).map (fun x => Item.formsT m x.1 x.2) ∧
      (segRow sub m (4 + shift sub)).outs = Item.pin m 1 :: Item.row m (.sample 1) :: Item.tie m ::
        (earlyRuns sub).map fun x => Item.forms m x.1 x.2 := by
  cases sub <;> exact ⟨rfl, rfl⟩

/-- A closed fact on the table's three sorts of segment, by evaluation in Lean's kernel. -/
theorem early_no_eq (sub : ModelPart) : ((earlyRuns sub).all fun x =>
          (runsOf sub x.1 x.2).all fun p => !(p.2 == "K8.equations")) = true := by
  cases sub <;> decide +kernel

/-- That test can fail: the run "small" of the piece behind the reads bears the name. -/
theorem late_has_eq (sub : ModelPart) : ((runsOf sub (5 + shift sub) "small").all fun p =>
          !(p.2 == "K8.equations")) = false := by
  cases sub <;> decide +kernel

/-- **Every item forms that the row owes has its item formsT among those that the row shuts**, and
none of its runs bears the name "K8.equations". General in the sort and in m. -/
theorem reads_shuts (sub : ModelPart) (m j : ℕ) (n : String)
    (h : Item.forms m j n ∈ (segRow sub m (4 + shift sub)).outs) :
    Item.formsT m j n ∈ (segRow sub m (4 + shift sub)).ins ∧
      ∀ p ∈ runsOf sub j n, (p.2 == "K8.equations") = false := by
  rw [(segRow_reads sub m).2] at h
  rw [(segRow_reads sub m).1]
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with h | h | h | ⟨x, hx, h⟩
  · cases h
  · cases h
  · cases h
  · injection h with _ h1 h2
    subst h1 h2
    refine ⟨List.mem_map.2 ⟨x, hx, rfl⟩, fun p hp => ?_⟩
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 (early_no_eq sub) x hx) p hp
    cases hb : (p.2 == "K8.equations") with
    | false => rfl
    | true =>
      rw [hb] at h3
      cases h3

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.formsQ_of_formsTQ
#print axioms ProofFile.Honest.K1.formsQ_of_arm
#print axioms ProofFile.Honest.K1.formsQ_of_step
#print axioms ProofFile.Honest.K1.formsQ_over_send
#print axioms ProofFile.Honest.K1.forms_of_formsT
#print axioms ProofFile.Honest.K1.segRow_reads
#print axioms ProofFile.Honest.K1.early_no_eq
#print axioms ProofFile.Honest.K1.late_has_eq
#print axioms ProofFile.Honest.K1.reads_shuts
