-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RidesK5.lean: CONDITIONAL: five of the six sorts of items that ride past
the block of an attention segment's own rounds (kind K5) say, of every state that `K5Keeps`
(Johnson/Desc/K5/Honest/Law/Returns.lean) ties to the state in front, and at any strings, what they
say in front. Rules over letters: the meaning is a letter, under one equation a field.

Which items ride is the library's test `riderB` (Johnson/Desc/First/Att/K05Riders.lean): the pile;
the parts of OTHER segments' relations; the index masks' pin; the open segment's own classes of
rows; the lookup's forms "objects"; and, beside these five, "no mark". The sixth sort, the forms
"objects", reads the open ledger, which the block turns: it is not in this file.

What each sort reads, by its text:
  "no mark": the mark of failure.
  `row m c` (`rowSays`, Johnson/Desc/First/Close/Law/FillRow.lean, at the reader `wordsAtFirst`):
    the statement and the book.
  `pile` (`RowsTrue`, Johnson/Desc/K13/Law/Letters.lean): the pending rows, and a letter rw.
  `constr n p` (`P5J.constrQAt`, Johnson/P5J/MeansQ.lean), p not the digits' part: the request, the
    decoded table, and at the head's segment a letter headPart. By the library's
    `constrQAt_back_any` (Johnson/Desc/Sound/ConstrRidesHead.lean), called at the relation turned
    round (`goesOn_iff_back`, Johnson/Desc/K5/Honest/Law/GoesOn.lean).
  `pinI`: the meaning's field `pin`: a premise here.

Main names:
  `relK5`: the relation: the public part is the same, `K5Keeps` ties the states; the strings free.
  `relK5Y`: the narrower relation: the two strings are tied by a letter Y. An honest run's strings
    in front of and behind a step are not free: they agree at the stored table and at the trees
    already sent.
  `keeps_reads`: whatever reads the state through the library's `restO` alone is kept.
  `mark_on`, `row_on`, `pile_on`, `constr_on`: a sort each.
  `riders_on`: **every rider but the forms "objects"**.

Who is meant to show the premises. The equations on the fields: by the meaning's make. hrw, hreq:
whoever lays these two letters: each reads nothing that the block turns. hdec: it holds of a decoder
that reads NEITHER THE STRINGS nor what the block turns (both strings are free in it): the honest
side's constant one; NOT of the library's own decoder, which reads the strings. hh: whoever writes
the head's part of the relation. hI: whoever says what a pin says on the honest side.

Limits. That any meaning meets the premises is not shown here. Nothing is said of the forms
"objects", of the items that the block's row shuts or owes, or of any other block.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.GoesOn
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.First.Att.K05Riders
import Johnson.Desc.First.Att.Door.Law.FillK5Pile
import Johnson.Desc.First.Att.Door.Law.FillK5Row
import Johnson.Desc.Sound.ConstrRidesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S Item Part RowClass Meaning Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.First.Att.P (restO ReadsRest riderB)
open VerifiableInference.Desc.Sound (MsgT GoesBack constrQAt_back_any)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13 RowsTrue)

/-- **The relation of the kind's step**: the public part is the same; `K5Keeps` ties the state in
front to the state behind; of the strings nothing is asked. -/
def relK5 (P : Type) : Rel P := fun a _ b _ => a.1 = b.1 ∧ K5Keeps a.2 b.2

/-- The narrower relation: beside `relK5`, the two strings are tied by Y, a letter. For a sentence
that reads a string. -/
def relK5Y (P : Type) (Y : Strs → Strs → Prop) : Rel P :=
  fun a y b y' => a.1 = b.1 ∧ K5Keeps a.2 b.2 ∧ Y y y'

/-- It is narrower. No premise. -/
theorem relK5Y_le (P : Type) (Y : Strs → Strs → Prop) (a : P × S) (y : Strs) (b : P × S)
    (y' : Strs) (h : relK5Y P Y a y b y') : relK5 P a y b y' := ⟨h.1, h.2.1⟩

/-- Whatever reads the state through the rest alone is kept. Conditional: hf; K. -/
theorem keeps_reads {X : Type} {f : S → X} (hf : ReadsRest f) {s s' : S} (K : K5Keeps s s') :
    f s = f s' := hf s s' K.1.symm

/-- The pending rows on the table are kept. Conditional: K. -/
theorem keeps_rows {s s' : S} (K : K5Keeps s s') : s.rows = s'.rows := by
  obtain ⟨_, a, a', e, e', _⟩ := K
  have ho : s.out = s'.out := keeps_reads VerifiableInference.Desc.First.Att.P.rest_out
    ⟨‹restO s' = restO s›, a, a', e, e', ‹_›⟩
  unfold S.rows
  rw [e, e', ho]

section
variable {P : Type}

/-- "No mark" goes on. -/
theorem mark_on {W : Type} : GoesOn (W := W) (relK5 P) (fun a _ _ => a.2.failed = none) :=
  fun _ _ _ _ _ hr h =>
    (keeps_reads VerifiableInference.Desc.First.Att.P.rest_failed hr.2).symm.trans h

variable {Cells Tok : Type}

/-- **The open segment's classes of rows go on.** Conditional: hrow: the field's make. -/
theorem row_on (Mg : Meaning P (Wit Cells Tok MsgT)) (N : Numbers) (arr : ℕ → ℕ → ℕ)
    (hrow : Mg.row = rowSays N (wordsAtFirst arr)) (m : ℕ) (c : RowClass) :
    GoesOn (relK5 P) (Mg.row m c) := by
  rw [hrow]
  intro a y b y' w hr h
  have e1 : a.2.st = b.2.st := keeps_reads VerifiableInference.Desc.First.Att.P.rest_st hr.2
  have e2 : a.2.book = b.2.book := keeps_reads VerifiableInference.Desc.First.Att.P.rest_book hr.2
  unfold rowSays wordsAtFirst VerifiableInference.Desc.First.classRows at h ⊢
  rw [← e1, ← e2]
  exact h

/-- **The pile goes on.** Conditional: hpile: the field's make; hrw: the letter rw reads nothing
that the kind's step turns. -/
theorem pile_on {W : Type} {nR : ℕ} (Mg Mg0 : Meaning P W) (D13 : DataK13 P W nR)
    (hpile : Mg.pile = (fillK13 D13 Mg0).pile)
    (hrw : ∀ a b : P × S, a.1 = b.1 → K5Keeps a.2 b.2 → D13.rw a = D13.rw b) :
    GoesOn (relK5 P) Mg.pile := by
  rw [hpile]
  intro a y b y' w hr h
  have h' : RowsTrue (D13.rw a) a.2 w := h
  show RowsTrue (D13.rw b) b.2 w
  rw [← hrw a b hr.1 hr.2]
  unfold RowsTrue at h' ⊢
  rw [← keeps_rows hr.2]
  exact h'

/-- **The parts of the segments' relations go on**, the digits' part aside. Conditional: hc: the
field's make; hreq, hdec: the request and the decoded table are read off what the kind's step
leaves; hh: the head's part goes on. -/
theorem constr_on {X : Model.Verify.Public} {W : Type} {rows cols : ℕ} (Mg : Meaning P W) (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → Cm.Idx → P × S → Strs → W → Prop)
    (digitsPart : ℕ → P × S → Strs → W → Prop)
    (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hreq : ∀ a b : P × S, a.1 = b.1 → K5Keeps a.2 b.2 → H.req a = H.req b)
    (hdec : ∀ (a b : P × S) y y', a.1 = b.1 → K5Keeps a.2 b.2 → H.dec a y = H.dec b y')
    (hh : ∀ p i, GoesOn (relK5 P) (headPart p i)) (m : ℕ) (p : P5J.TPart) (hp : p ≠ .lookDigits) :
    GoesOn (relK5 P) (Mg.constr m p) := by
  rw [hc]
  exact (goesOn_iff_back _ _).2 (constrQAt_back_any hd put H headPart digitsPart m p hp
    (relK5 P).turned (fun a _ b _ hr => (hreq b a hr.1 hr.2).symm)
    (fun a y b y' hr => (hdec b a y' y hr.1 hr.2).symm)
    (fun i => (goesOn_iff_back _ _).1 (hh p i)))

/-- **Every rider but the forms "objects" goes on**, over any relation rel that is narrower than
`relK5`. i: "no mark", or an item that passes the library's test `riderB` at the segment's number m
and is no item of forms. Conditional: hrel; a premise a sort: hC, hR, hP: three sorts' sentences go
on over `relK5`, the strings free (`constr_on`, `row_on`, `pile_on` show them under their own
premises); hI: the index masks' pin goes on OVER rel: a premise on the meaning's field `pin`, THE
ONE FIELD HERE THAT MAY READ A STRING: so rel may say of the strings what that field needs
(`relK5Y`). -/
theorem riders_on {W : Type} (N : Numbers) (Mg : Meaning P W) (m : ℕ) (rel : Rel P)
    (hrel : ∀ a y b y', rel a y b y' → relK5 P a y b y')
    (hC : ∀ n p, n ≠ m → p ≠ .lookDigits → GoesOn (relK5 P) (Mg.constr n p))
    (hI : GoesOn rel (Mg.pin N.index.1 N.index.2))
    (hR : ∀ c, GoesOn (relK5 P) (Mg.row m c)) (hP : GoesOn (relK5 P) Mg.pile) (i : Item)
    (hi : i = .unmarked ∨ riderB m i = true) (hd : ∀ n, i ≠ .constr n .lookDigits)
    (hf : ∀ n k r, i ≠ .formsT n k r) : GoesOn rel (i.holds N Mg) := by
  rcases hi with rfl | hi
  · exact mark_on.mono hrel
  · cases i with
    | pile => exact hP.mono hrel
    | constr n q =>
      simp only [riderB, bne_iff_ne, ne_eq] at hi
      exact (hC n q hi (fun e => hd n (by rw [e]))).mono hrel
    | pinI => exact hI
    | row n c =>
      simp only [riderB, beq_iff_eq] at hi
      subst hi
      exact (hR c).mono hrel
    | formsT n k r => exact absurd rfl (hf n k r)
    | _ => exact absurd hi (by simp [riderB])

end

end H2K5.Honest

#print axioms H2K5.Honest.relK5Y_le
#print axioms H2K5.Honest.keeps_reads
#print axioms H2K5.Honest.keeps_rows
#print axioms H2K5.Honest.mark_on
#print axioms H2K5.Honest.row_on
#print axioms H2K5.Honest.pile_on
#print axioms H2K5.Honest.constr_on
#print axioms H2K5.Honest.riders_on
