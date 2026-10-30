-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRowsPlain.lean: A FILLED SEAT IN THE PLAIN FORM'S OWN COIN: from seats that
are filled in the knowledge form (`SeatGood`, Johnson/Desc/Sound/KeySeatsAt.lean) to the plain
rule's premise `EachLeads` (Johnson/Desc/Plain/FoldChain.lean).

The question. A carried typed block pays a lost promise in its counts: it gives "(true behind, or
the promise behind is lost) → true in front", not "the promise behind is kept". Does the plain
rule's fold bear that?

The answer. YES, AS IT IS TYPED: its premise `EachLeads on Q` is general in the conditions and the
relations. Take as the condition at a border "THE STATEMENT IS FALSE": in the row's condition, and
the row's relation does not hold (`falseAt`); as a block's relation "what is put out is false".
  `leads_of_good`: a piece that is good between two rows leads from false to false.
  `eachLeads_of_seats`: all seats of a chain filled give `EachLeads`.
The like for the form with promises and claims: Johnson/Desc/Sound/KeyRowsKeeps.lean
[not in this library].

What does not go over. `Keeps.beside` (a claim that is only carried rides past a block at no cost)
wants the promise kept at true statements: files that lean on it owe `Keeps` at their own tables.
A `SeatGood` seat carries the whole of what is open in its own rows.

Limits. Forms. Nothing is filled here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeySeatsAt
import Johnson.Desc.Sound.KeyLeads
import Johnson.Desc.Plain.FoldChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Plain
open _root_.Run (ckP)
open _root_.Iop (Err Reduction)

section
variable {S Cl W : Type} {F : Frame}

/-- The statement is false at the row: in its condition, and its relation does not hold. -/
def falseAt (R : JointRow S F) (a : S × F.E.Str) : Prop := R.on a ∧ ¬ R.rel a

/-- **A piece that is good between two rows leads from false to false.** -/
theorem leads_of_good [Inhabited W] (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good) :
    p.ior.red.Leads (falseAt A) (fun _ b => falseAt B b) p.err :=
  fun a ha => outright_leads_false p A B h a ha

/-- **All seats of a chain filled give the plain rule's premise.** -/
theorem eachLeads_from [Inhabited W] (εs : ℝ≥0∞) (A : JointRow S F) (rs : List (JointRow S F)) :
    ∀ (l : List (Piece (ckP .two) F S Cl W)) (j : ℕ),
    (∀ i (p : Piece (ckP .two) F S Cl W), l[i]? = some p →
      (p.bk (keyRowAt A rs (j + i)).on (keyRowAt A rs (j + i + 1)).on
        (fun a _ => (keyRowAt A rs (j + i)).rel a)
        (fun a _ => (keyRowAt A rs (j + i + 1)).rel a)).Good) →
    EachLeads (fun i => falseAt (keyRowAt A rs i))
      (fun i _ b => falseAt (keyRowAt A rs (i + 1)) b) j l
  | [], _, _ => trivial
  | p :: l, j, h =>
    ⟨leads_of_good p _ _ (h 0 p List.getElem?_cons_zero), fun _ _ _ hq => hq,
      eachLeads_from εs A rs l (j + 1) fun i q hq => by
        have e := h (i + 1) q (List.getElem?_cons_succ.trans hq)
        have e1 : j + (i + 1) = j + 1 + i := by omega
        rw [e1] at e
        exact e⟩

theorem eachLeads_of_seats [Inhabited W] (εs : ℝ≥0∞) (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F))
    (g : ∀ i, i < ps.length → SeatGood εs A ps rs i) :
    EachLeads (fun i => falseAt (keyRowAt A rs i))
      (fun i _ b => falseAt (keyRowAt A rs (i + 1)) b) 0 ps :=
  eachLeads_from εs A rs ps 0 fun i p hp => by
    have hi : i < ps.length := (List.getElem?_eq_some_iff.1 hp).1
    have e := (g i hi p hp).1
    rw [Nat.zero_add]
    exact e

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.leads_of_good
#print axioms VerifiableInference.Desc.Sound.eachLeads_of_seats
