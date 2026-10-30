-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Worth.lean: the kind "lookup" (K3): WHAT THE TABLE OF JOINTS' ITEMS worth "planes",
worth "keys", worth "rider" SAY AT A LOOKUP's ROW, AS DEFINITIONS; with the item "objects" in the
same form. General in the seat and in the caller. Definitions and two small statements.

OBJECT: no text that runs: definitions, meant as the filling of the table of joints' letter
  Meaning.worth at the lookups' rows.
USER: k3_att_t3, attBehind_items (Johnson/Desc/First/Look/K3CallsTies.lean), k3_lay_t3,
  layBehind_items (K3LayTies.lean). Of the table's filling: worthDig
  (Johnson/Desc/First/Look/K3FillWorth.lean).
LETTERS: fork, heard := a seat's two readers; h, lm, first := the place's; nu, Kv, ms, st := the
  caller's readings of a witness and of the record.

Why. The table's letter Meaning.worth is left to the kind named in the rows. The lookup's
own law ends in the row out (K3Out, Johnson/Top/H/K3RowOut.lean; K3OutRider,
Johnson/Top/H/K3RowOutRider.lean) at a ledger and a heard record that stand under an "there is". An
item must be a sentence on a statement's record and a witness alone: so each names no heard record
of its own: it speaks AT WHATEVER LEDGER AND HEARD RECORD THE RECORD HOLDS.

Main names (fork, heard: the seat's two readers; nu, Kv, ms: how the caller reads a witness: the
places, the key vectors, the tuple of messages):
  `K3Objects`: every residue of the sumchecks' rows is 0.
  `K3WorthPlanes`: the planes' matrix at its two points and the counts are worth what lies under
    the lookup's slots.
  `K3WorthKeys`: each call's key vector at its point likewise.
  `K3WorthRider`: the caller's identity at the lookup's key point holds.
  `k3Out_of_worth`, `k3Worth_of_out`: with a ledger and a heard record in the record these are the
    row out, both ways. `k3WorthPlanes_of_out`, `k3WorthKeys_of_out`, `k3WorthRider_of_out`: one
    item, from its sentence at the ledger and the heard record that the record holds: what a row
    that closes the item calls.

Limits. WHERE THE RECORD HOLDS NO LEDGER OR NOTHING HEARD EACH ITEM IS TRUE OF EVERY WITNESS. THE
DEFINITIONS STAND ON THIS TERM: the table's promise says that both are there
(its public items ledger, look, lookOut) at every border at which an item worth is open: whoever
spends or closes an item takes the ledger and the heard record FROM THAT PROMISE. Each item speaks
at all rounds for which the heard record stands: at a heard record that stands for none it is true
of every witness.
WHO CLOSES THESE ITEMS (the calling kind's rows) is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RowOutRider

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel

section
variable {S W : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
  (h : FoNums.Sh) (lm first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) (Kv : W → ℕ → ℕ → Cb.Gl.E)

/-- The item "objects". -/
def K3Objects (s : S) (w : W) : Prop :=
  ∀ g F', fork s = some F' → heard s = some g → K3OutRows h lm first (nu w) Reading.gl g F'

/-- **worth "planes".** -/
def K3WorthPlanes (s : S) (w : W) : Prop :=
  ∀ g F', fork s = some F' → heard s = some g → K3OutPlanes h lm first (nu w) Reading.gl g F'

/-- **worth "keys".** -/
def K3WorthKeys (s : S) (w : W) : Prop :=
  ∀ g F', fork s = some F' → heard s = some g →
    K3OutKeys h lm first (nu w) (Kv w) Reading.gl g F'

/-- One item, from its sentence at the ledger and the heard record that the record holds. -/
theorem k3WorthPlanes_of_out {s : S} {w : W} {g : Forest.Heard} {F' : Fork}
    (hf : fork s = some F') (hh : heard s = some g)
    (hK : K3OutPlanes h lm first (nu w) Reading.gl g F') :
    K3WorthPlanes fork heard h lm first nu s w := by
  intro g₁ F₁ a b
  obtain rfl : F' = F₁ := Option.some.inj (hf.symm.trans a)
  obtain rfl : g = g₁ := Option.some.inj (hh.symm.trans b)
  exact hK

theorem k3WorthKeys_of_out {s : S} {w : W} {g : Forest.Heard} {F' : Fork}
    (hf : fork s = some F') (hh : heard s = some g)
    (hK : K3OutKeys h lm first (nu w) (Kv w) Reading.gl g F') :
    K3WorthKeys fork heard h lm first nu Kv s w := by
  intro g₁ F₁ a b
  obtain rfl : F' = F₁ := Option.some.inj (hf.symm.trans a)
  obtain rfl : g = g₁ := Option.some.inj (hh.symm.trans b)
  exact hK

/-- With a ledger and a heard record in the record, the three are the row out. -/
theorem k3Out_of_worth {s : S} {w : W} {g : Forest.Heard} {F' : Fork} (hf : fork s = some F')
    (hh : heard s = some g) (h1 : K3Objects fork heard h lm first nu s w)
    (h2 : K3WorthPlanes fork heard h lm first nu s w)
    (h3 : K3WorthKeys fork heard h lm first nu Kv s w) :
    K3Out h lm first (nu w) (Kv w) Reading.gl g F' :=
  ⟨h1 g F' hf hh, h2 g F' hf hh, h3 g F' hf hh⟩

/-- And back. -/
theorem k3Worth_of_out {s : S} {w : W} {g : Forest.Heard} {F' : Fork} (hf : fork s = some F')
    (hh : heard s = some g) (hK : K3Out h lm first (nu w) (Kv w) Reading.gl g F') :
    K3Objects fork heard h lm first nu s w ∧ K3WorthPlanes fork heard h lm first nu s w ∧
      K3WorthKeys fork heard h lm first nu Kv s w := by
  have key : ∀ g₁ F₁, fork s = some F₁ → heard s = some g₁ → F' = F₁ ∧ g = g₁ :=
    fun g₁ F₁ a b => ⟨Option.some.inj (hf.symm.trans a), Option.some.inj (hh.symm.trans b)⟩
  refine ⟨fun g₁ F₁ a b => ?_, fun g₁ F₁ a b => ?_, fun g₁ F₁ a b => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := key g₁ F₁ a b
  · exact hK.1
  · exact hK.2.1
  · exact hK.2.2

end

/-- **worth "rider".** st: the caller's state, read off the record; ms: its tuple of messages, read
off the witness. -/
def K3WorthRider {S W : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (r : LookupCRCaller) (lm first : ℕ) (st : S → r.c.St₀) (ms : W → r.c.Sg.Msg) (s : S) (w : W) :
    Prop :=
  ∀ g F', fork s = some F' → heard s = some g → K3OutRider r lm first (st s) (ms w) g F'

theorem k3WorthRider_of_out {S W : Type} {fork : S → Option Fork}
    {heard : S → Option Forest.Heard} {r : LookupCRCaller} {lm first : ℕ} {st : S → r.c.St₀}
    {ms : W → r.c.Sg.Msg} {s : S} {w : W} {g : Forest.Heard} {F' : Fork} (hf : fork s = some F')
    (hh : heard s = some g) (hK : K3OutRider r lm first (st s) (ms w) g F') :
    K3WorthRider fork heard r lm first st ms s w := by
  intro g₁ F₁ a b
  obtain rfl : F' = F₁ := Option.some.inj (hf.symm.trans a)
  obtain rfl : g = g₁ := Option.some.inj (hh.symm.trans b)
  exact hK

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3WorthPlanes_of_out
#print axioms VerifiableInference.OnPublicFiles.k3WorthKeys_of_out
#print axioms VerifiableInference.OnPublicFiles.k3WorthRider_of_out
#print axioms VerifiableInference.OnPublicFiles.k3Out_of_worth
#print axioms VerifiableInference.OnPublicFiles.k3Worth_of_out
