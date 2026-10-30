-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StatedAll.lean: THE LETTER St OF THE SENTENCE "formsT" (Johnson/Desc/Sound/FormsQ.lean: Stated; as a term: Stated.of u, Johnson/Desc/Sound/FormsT.lean) FOR ALL SORTS OF SEGMENT AT ONCE: ONE u, ONE St, THREE ARMS BY THE SORT OF THE RECORD's OPEN SEGMENT. Definitions and theorems.
WHY. "formsT" passes the data through St.at1: each array of a segment's second sending is set to its STATED FUNCTION of the first sending's arrays. Each hearing kind has its own formula, over ITS OWN MAKER of the tables in front of the sending (at the one border at which "formsT" is open the record's own list of tables is still the open one: so u may not read it), and asks of St a sentence at its own term. One formula for all sorts would make two of the three kinds' files owe a bridge from their text to it.
  linkNo s: the open link's number, off the record.
  uBySort uL uA uH: at a layers' | an attention | the head's segment: that arm, handed the link's number; elsewhere 0. THE THREE ARMS ARE LETTERS HERE: meant: each kind's own term off the public record.
  StatedIs St u s: what a kind asks of St at a record s, general in its u: the mask row is kept · at an array of the second sending the cell is u's · every other cell is the data's own.
  stated_lay | stated_att | stated_head: AT A RECORD OF THAT SORT Stated.of (uBySort …) IS THAT ARM's: by unfolding.
  statedIs_can_fail: a control on the statement: the identity on the data is no such St where u parts from the data.
  u reads the record and the data alone: BY ITS TYPE: no witness is handed to it.
"ONE FORMULA WITH THE LIST OF TABLES BY THE SORT" IS AN INSTANCE: the three arms at one text.

Limits. (1) WHAT THIS CUT MOVES: the exchange at the block behind the second sending ("forms" and the smallness test's tie behind give "formsT" in front: formsTQ_of_formsQ's hcell) THEN WANTS ONE BRIDGE A SORT: "the tie at the record behind, and the kind's law on the tables, give: the array of the reads at (r, i) is that kind's arm at the record in front": EACH KIND's FILES ARE ASKED FOR ONE LEMMA: "my arm is the sum over j below the table's length of the weight j times the unpacked symbol, at the place that the numbering of places gives, over the tables that stand in the record behind". OWED, ARM BY ARM. (2) Between the lookup on the calls and the kind's own block the kind's maker gives no table: the arm says 0 at the array of the reads there: harmless just if the lookup's early forms name no array of the second sending: not shown. (3) That s.here's sort and linkNo s are those of the segment m of which "formsT m" speaks is the promise's. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FormsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)

/-- A stated function: of the record, the data, an array's name, a row and a place. -/
abbrev UFn : Type := S → Bound GQ → ℕ × String → ℕ → ℕ → GQ

/-- The open link's number, off the record; 0 where no link is open. -/
def linkNo (s : S) : ℕ := (s.link?.map (·.check.frame.link)).getD 0

/-- **ONE u: three arms by the sort of the record's open segment**, each handed the link's number. -/
def uBySort (uL uA uH : ℕ → UFn) : UFn := fun s =>
  match s.here with
  | .lay _ => uL (linkNo s) s
  | .att _ => uA (linkNo s) s
  | .head _ => uH (linkNo s) s
  | _ => fun _ _ _ _ => 0

/-- **What a kind asks of St at a record**, general in its stated function. -/
structure StatedIs (St : Stated) (u : UFn) (s : S) : Prop where
  mask : ∀ D : Bound GQ, (St.at1 s D).mask = D.mask
  cell : ∀ (D : Bound GQ) (c : ℕ × String) (r i : ℕ), second s c = true →
    (St.at1 s D).cell c.1 c.2 r i = u s D c r i
  other : ∀ (D : Bound GQ) (c : ℕ × String) (r i : ℕ), second s c = false →
    (St.at1 s D).cell c.1 c.2 r i = D.cell c.1 c.2 r i

/-- Stated.of u is u's, at every record. -/
theorem statedIs_of (u : UFn) (s : S) : StatedIs (Stated.of u) u s :=
  ⟨fun D => of_mask u s D, fun D c r i h => of_second u s D c r i h,
    fun D c r i h => of_else u s D c r i h⟩

/-- It hangs on u at that record alone. -/
theorem StatedIs.congr {St : Stated} {u u' : UFn} {s : S} (h : StatedIs St u s) (e : u s = u' s) :
    StatedIs St u' s :=
  ⟨h.mask, fun D c r i hc => by rw [h.cell D c r i hc, e], h.other⟩

section
variable (uL uA uH : ℕ → UFn) (s : S)

theorem uBySort_lay (a : First.LayOwn) (h : s.here = .lay a) :
    uBySort uL uA uH s = uL (linkNo s) s := by
  unfold uBySort
  rw [h]

theorem uBySort_att (a : First.AttOwn) (h : s.here = .att a) :
    uBySort uL uA uH s = uA (linkNo s) s := by
  unfold uBySort
  rw [h]

theorem uBySort_head (a : First.HeadOwn) (h : s.here = .head a) :
    uBySort uL uA uH s = uH (linkNo s) s := by
  unfold uBySort
  rw [h]

/-- **At a record of a layers' segment.** -/
theorem stated_lay (a : First.LayOwn) (h : s.here = .lay a) :
    StatedIs (Stated.of (uBySort uL uA uH)) (uL (linkNo s)) s :=
  (statedIs_of _ s).congr (uBySort_lay uL uA uH s a h)

/-- **At a record of an attention segment.** -/
theorem stated_att (a : First.AttOwn) (h : s.here = .att a) :
    StatedIs (Stated.of (uBySort uL uA uH)) (uA (linkNo s)) s :=
  (statedIs_of _ s).congr (uBySort_att uL uA uH s a h)

/-- **At a record of the head's segment.** -/
theorem stated_head (a : First.HeadOwn) (h : s.here = .head a) :
    StatedIs (Stated.of (uBySort uL uA uH)) (uH (linkNo s)) s :=
  (statedIs_of _ s).congr (uBySort_head uL uA uH s a h)

end

/-- A CONTROL ON THE STATEMENT: StatedIs can fail: the identity on the data is no St for a u that parts from the data at an array of the second sending. -/
theorem statedIs_can_fail (u : UFn) (s : S) (D : Bound GQ) (c : ℕ × String) (r i : ℕ)
    (hc : second s c = true) (hne : D.cell c.1 c.2 r i ≠ u s D c r i) :
    ¬ StatedIs ⟨fun _ D => D⟩ u s :=
  fun h => hne (h.cell D c r i hc)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.statedIs_of
#print axioms VerifiableInference.Desc.Sound.stated_lay
#print axioms VerifiableInference.Desc.Sound.stated_att
#print axioms VerifiableInference.Desc.Sound.stated_head
#print axioms VerifiableInference.Desc.Sound.statedIs_can_fail
