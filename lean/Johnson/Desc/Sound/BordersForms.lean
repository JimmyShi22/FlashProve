-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersForms.lean: THE TABLE OF JOINTS' FOUR LETTERS forms, formsT, totalB,
total, FILLED with the sentences of Johnson/Desc/Sound/FormsQ.lean, AND THE THREE PUBLIC ITEMS THAT
ARE TIED TO THEM. Definitions, theorems, and a guard on the map of names.

What is said. `meaningForms`: a meaning of the items (`Meaning`, Johnson/Desc/First/Borders.lean)
whose four fields are `formsQ`, `formsTQ`, `totalBQ`, `totalQ` at the chain's record and the
witness's tables. THE READERS ARE A SEGMENT's (`Rd m`: Johnson/Desc/First/Batch/ReadersOfLink.lean
has the term for a link of a real chain), AND THEY GO BY THE DRIVER's OWN PAIRS (block, name): an
item forms m k r | formsT m k r, whose names are the table's, STANDS FOR THE RUNS `runs m k r` (a
letter: the table's own map `runsOf` fills it: `runsAt`), and says the sentence OF EACH. WHERE THAT
LIST IS EMPTY THE ITEM HOLDS OF EVERY WITNESS: it is idle there. THE WITNESS IS READ THROUGH THE
TABLE's ONE ACCESSOR, BY SEAT (`seatTab`, Johnson/Desc/Sound/BordersFill.lean): a copy's own table:
its pad's places off the witness's pads, all others off the message that the copies share. Nothing
here reads a component of the witness bare. WHICH SEATS EACH MAY READ IS THE TABLE's OWN LIST: a
segment's whole group; for formsT its first sending's alone.
  THREE LETTERS INSIDE THE FOUR FIELDS: `wt`: AT THE NAME "weights" forms | formsT say, beside the
    runs' sentences, wt m a y w: what the item's closer means by it · `rw`: total | totalB say,
    beside the sentence on the sum, rw m a.2 = true: a Bool on the record · `ah`: OF WHICH RUNS THE
    FORMS MAY NAME AN ARRAY THAT THE SEGMENT HAS NOT YET SENT: there forms says `formsQA`
    (Johnson/Desc/Sound/FormsAhead.lean: such an array is read off the witness at the seat that the
    plan gives its message) and formsIn `formsInA`; meant: the smallness test's equations alone,
    whose item is open one block in front of the sending of the digits' array.
  `seatTab_congr`: the accessor at a seat reads that seat's message and pad, and nothing else.
  `readsOkForms` (proved): where a meaning reads the witness through the components that the table
    names (`ReadsOkQ`, Johnson/Desc/Sound/BordersSides.lean), so does the meaning with these four
    fields filled: BY THE MAKE of the accessor `tabQ`; of wt it asks as premises that it reads the
    witness through what the table names for forms | formsT m k "weights".
  `seatsAre ms own`: FOR THE PROMISE: a test: every seat of own is a member's: at a seat that is no
    member's `seatTab` is the zero table, in silence. It reads the plan's lists alone.
  THE PROMISE's THREE PUBLIC ITEMS formsIn, formsInT, totalIn ARE FILLED BESIDE THEM
  (`Meaning.pub`):
    the public tests of Johnson/Desc/First/Batch/FormsIn.lean, at the same readers, map of names and
    seats; every other public item is handed on. THAT BOOL HALF IS A FUNCTION WITH CODE OF ITS OWN
    (`K9.pubForms`, Johnson/Desc/First/Batch/FormsPub.lean; no Mathlib), so that a sheet can call it
    alone. `meaningForms_pub`: the filling's pub is that function, by the make.
  `forms_pub`, `formsT_pub` (with `formsTQ_in`): where forms m k r | formsT m k r holds of a
      witness,
    formsIn m k r | formsInT m k r is true of the record. `total` DOES NOT HOLD `totalIn`.
  `runsAt links`: THE MAP OF NAMES AT A REAL CHAIN: the table's own `runsOf` at the sort of segment
      m.
  `idleAt sub`, `idle_layers`, `idle_attention`, `idle_head` (proved by evaluation): THE GUARD:
      WHICH
    OF THE TABLE's NAMES STAND FOR NO RUN, so that the item holds of every witness: at a
    feed-forward segment (2, "planes") and (2, "join") (idle: these claims lie inside the caller's
    own runs); at attention none; AT THE HEAD (4, "weights"): it stands for no run: what it says is
    the letter wt.
Limits: The segment's number m picks the seats; that the record stands in segment m is the
promise's. What was handed to the chain is not read. The letters (the readers; the map of names; the
stated functions; wt; rw; ah) and `after m` (the runs behind the batching, as
the block at that place runs them: Johnson/Desc/Block.lean's `afterIn` at the link's lists) are
letters still. Where a run's reader is silent the item is false of every witness: SO THE PROMISE
STANDS OR FALLS WITH WHICH READERS ARE LAID IN. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersSides
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.FormsPub
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp)
open VerifiableInference.Desc.K9 (Readers)

section
variable (cs : OnBytes.Codes) {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → First.S → Except String First.S) (N : Numbers)
  (wt : ℕ → P × First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → First.S → Bool)
  (ah : ℕ → String → Bool)

/-- FOR THE PROMISE: every seat that a sentence may read is a member's. -/
def seatsAre (own : List (ℕ × ℕ)) : Bool := own.all fun x => ms.any fun y => decide (seatOf y = x)

/-- **The four letters, filled.** -/
def meaningForms (Mg : Meaning P (Wit Cells Tok MsgT)) : Meaning P (Wit Cells Tok MsgT) :=
  { Mg with
    forms := fun m k r a y w => (∀ p ∈ runs m k r,
      if ah p.1 p.2 = true then
        formsQA (N.sent m) (N.group m) (Rd m) p.1 p.2 a.2 (seatTab cs arr ms w)
      else formsQ (Rd m) (N.group m) p.1 p.2 a.2 (seatTab cs arr ms w)) ∧
        (r = "weights" → wt m a y w)
    formsT := fun m k r a y w => (∀ p ∈ runs m k r,
      formsTQ (Rd m) St (N.sent m 0) p.1 p.2 a.2 (seatTab cs arr ms w)) ∧
        (r = "weights" → wt m a y w)
    totalB := fun m a _ w =>
      totalBQ (after m) (N.group m) a.2 (seatTab cs arr ms w) ∧ rw m a.2 = true
    total := fun m a _ w => totalQ (N.group m) a.2 (seatTab cs arr ms w) ∧ rw m a.2 = true
    pub := K9.pubForms Rd runs ah N Mg.pub }

/-- THE FILLING's BOOL HALF IS THE FUNCTION WITH CODE, BY THE MAKE. -/
theorem meaningForms_pub (Mg : Meaning P (Wit Cells Tok MsgT)) :
    (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).pub =
      K9.pubForms Rd runs ah N Mg.pub := rfl

/-- The sentence "formsT" holds its test. -/
theorem formsTQ_in (R₀ : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : First.S)
    (rd : ℕ × ℕ → MsgQ) (h : formsTQ R₀ St own piece run s rd) :
    K9.formsInT R₀ own piece run s = true := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := h
  unfold K9.formsInT
  rw [ha, hs]
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hm => (hf f hm).1⟩

/-- THE SENTENCE HOLDS THE PROMISE's TEST, AT THE FILLING: where the item forms m k r holds of a
witness, the public item formsIn m k r is true of the record. -/
theorem forms_pub (Mg : Meaning P (Wit Cells Tok MsgT)) (m k : ℕ) (r : String) (a : P × First.S)
    (y : Strs) (w : Wit Cells Tok MsgT)
    (h : (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).forms m k r a y w) :
    (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).pub (.formsIn m k r) a = true :=
  List.all_eq_true.2 fun p hp => by
    have h1 := h.1 p hp
    by_cases e : ah p.1 p.2 = true
    · rw [if_pos e] at h1
      show (if ah p.1 p.2 = true then _ else _) = true
      rw [if_pos e]
      exact formsQA_in (N.sent m) (N.group m) (Rd m) p.1 p.2 a.2 _ h1
    · rw [if_neg e] at h1
      show (if ah p.1 p.2 = true then _ else _) = true
      rw [if_neg e]
      exact formsQ_in (Rd m) (N.group m) p.1 p.2 a.2 _ h1

/-- The like for formsT m k r and formsInT m k r. (`total` DOES NOT HOLD `totalIn`: that test is the
promise's own at total's borders; `totalB` holds it inside, at the record that the runs behind the
batching return.) -/
theorem formsT_pub (Mg : Meaning P (Wit Cells Tok MsgT)) (m k : ℕ) (r : String) (a : P × First.S)
    (y : Strs) (w : Wit Cells Tok MsgT)
    (h : (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).formsT m k r a y w) :
    (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).pub (.formsInT m k r) a = true :=
  List.all_eq_true.2 fun p hp => formsTQ_in St (Rd m) (N.sent m 0) p.1 p.2 a.2 _ (h.1 p hp)

/-- The map of names at a real chain: the table's own, at the sort of segment m; beyond the list:
nothing. -/
def runsAt (links : List ModelPart) (m k : ℕ) (r : String) : List (ℕ × String) :=
  ((links[m]?).map fun sub => First.runsOf sub k r).getD []

/-- The table's names of runs that stand for no run at a sort of segment. -/
def idleAt (sub : ModelPart) : List (ℕ × String) :=
  (First.tableRuns sub).filter fun x => (First.runsOf sub x.1 x.2).isEmpty

theorem idle_layers : idleAt .layers = [(2, "planes"), (2, "join")] := by decide

theorem idle_attention : idleAt .attention = [] := by decide

theorem idle_head : idleAt .head = [(4, "weights")] := by decide

/-- The accessor at a seat reads that seat's message and pad alone. -/
theorem seatTab_congr (w w' : Wit Cells Tok MsgT) (x : ℕ × ℕ)
    (h1 : w.msg (arr x.1 x.2) = w'.msg (arr x.1 x.2)) (h2 : w.pad x.1 x.2 = w'.pad x.1 x.2) :
    seatTab cs arr ms w x = seatTab cs arr ms w' x := by
  unfold seatTab
  cases e : ms.find? fun y => decide (seatOf y = x) with
  | none => rfl
  | some y =>
    have hy : y.1.seat y.2 = x := by
      have h := List.find?_some e
      exact of_decide_eq_true h
    show memTab cs arr w y = memTab cs arr w' y
    unfold memTab Wit.tab numOf
    rw [hy, h1, h2]

/-- Two witnesses that have the components of an item's tenants in common read alike at these
seats. -/
theorem sameSeats (links : List ModelPart) (i : Item) (w w' : Wit Cells Tok MsgT)
    (h : ∀ c ∈ i.reads arr N links, sameQ c w w') :
    ∀ x ∈ i.tenants N, seatTab cs arr ms w x = seatTab cs arr ms w' x := by
  intro x hx
  have hm : ∀ c ∈ [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2], c ∈ i.reads arr N links :=
    fun c hc => List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, hc⟩)
  exact seatTab_congr cs arr ms w w' x (h (.msg (arr x.1 x.2)) (hm _ (by simp)))
    (h (.pad x.1 x.2) (hm _ (by simp)))

/-- **The filling keeps `ReadsOkQ`.** -/
theorem readsOkForms (links : List ModelPart) (Mg : Meaning P (Wit Cells Tok MsgT))
    (h : ReadsOkQ arr N links Mg)
    (hF : ∀ m k a y w w', (∀ c ∈ (Item.forms m k "weights").reads arr N links, sameQ c w w') →
      wt m a y w → wt m a y w')
    (hT : ∀ m k a y w w', (∀ c ∈ (Item.formsT m k "weights").reads arr N links, sameQ c w w') →
      wt m a y w → wt m a y w') :
    ReadsOkQ arr N links (meaningForms cs arr ms Rd runs St after N wt rw ah Mg) := by
  intro i a y w w' hc hw
  cases i with
  | forms m k r =>
    refine ⟨fun p hp => ?_, fun e => ?_⟩
    · have h1 := hw.1 p hp
      by_cases e : ah p.1 p.2 = true
      · rw [if_pos e] at h1 ⊢
        exact formsQA_congr (N.sent m) _ (Rd m) p.1 p.2 a.2 _ _
          (sameSeats cs arr ms N links _ w w' hc) h1
      · rw [if_neg e] at h1 ⊢
        exact formsQ_congr (Rd m) _ p.1 p.2 a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) h1
    · subst e
      exact hF m k a y w w' hc (hw.2 rfl)
  | formsT m k r =>
    refine ⟨fun p hp => formsTQ_congr (Rd m) St _ p.1 p.2 a.2 _ _
      (sameSeats cs arr ms N links _ w w' hc) (hw.1 p hp), fun e => ?_⟩
    subst e
    exact hT m k a y w w' hc (hw.2 rfl)
  | totalB m =>
    exact ⟨totalBQ_congr (after _) _ a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) hw.1, hw.2⟩
  | total m =>
    exact ⟨totalQ_congr _ a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) hw.1, hw.2⟩
  | _ => exact h _ a y w w' hc hw

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.meaningForms_pub
#print axioms VerifiableInference.Desc.Sound.formsTQ_in
#print axioms VerifiableInference.Desc.Sound.forms_pub
#print axioms VerifiableInference.Desc.Sound.formsT_pub
#print axioms VerifiableInference.Desc.Sound.idle_layers
#print axioms VerifiableInference.Desc.Sound.idle_attention
#print axioms VerifiableInference.Desc.Sound.idle_head
#print axioms VerifiableInference.Desc.Sound.seatTab_congr
#print axioms VerifiableInference.Desc.Sound.sameSeats
#print axioms VerifiableInference.Desc.Sound.readsOkForms
