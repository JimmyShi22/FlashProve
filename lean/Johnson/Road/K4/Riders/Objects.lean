-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/Objects.lean: THE LOOKUP's TWO RUNS OF CLAIMS "objects" AND "guests" RIDE
OVER A STEP THAT TURNS THE OPEN LAYERS' LINK's LEDGER INTO A LATER ONE (as a yes of K4's block
does): the sentence formsTQ (Johnson/Desc/Sound/FormsQ.lean) from the state behind to
the state in front, the public test formsInT (Johnson/Desc/First/Batch/FormsIn.lean) from in front
to behind. AT EVERY READERS Rd THAT GIVE, AT THE RUN AND THE TWO STATES, WHAT THE GENERIC READER
GIVES (K9.readerOf, Johnson/Desc/First/Batch/ReaderOf.lean; the premises e, e': at
K9.Readers.ofStates by rfl; at a link's readers wherever the generic reader answers). Definitions,
statements and proofs.

WHY IT IS LIGHT. The run "objects" (Johnson/Desc/First/Look/Via/Via.lean) lists the rows that the
lookup's hearing left in the verifier's state, and marks a debt in the ledger as paid. Its forms do
not hang on the ledger. It fills no slot: so the reader's list of late slots is empty at every
ledger. The run "guests", with no guest handed in, lists nothing and leaves the state as it is.
WHERE THE LEDGER COMES IN. (1) The reader asks of every ENTRY of a form that it names row 0 of an
array with one own row in the ledger (rowsOwn): that reads the ledger's field trees alone, which the
step leaves (htr). (2) The test on a slot asks: below the number of slots, filled, inside the two
arrays' sizes: a later ledger keeps these. (3) THE FREE SLOT, K9.mergeOf, TURNS: nothing in front of
K4's yes (by the item callerIn m; not spent here), the merge's end value's slot behind: THE TEST
BEHIND IS STRICTER. In front a named slot is filled; where nothing is filled from the ledger's next
free number on, it lies below that number, and so below the free slot (hsF). (4) The sentence reads
what is shown and the factor under the named slots: a later ledger keeps them. (5) WHERE THE ROWS'
ENTRIES COME IN: the step forward asks nothing of them. The step back does (hne: the rows name no
entry): the stated data's CELLS may turn at K4's yes (the stated function that is meant at a layers'
link reads the link's field own, which K4's yes lays: not imported here), so a form that
named a cell could turn its worth.

  `ObjRun run`, `GuestRun run`: what is asked of the two runs: their returns, handed 0 claims.
  `lateOf_paid`, `lateOf_self`: no slot is late.
  `segAt_lay'`: the open segment's part at a layers' link, with four of its fields.
  `rowsOwn`, `rowsOwn_trees`, `rowsOwn_of_hne`; `reader_objects`, `reader_guests`: the reader in
    closed form.
  `rides_of`, `dataQ_same`, `entInT_same`, `slotIn_later`: the later part rides on the earlier.
  `hne_of_bare`: "the rows name no entry" out of a test with code.
  **`objects_back`**: a filling of formsTQ_rides' premises. **`objects_forward`**.
  `guests_holds`, `guests_in`: at a layers' link the sentence and the test of "guests" hold
    outright: THE ITEM IS IDLE: its list is empty.
EVERY OTHER ITEM OF THESE TWO SORTS THAT IS OPEN ACROSS K4's PLACE WOULD OWE THE SAME STEP PAST THE
FREE SLOT. By the table's rows (segRow, Johnson/Desc/First/Borders.lean: pieces 1 to 4 of a layers'
segment; as theorems: riders_full, Johnson/Road/K4/Riders/Full.lean, and k4TiedFit,
Johnson/Road/K4/Riders/KeepsOfMeans.lean: BOTH NOT IMPORTED) formsT m 2 "objects" is
the only item of the sorts forms and formsT that is open across K4's block. New: that the list of
late slots is empty; the step forward past the free slot. The step back is formsTQ_rides.
**Limits.** PREMISES, none paid here; where a payer is known it is named. Of the step: ha (a layers'
link in front), R (Rest s s'), hG, L (the ledger behind is later), htr (it has the same arrays that
the claims read): had behind a yes of K4's block (KeptAtS, Johnson/Road/K4/KeptAtS.lean; htr:
hear_trees, Johnson/Road/K4/Slots/HearTrees.lean). Of the runs: hfind (the block's list states a run
of that name) and ObjRun or GuestRun: THAT THE SEATED LOOKUP's BLOCK's RUNS ARE SUCH IS NOT SHOWN
HERE; THE SEATED RUNS BEAR THE DRIVER's GUARD ON THE REPLY:
Johnson/Road/K4/Riders/ObjectsGuarded.lean. hh (what the lookup heard lies in the link): the
promise's item look m. e, e' (the readers give the generic reader's answer at the run and
the two states). hin: the public test in front: tied to the item, which is open there. Back alone:
hne (the rows that the lookup heard name no entry): IT MUST REACH THE USER OUT OF THE PROMISE IN
FRONT OF K4's BLOCK, AND NO ITEM THERE SAYS IT: a law in the lookup's files does not suffice;
hSt: ON A LETTER: the stated data's mask row is the same at the two states. Forward: hS, hfree: the
promise's items ledger m and freeAbove m; hm: what K4's yes lays (KeptAtS); hsF (the free slot
behind is not below the ledger's next free number in front): next_le_sFv,
Johnson/Road/K4/Riders/ObjectsAtMeans.lean. Nothing says that a form is worth 0 anywhere. Nothing on
soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no member.


-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Desc.First.K4.ReadsAtS
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (Claim K9.readerOf K9.lateOf K9.lateOk K9.lateAt K9.slotIn K9.ownRow
  K9.maskSeat K9.mergeOf K9.segAt? K9.RunOf K9.Part K9.Read K9.Readers K9.formsInT K9.affInT
  K9.entInT K9.entIn K9.arrayIn K9.atMoment1)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.Sound (Stated formsTQ formsTQ_rides Rides dataQ MsgQ)

/-- The run "objects", handed 0 claims, wherever a ledger is open and the lookup is heard (nothing
is asked elsewhere): the rows that the lookup heard, each as a claim; one debt of the ledger is
marked as paid. -/
def ObjRun (run : Nat → S → Except String (List Claim × S)) : Prop :=
  ∀ (s : S) (F : Fork) (g : Forest.Heard), s.fork? = some F → s.lookHeard? = some g →
    run 0 s = .ok (g.rows.toList.map fun a => ({ form := a } : Claim),
      s.putFork (F.paid g.owedObjects))

/-- The run "guests" with no guest: no claim; the state as it is. -/
def GuestRun (run : Nat → S → Except String (List Claim × S)) : Prop :=
  ∀ s : S, run 0 s = .ok ([], s)

/-! ## No slot is late -/

theorem lateOf_paid (F : Fork) (i : Nat) : K9.lateOf F (F.paid i) = [] := by
  unfold K9.lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  show (if (!(F.gotF.getD j false) && F.gotF.getD j false) = true then _ else none) = none
  cases F.gotF.getD j false <;> rfl

theorem lateOf_self (F : Fork) : K9.lateOf F F = [] := by
  unfold K9.lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  cases F.gotF.getD j false <;> rfl

/-! ## The part and the reader at a layers' link -/

theorem segAt_lay' {s : S} {a : LayOwn} (ha : s.here = .lay a) :
    ∃ A, K9.segAt? s = some A ∧ A.F = a.F ∧ A.L = a.L ∧ A.d.st = s.st ∧ A.d.book = s.book := by
  have hL : s.link? = some a.L := by simp only [S.link?, ha]
  have hF : s.fork? = some a.F := by simp only [S.fork?, ha]
  have hT : s.tl? = some a.tl := by simp only [S.tl?, ha]
  unfold K9.segAt?
  rw [hL, hF, hT]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

private theorem forms_lit : ∀ l : List Aff,
    (l.map fun a => ({ form := a } : Claim)).map (·.form) = l
  | [] => rfl
  | x :: l => by
    show x :: (l.map fun a => ({ form := a } : Claim)).map (·.form) = x :: l
    rw [forms_lit l]

variable {states : Nat → List (K9.RunOf S)} {b : Nat} {nm : String}
  {run : Nat → S → Except String (List Claim × S)} {s s' : S} {a : LayOwn} {g : Forest.Heard}

/-- The reader's own test on the rows that the lookup heard: each entry names row 0 of an array with
one own row in the ledger F. Where the rows name no entry it says yes idly. -/
def rowsOwn (F : Fork) (g : Forest.Heard) : Bool :=
  (g.rows.toList.map fun a => ({ form := a } : Claim)).all fun c =>
    c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow F)

/-- It reads of the ledger the arrays that the claims read, and nothing else. -/
theorem rowsOwn_trees {F G : Fork} (h : G.trees = F.trees) (g : Forest.Heard) :
    rowsOwn G g = rowsOwn F g := by
  have e : K9.ownRow G = K9.ownRow F := by
    funext x
    unfold K9.ownRow
    rw [h]
  unfold rowsOwn
  rw [e]

/-- Where the rows name no entry the reader's test says yes. -/
theorem rowsOwn_of_hne (F : Fork) {g : Forest.Heard}
    (hne : ∀ f ∈ g.rows.toList, f.ents.toList = []) : rowsOwn F g = true := by
  unfold rowsOwn
  refine List.all_eq_true.2 fun c hc => ?_
  obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hc
  show ((#[] : Array Run2).isEmpty && (none : Option Nat).isNone &&
    f.ents.all (K9.ownRow F)) = true
  rw [← Array.all_toList, hne f hf']
  rfl

/-- **The reader at "objects"**, in closed form. -/
theorem reader_objects (hfind : (states b).find? (fun r => r.1 == "objects") = some (nm, run))
    (hrun : ObjRun run) (ha : s.here = .lay a) (hh : a.lookHeard = some g) :
    K9.readerOf states b "objects" s =
      if rowsOwn a.F g = true then some { forms := g.rows.toList, late := [] } else none := by
  have hF : s.fork? = some a.F := by simp only [S.fork?, ha]
  have hg : s.lookHeard? = some g := by simp only [S.lookHeard?, ha, hh]
  have hG : (s.putFork (a.F.paid g.owedObjects)).fork? = some (a.F.paid g.owedObjects) := by
    simp only [S.putFork, S.fork?, ha]
  unfold K9.readerOf
  rw [hfind, Option.bind_some]
  simp only [hrun s a.F g hF hg, hF, hG, Option.bind_some]
  rw [forms_lit, lateOf_paid]
  rfl

/-- **The reader at "guests".** -/
theorem reader_guests (hfind : (states b).find? (fun r => r.1 == "guests") = some (nm, run))
    (hrun : GuestRun run) (ha : s.here = .lay a) :
    K9.readerOf states b "guests" s = some { forms := [], late := [] } := by
  have hF : s.fork? = some a.F := by simp only [S.fork?, ha]
  unfold K9.readerOf
  rw [hfind, Option.bind_some]
  simp only [hrun s, hF, Option.bind_some]
  rw [lateOf_self]
  rfl

/-! ## The later part rides on the earlier -/

theorem rides_of (own : List (Nat × Nat)) {A B : K9.Part} (hL : B.L = A.L) (hst : B.d.st = A.d.st)
    (hbk : B.d.book = A.d.book) (L : Later A.F B.F) : Rides own A B :=
  ⟨by rw [hL], by rw [hL], fun _ _ _ h => by rw [hL]; exact h, fun _ h => by rw [hL]; exact h,
    fun _ _ h => by rw [hbk]; exact h, fun _ _ _ _ => by rw [hst]; exact ⟨rfl, rfl⟩,
    fun j _ hj => (L.keep j hj).2⟩

theorem dataQ_same (own : List (Nat × Nat)) {A B : K9.Part} (hL : B.L = A.L)
    (hst : B.d.st = A.d.st) (hbk : B.d.book = A.d.book) (rd : Nat × Nat → MsgQ) :
    dataQ own B rd = dataQ own A rd := by
  unfold dataQ
  rw [hL, hst, hbk]

/-- The test on an entry reads the link's context and the book alone. -/
theorem entInT_same (own : List (Nat × Nat)) {A B : K9.Part} (hL : B.L = A.L)
    (hbk : B.d.book = A.d.book) (x : Ent) : K9.entInT own B x = K9.entInT own A x := by
  unfold K9.entInT K9.entIn K9.arrayIn K9.atMoment1
  rw [hL, hbk]

/-- The test on a slot, with no late slot, at a later part and another free slot. -/
theorem slotIn_later {own : List (Nat × Nat)} {free free' : Option Nat} {A B : K9.Part} {j : Nat}
    (hL : B.L = A.L) (hbk : B.d.book = A.d.book) (L : Later A.F B.F) (hS : Sized A.F)
    (hfr : Filled A.F j → free' ≠ some j) (h : K9.slotIn own free [] A j = true) :
    K9.slotIn own free' [] B j = true := by
  unfold K9.slotIn at h
  obtain ⟨s1, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨s2, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have h' : (A.F.gotF.getD j false &&
      (decide (j < A.F.vp.size) && decide (j < A.F.mf.size))) = true := h
  obtain ⟨g0, _⟩ := Eq.mp (Bool.and_eq_true _ _) h'
  have j1 : j < B.F.ns := by
    rw [L.ns]
    exact of_decide_eq_true s1
  have sB : Sized B.F := L.sized hS
  have g1 : B.F.gotF.getD j false = true := (L.keep j g0).1
  have hm : K9.maskSeat own B = K9.maskSeat own A := by
    unfold K9.maskSeat
    rw [hL, hbk]
  have hf : (free' != some j) = true := by simpa using hfr g0
  unfold K9.slotIn
  rw [decide_eq_true j1, hm, s2, hf, g1,
    decide_eq_true (show j < B.F.vp.size by rw [sB.1]; exact j1),
    decide_eq_true (show j < B.F.mf.size by rw [sB.2.1]; exact j1)]
  rfl

/-- "The rows name no entry", out of a test with code. -/
theorem hne_of_bare {g : Forest.Heard} (h : (g.rows.all fun f => f.ents.isEmpty) = true) :
    ∀ f ∈ g.rows.toList, f.ents.toList = [] := by
  intro f hf
  rw [← Array.all_toList] at h
  have k := List.all_eq_true.1 h f hf
  have k' : f.ents.isEmpty = true := k
  rw [Array.isEmpty_iff] at k'
  rw [k']

/-! ## "objects" -/

variable {G : Fork} {own : List (Nat × Nat)} {Rd : K9.Readers}

/-- **BACK.** UNDER: a layers' link in front, Rest, a later ledger behind with the same arrays that
the claims read; the run is an ObjRun, found under its name; what the lookup heard lies in the link,
and ITS ROWS NAME NO ENTRY; the readers give the generic reader's answer at both states; the public
test holds in front; the stated data's mask row is one at both: the sentence at the state behind
gives the sentence at the state in front. -/
theorem objects_back {St : Stated} {rd : Nat × Nat → MsgQ} (ha : s.here = .lay a) (R : Rest s s')
    (hG : s'.fork? = some G) (L : Later a.F G) (htr : G.trees = a.F.trees)
    (hfind : (states b).find? (fun r => r.1 == "objects") = some (nm, run)) (hrun : ObjRun run)
    (hh : a.lookHeard = some g) (hne : ∀ f ∈ g.rows.toList, f.ents.toList = [])
    (e : Rd.forms b "objects" s = K9.readerOf states b "objects" s)
    (e' : Rd.forms b "objects" s' = K9.readerOf states b "objects" s')
    (hin : K9.formsInT Rd own b "objects" s = true)
    (hSt : ∀ D j, (St.at1 s' D).mask j = (St.at1 s D).mask j)
    (h : formsTQ Rd St own b "objects" s' rd) : formsTQ Rd St own b "objects" s rd := by
  obtain ⟨a', ha', hL', _, _, hlh⟩ := R.here a ha
  have hF' : a'.F = G := by
    have e0 : s'.fork? = some a'.F := by simp only [S.fork?, ha']
    exact Option.some.inj (e0.symm.trans hG)
  obtain ⟨A, hA, eF, eL, est, ebk⟩ := segAt_lay' ha
  obtain ⟨B, hB, fF, fL, fst, fbk⟩ := segAt_lay' ha'
  have c1 := e.trans (reader_objects hfind hrun ha hh)
  have c2 := e'.trans (reader_objects hfind hrun ha' (hlh.trans hh))
  rw [hF', rowsOwn_trees htr] at c2
  have hL : B.L = A.L := by rw [fL, eL, hL']
  have hst : B.d.st = A.d.st := by rw [fst, est, R.st]
  have hbk : B.d.book = A.d.book := by rw [fbk, ebk, R.book]
  have hLat : Later A.F B.F := by
    rw [eF, fF, hF']
    exact L
  refine formsTQ_rides own Rd St b "objects" s s' A B rd hA hB (c2.trans c1.symm) hin
    (rides_of own hL hst hbk hLat) (fun Rr hR f hf => ?_) h
  have hf' : f ∈ g.rows.toList := by
    by_cases hb : rowsOwn a.F g = true
    · rw [if_pos hb] at c1
      obtain rfl : ({ forms := g.rows.toList, late := [] } : K9.Read) = Rr :=
        Option.some.inj (c1.symm.trans hR)
      exact hf
    · rw [if_neg hb] at c1
      exact nomatch c1.symm.trans hR
  refine ⟨fun x hx => ?_, fun x _ => ?_⟩
  · rw [hne f hf'] at hx
    cases hx
  · rw [dataQ_same own hL hst hbk rd]
    exact hSt _ _

/-- **FORWARD.** UNDER: the same step and run (nothing on the rows' entries); the free slot behind
is sF, not below the ledger's next free number in front; the ledger in front has its sizes, and
nothing is filled from its next free number on; the readers give the generic reader's answer at
both states: the public test at the state in front gives the test at the state behind, past the free
slot. -/
theorem objects_forward {sF : Nat} (ha : s.here = .lay a) (R : Rest s s') (hG : s'.fork? = some G)
    (L : Later a.F G) (htr : G.trees = a.F.trees)
    (hfind : (states b).find? (fun r => r.1 == "objects") = some (nm, run)) (hrun : ObjRun run)
    (hh : a.lookHeard = some g) (hm : K9.mergeOf s' = some sF) (hsF : a.F.next ≤ sF)
    (hS : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (e : Rd.forms b "objects" s = K9.readerOf states b "objects" s)
    (e' : Rd.forms b "objects" s' = K9.readerOf states b "objects" s')
    (hin : K9.formsInT Rd own b "objects" s = true) :
    K9.formsInT Rd own b "objects" s' = true := by
  obtain ⟨a', ha', hL', _, _, hlh⟩ := R.here a ha
  have hF' : a'.F = G := by
    have e0 : s'.fork? = some a'.F := by simp only [S.fork?, ha']
    exact Option.some.inj (e0.symm.trans hG)
  obtain ⟨A, hA, eF, eL, est, ebk⟩ := segAt_lay' ha
  obtain ⟨B, hB, fF, fL, fst, fbk⟩ := segAt_lay' ha'
  have c1 := e.trans (reader_objects hfind hrun ha hh)
  have c2 := e'.trans (reader_objects hfind hrun ha' (hlh.trans hh))
  rw [hF', rowsOwn_trees htr] at c2
  have hL : B.L = A.L := by rw [fL, eL, hL']
  have hbk : B.d.book = A.d.book := by rw [fbk, ebk, R.book]
  have hLat : Later A.F B.F := by
    rw [eF, fF, hF']
    exact L
  unfold K9.formsInT at hin ⊢
  by_cases hb : rowsOwn a.F g = true
  · rw [if_pos hb] at c1 c2
    rw [hA, c1] at hin
    rw [hB, c2]
    obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    refine Eq.mpr (Bool.and_eq_true _ _) ⟨rfl, List.all_eq_true.2 fun f hf => ?_⟩
    have hi : K9.affInT own (K9.mergeOf s) [] A f = true := List.all_eq_true.1 hall f hf
    unfold K9.affInT at hi ⊢
    obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hi
    refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun x hx => ?_,
      List.all_eq_true.2 fun x hx => ?_⟩
    · rw [entInT_same own hL hbk]
      exact List.all_eq_true.1 h1 x hx
    · refine slotIn_later hL hbk hLat (by rw [eF]; exact hS) (fun hfil => ?_)
        (List.all_eq_true.1 h2 x hx)
      rw [hm]
      intro e0
      have e1 : sF = x.1 := Option.some.inj e0
      rw [eF] at hfil
      exact hfree x.1 (by rw [← e1]; exact hsF) hfil
  · rw [if_neg hb] at c1
    rw [hA, c1] at hin
    simp at hin

/-! ## "guests" -/

/-- UNDER: a layers' link; the run is a GuestRun (NO GUEST IS HANDED IN), found under its name; the
readers give the generic reader's answer: the sentence of "guests" holds of every witness: its list
is empty. -/
theorem guests_holds {St : Stated} {rd : Nat × Nat → MsgQ} (ha : s.here = .lay a)
    (hfind : (states b).find? (fun r => r.1 == "guests") = some (nm, run)) (hrun : GuestRun run)
    (e : Rd.forms b "guests" s = K9.readerOf states b "guests" s) :
    formsTQ Rd St own b "guests" s rd := by
  obtain ⟨A, hA, _⟩ := segAt_lay' ha
  exact ⟨A, { forms := [], late := [] }, hA, e.trans (reader_guests hfind hrun ha), rfl,
    fun _ hf => nomatch hf⟩

/-- Under the same: so does its test. -/
theorem guests_in (ha : s.here = .lay a)
    (hfind : (states b).find? (fun r => r.1 == "guests") = some (nm, run)) (hrun : GuestRun run)
    (e : Rd.forms b "guests" s = K9.readerOf states b "guests" s) :
    K9.formsInT Rd own b "guests" s = true := by
  obtain ⟨A, hA, _⟩ := segAt_lay' ha
  have r : Rd.forms b "guests" s = some { forms := [], late := [] } :=
    e.trans (reader_guests hfind hrun ha)
  unfold K9.formsInT
  rw [hA, r]
  rfl

end OnBytes.Desc.First.K4.Riders

#print axioms OnBytes.Desc.First.K4.Riders.lateOf_paid
#print axioms OnBytes.Desc.First.K4.Riders.lateOf_self
#print axioms OnBytes.Desc.First.K4.Riders.segAt_lay'
#print axioms OnBytes.Desc.First.K4.Riders.rowsOwn_trees
#print axioms OnBytes.Desc.First.K4.Riders.rowsOwn_of_hne
#print axioms OnBytes.Desc.First.K4.Riders.reader_objects
#print axioms OnBytes.Desc.First.K4.Riders.reader_guests
#print axioms OnBytes.Desc.First.K4.Riders.rides_of
#print axioms OnBytes.Desc.First.K4.Riders.dataQ_same
#print axioms OnBytes.Desc.First.K4.Riders.entInT_same
#print axioms OnBytes.Desc.First.K4.Riders.slotIn_later
#print axioms OnBytes.Desc.First.K4.Riders.hne_of_bare
#print axioms OnBytes.Desc.First.K4.Riders.objects_back
#print axioms OnBytes.Desc.First.K4.Riders.objects_forward
#print axioms OnBytes.Desc.First.K4.Riders.guests_holds
#print axioms OnBytes.Desc.First.K4.Riders.guests_in
