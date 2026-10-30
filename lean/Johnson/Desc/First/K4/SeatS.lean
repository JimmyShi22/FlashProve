-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/SeatS.lean: A SEAT AT THE FIRST CHAIN's CARRIED RECORD ITSELF, AND THE BLOCK
THAT RIDES READ THROUGH IT. A DEVICE OF THE PROOF: no text of the description that we hold calls
`seatS`, and it runs nowhere. A definition, statements and proofs.

Why. The block that rides at the carried record is `blockAtS p` (Johnson/Desc/First/K4/AtS.lean):
K4's block at the seat `seatOwn` of K4's PART of the record, lifted along the lens `part?`,
`setPart`. BY READING, NO THEOREM: it is `block L p` at no seat L of the record itself:
between two links it refuses in the lens's own words. A law that is typed over `block L p` at a
letter L then cannot be called at it. What such a law uses OF THE BLOCK's DECISION is what a yes of
it gives (`decide_ok`, Johnson/Desc/First/K4/BlockLaws.lean): here that conclusion is shown, to the
letter, of `blockAtS p` at `seatS`. Of the block's declared rounds: `Declares`
(Johnson/Road/K4/PieceTiled.lean). Whether a given law uses more of the block is that law's
to say.

  `seatS : Seat S`: inside a layers' link: the link's ledger, what the lookup on the calls returned,
    what K4 heard, the debt of rows as K4's lens reads it ("some 0" and none alike: none); the three
    setters write these fields. OUTSIDE A LAYERS' LINK: an empty ledger, nothing heard, nothing
    owed, and the setters leave the record as it is. The request's tokens: `S.tokv`, everywhere.
  `seatS_fork`, `seatS_look`, `seatS_own`, `seatS_owed`, `seatS_setFork`, `seatS_setOwn`,
    `seatS_setOwed`, `seatS_laid`: what its fields are inside a layers' link. `seatS_forkQ`: there
    the record's own reader `S.fork?` finds the seat's ledger.
  **`hearsAs_atS`**: WHERE THE DECISION OF `blockAtS p` RETURNS: `decide_ok`'s conclusion at
    L := `seatS`, to the letter.
  `seatS_fits`, `seatS_fits1`: the seat's laying and reading of the ledger fit, INSIDE A LAYERS'
    LINK. Outside they do not, BY READING, NO THEOREM (the seat there reads an empty ledger whatever
    was laid): so the premise "for all records" of `decide_later`, `front_later`, `back_later`
    (Johnson/Desc/First/K4/LedgerKeeps.lean) is not to be had of `seatS`.
  `wrote_seatS`, `frontAs_atS`, `backAs_atS`: where a run of claims of `blockAtS p` returns:
    `runOf_ok`'s right-hand side at `seatS`, BUT FOR THE RECORD BEHIND: the lifted run also lays the
    debt of rows as the lens read it: s' = seatS.setOwed (seatS.setFork s F) (seatS.owed s).
  `freeSlotAs_atS`: where the run "free-slot" returns: s' = seatS.setOwed s (seatS.owed s).

Limits. NOTHING HERE SHOWS THAT THE BLOCK OR A RUN RETURNS ANYWHERE. OUTSIDE A LAYERS' LINK THE
SEAT ANSWERS WITH BLANKS: its empty ledger has its sizes and is later than itself, and is not what
`S.fork?` finds in an attention link or in the opened head; it says "nothing owed" ALSO WHERE ROWS
ARE OWED; its setters are idle. SO A CONDITION OR A RELATION AT A BOUNDARY THAT IS WRITTEN IN A
SEAT's LETTERS AND IS READ AT `seatS` MUST ITSELF HOLD THE RECORD IN A LAYERS' LINK (by
`seatS.look s = some _` or `seatS.own s = some _`, which only such a link answers): else it is met
by records that no such link holds. The setters one by one are not the lifted block's: `setPart`
also lays the debt as the lens read it; the two compounds that K4 uses agree (`seatS_laid`,
`wrote_seatS`). The premise for which `hearsAs_atS` is made, `HearsAs` (
Johnson/Road/K4/CarriageHeard.lean), is not imported here: that `hearsAs_atS p` has its field's type
is shown where it is called (`hearsAs_S`, Johnson/Road/K4/CloseAtS.lean). One direction, from a
return. Nothing on soundness.
-/
import Johnson.Desc.First.K4.RunsAtS
import Johnson.Desc.First.K4.AtSHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open VerifiableInference.Desc.First (S LayOwn)

/-- **A seat at the carried record itself.** A device of the proof. -/
def seatS : Seat S where
  fork := fun s =>
    match s.here with
    | .lay a => a.F
    | _ => {}
  setFork := fun s F =>
    match s.here with
    | .lay a => { s with here := .lay { a with F := F } }
    | _ => s
  look := fun s =>
    match s.here with
    | .lay a => a.fo
    | _ => none
  own := fun s =>
    match s.here with
    | .lay a => a.own
    | _ => none
  setOwn := fun s o =>
    match s.here with
    | .lay a => { s with here := .lay { a with own := some o } }
    | _ => s
  owed := fun s =>
    match s.here with
    | .lay _ => if s.noneWaits then none else s.rowsOwed
    | _ => none
  setOwed := fun s d =>
    match s.here with
    | .lay _ => { s with rowsOwed := d }
    | _ => s
  tokv := S.tokv

/-! ### Inside a layers' link -/

/-- The seat's ledger is the link's. -/
theorem seatS_fork {s : S} {a : LayOwn} (ha : s.here = .lay a) : seatS.fork s = a.F := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- What the lookup on the calls returned, as the link holds it. -/
theorem seatS_look {s : S} {a : LayOwn} (ha : s.here = .lay a) : seatS.look s = a.fo := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- What K4 heard, as the link holds it. -/
theorem seatS_own {s : S} {a : LayOwn} (ha : s.here = .lay a) : seatS.own s = a.own := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- The debt of rows, as K4's lens reads it. -/
theorem seatS_owed {s : S} {a : LayOwn} (ha : s.here = .lay a) :
    seatS.owed s = if s.noneWaits then none else s.rowsOwed := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- Laying a ledger writes the link's F. -/
theorem seatS_setFork {s : S} {a : LayOwn} (ha : s.here = .lay a) (F : Fork) :
    seatS.setFork s F = { s with here := .lay { a with F := F } } := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- Laying what K4 heard writes the link's own. -/
theorem seatS_setOwn {s : S} {a : LayOwn} (ha : s.here = .lay a) (o : Own) :
    seatS.setOwn s o = { s with here := .lay { a with own := some o } } := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- Laying a debt writes the record's rowsOwed. -/
theorem seatS_setOwed {s : S} {a : LayOwn} (ha : s.here = .lay a) (d : Option Nat) :
    seatS.setOwed s d = { s with rowsOwed := d } := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- The record's own reader of the ledger finds the seat's. -/
theorem seatS_forkQ {s : S} {a : LayOwn} (ha : s.here = .lay a) :
    s.fork? = some (seatS.fork s) := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- The three setters in the order in which K4's decision calls them. -/
theorem seatS_laid {s : S} {a : LayOwn} (ha : s.here = .lay a) (F : Fork) (o : Own)
    (d : Option Nat) :
    seatS.setOwed (seatS.setOwn (seatS.setFork s F) o) d =
      { s with here := .lay { a with F := F, own := some o }, rowsOwed := d } := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- The seat's laying and reading of the ledger fit, inside a layers' link: behind the decision's
three layings. -/
theorem seatS_fits {s : S} {a : LayOwn} (ha : s.here = .lay a) (F : Fork) (o : Own) :
    seatS.fork (seatS.setOwed (seatS.setOwn (seatS.setFork s F) o) none) = F := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- The like behind one laying. -/
theorem seatS_fits1 {s : S} {a : LayOwn} (ha : s.here = .lay a) (F : Fork) :
    seatS.fork (seatS.setFork s F) = F := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-! ### The block that rides, read through the seat -/

/-- **Where the decision of the block that rides returns**: `decide_ok`'s conclusion at `seatS`, to
the letter. -/
theorem hearsAs_atS (p : Par) : ∀ (s : S) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (s' : S), (blockAtS p).decide s rs cols = .ok s' →
    (seatS.owed s).isNone = true ∧
    fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true ∧
    Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true ∧
    ∃ fo o F, seatS.look s = some fo ∧
      hearFl { p.P with tokv := seatS.tokv s } p.hp p.g fo (seatS.fork s)
        (paired rs (entries p.P p.hp p.g)) = some (o, F, []) ∧
      s' = seatS.setOwed (seatS.setOwn (seatS.setFork s F) o) none := by
  intro s rs cols s' h
  obtain ⟨a, fo, o, G, ha, h0, hfo, h1, h2, hh, e⟩ := blockAtS_hears h
  refine ⟨by rw [seatS_owed ha]; exact h0, h1, h2, fo, o, G, by rw [seatS_look ha]; exact hfo,
    by rw [seatS_fork ha]; exact hh, by rw [seatS_laid ha]; exact e⟩

/-- What a run of K4's writes, in the seat's letters. -/
theorem wrote_seatS {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') :
    s' = seatS.setOwed (seatS.setFork s G) (seatS.owed s) := by
  obtain ⟨ha, rfl⟩ := h
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

/-- **Where the run "front" of the block that rides returns**, in the seat's letters. -/
theorem frontAs_atS {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ o fs F, seatS.own s = some o ∧ frontOf p o (seatS.fork s) = some (fs, F) ∧ cl = fs.toList ∧
      s' = seatS.setOwed (seatS.setFork s F) (seatS.owed s) := by
  obtain ⟨a, o, fs, G, ho, hf, hc, hw⟩ := frontAtS hr h
  exact ⟨o, fs, G, by rw [seatS_own hw.1]; exact ho, by rw [seatS_fork hw.1]; exact hf, hc,
    wrote_seatS hw⟩

/-- **Where the run "back" of the block that rides returns**, in the seat's letters. -/
theorem backAs_atS {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ o fs F, seatS.own s = some o ∧ formsBack o (seatS.fork s) = some (fs, F) ∧ cl = fs.toList ∧
      s' = seatS.setOwed (seatS.setFork s F) (seatS.owed s) := by
  obtain ⟨a, o, fs, G, ho, hf, hc, hw⟩ := backAtS hr h
  exact ⟨o, fs, G, by rw [seatS_own hw.1]; exact ho, by rw [seatS_fork hw.1]; exact hf, hc,
    wrote_seatS hw⟩

/-- **Where the run "free-slot" of the block that rides returns**, in the seat's letters. -/
theorem freeSlotAs_atS {p : Par} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) {s s' : S} (h : run s = .ok s') :
    s' = seatS.setOwed s (seatS.owed s) := by
  obtain ⟨a, ha, rfl⟩ := freeSlotAtS hr h
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  change here = .lay a at ha
  subst ha
  rfl

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hearsAs_atS
#print axioms OnBytes.Desc.First.K4.seatS_fits
#print axioms OnBytes.Desc.First.K4.seatS_fits1
#print axioms OnBytes.Desc.First.K4.frontAs_atS
#print axioms OnBytes.Desc.First.K4.backAs_atS
#print axioms OnBytes.Desc.First.K4.freeSlotAs_atS
#print axioms OnBytes.Desc.First.K4.seatS_forkQ
