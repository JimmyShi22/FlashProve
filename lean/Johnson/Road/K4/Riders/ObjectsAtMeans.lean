-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/ObjectsAtMeans.lean: THE ITEM formsT m 2 "objects" AND ITS PUBLIC TEST RIDE
OVER A YES OF K4's PIECE, AT THE TABLE's OWN SENTENCES: the two lines hobj and hObj of
Johnson/Road/K4/K4OfMeans.lean (k4Riders_of_means, k4Keeps_of_means), to their letter, out of
Johnson/Road/K4/Riders/Objects.lean, under the structure of equations K4Means and named premises.
Statements and proofs: a join.

  `link_forms`: where the generic reader answers, and the run is not the smallness test's equations,
    a link's reader (K9.readersOfLink) gives the generic reader's answer.
  `sized_of_ledgerB`, `free_of_freeAboveB`: what the table's two tests say at a layers' link.
  `next_le_sFv`: behind a hearing the merge's end value's slot is not below the ledger's next free
    number in front.
  `ObjAsks`: THE PREMISES, BY NAME (below). `at_yes`: what both lines draw out of a yes and the
    promise in front.
  **`hobj_of_means`**: the sentence from behind a yes to in front. **`hObj_of_means`**: the test
    from in front to behind.
No new argument.
**Limits.** ObjAsks IS A STRUCTURE OF PREMISES, NONE PAID HERE: Rd (segment m's readers are a
link's) · runs (the item stands for the two runs (1, "objects"), (1, "guests")) · fO, oRun, fG, gRun
(block number 1 of that link states the two runs, and they are an ObjRun and a GuestRun:
Johnson/Road/K4/Riders/ObjectsAtK3.lean shows it of the kind's own block, not of the seated link) ·
bare (A TEST WITH CODE on what the lookup heard: its rows name no entry: NO ITEM OF THE TABLE THAT
IS IMPORTED HERE SAYS IT: a public item is owed, made by the lookup's block) · St (ON A LETTER: the
stated data's mask row is the same at two states in LayRest: the line stMask of the structure
K4Reads) · front (the public test holds in front: it is tied to an item that is open there). Beside
it: K4Means (equations), AtK4, the table's test pubFit, D.links = links. Nothing says that a form is
worth 0 anywhere. Nothing on soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met
through Lean at no member.


-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4Reads
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.Riders.Objects
import Johnson.Road.K4.Total.NotFree
import Johnson.Road.K4.Slots.HearTrees
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Filled Later)
open OnBytes.Desc.First.K4 (Par seatS Rest hear hearFl engFl)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun reader_objects reader_guests objects_back
  objects_forward guests_holds guests_in hne_of_bare rowsOwn_of_hne)
open OnBytes.Desc.First.K4.Total (fills_before sFv_at)
open OnBytes.Desc.First.K4.Slots (merge_next hear_trees)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Strs Claim Link K9.readerOf K9.Readers K9.Readers.ofStates
  K9.readersOfLink K9.statesOfLink K9.LinkHoles K9.formsInT K9.Read K9.mergeOf)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Meaning pubFit ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillK4 (isLay look_agrees)
open VerifiableInference.Desc.Sound (Frame Piece strsOf meansQ onQ MsgT Stated formsTQ MsgQ)

/-! ## A link's readers and the generic ones -/

theorem link_forms {Hh : K9.LinkHoles} {l : Link S Claim} {b : ℕ} {name : String} {s : S}
    {R : K9.Read} (hn : (name == "K8.equations") = false)
    (hr : K9.readerOf (K9.statesOfLink l) b name s = some R) :
    (K9.readersOfLink Hh l).forms b name s =
      (K9.Readers.ofStates (K9.statesOfLink l)).forms b name s := by
  show (if name == "K8.equations" then Hh.small s
    else match K9.readerOf (K9.statesOfLink l) b name s with
      | some R => some R
      | Option.none => Hh.silent b name s) = K9.readerOf (K9.statesOfLink l) b name s
  rw [hn, hr]
  rfl

/-! ## What the table's two tests say at a layers' link -/

theorem sized_of_ledgerB {s : S} {al : LayOwn} (ha : s.here = .lay al) (h : ledgerB s = true) :
    PscRun.Sized al.F := by
  have e : s.fork? = some al.F := by simp only [S.fork?, ha]
  unfold ledgerB at h
  rw [e] at h
  have h' : (al.F.vp.size == al.F.ns && al.F.mf.size == al.F.ns &&
      al.F.gotF.size == al.F.ns) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem free_of_freeAboveB {s : S} {al : LayOwn} {n : ℕ} (ha : s.here = .lay al)
    (hS : PscRun.Sized al.F) (h : freeAboveB n s = true) :
    ∀ j, al.F.next ≤ j → ¬ Filled al.F j := by
  have e : s.fork? = some al.F := by simp only [S.fork?, ha]
  unfold freeAboveB at h
  rw [e] at h
  have h' : (((List.range (al.F.ns - al.F.next)).all fun j =>
      !al.F.gotF.getD (al.F.next + j) true) && al.F.ns == n) = true := h
  rw [Bool.and_eq_true] at h'
  intro j hj hfil
  unfold Filled at hfil
  by_cases hlt : j < al.F.ns
  · have k : (!al.F.gotF.getD (al.F.next + (j - al.F.next)) true) = true :=
      List.all_eq_true.1 h'.1 (j - al.F.next) (List.mem_range.2 (by omega))
    rw [Nat.add_sub_cancel' hj] at k
    have hs : j < al.F.gotF.size := by
      rw [hS.2.2]
      exact hlt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some] at k hfil
    rw [hfil] at k
    cases k
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [hS.2.2]; omega)] at hfil
    cases hfil

/-- Behind a hearing the merge's end value's slot is not below the ledger's next free number in
front. -/
theorem next_le_sFv {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : PscRun.Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    F.next ≤ o.wo.sFv := by
  obtain ⟨G5, u5, cl, s5, f5, _, hE⟩ := fills_before hF h
  obtain ⟨m1, _⟩ := merge_next s5 hE
  have e := sFv_at h
  have n5 := f5.next
  omega

/-! ## The join -/

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **The premises, by name.** -/
structure ObjAsks (Fr : Frame) (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT))
    (D : K4Data Xi P Tok rows cols nR kC X) (Z : P) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (Hh : K9.LinkHoles) (l : Link S Claim) (nO nG : String)
    (runO runG : ℕ → S → Except String (List Claim × S)) : Prop where
  Rd : D.Rd m = K9.readersOfLink Hh l
  runs : D.runs m 2 "objects" = [(1, "objects"), (1, "guests")]
  fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO)
  oRun : ObjRun runO
  fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG)
  gRun : GuestRun runG
  bare : ∀ (a : S × Fr.E.Str) (al : LayOwn) (g : Forest.Heard),
    onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none → a.1.here = .lay al →
    al.lookHeard = some g → (g.rows.all fun f => f.ents.isEmpty) = true
  St : ∀ s s' : S, LayRest s s' → ∀ B j, (D.St.at1 s' B).mask j = (D.St.at1 s B).mask j
  front : ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
    Mg.pub (.formsInT m 2 "objects") (Z, a.1) = true

variable {Hh : K9.LinkHoles} {l : Link S Claim} {nO nG : String}
  {runO runG : ℕ → S → Except String (List Claim × S)}

/-- The public test at the item, written out at the two runs. -/
theorem pub_objects (E : K4Means Mg D) (A : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG)
    (s : S) : Mg.pub (.formsInT m 2 "objects") (Z, s) =
      (K9.formsInT (K9.readersOfLink Hh l) (D.N.sent m 0) 1 "objects" s &&
        (K9.formsInT (K9.readersOfLink Hh l) (D.N.sent m 0) 1 "guests" s && true)) := by
  rw [E.formsInT, A.runs, A.Rd]
  rfl

/-- What both lines draw out of a yes and the promise in front. -/
theorem at_yes (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hfit : pubFit Mg.more links ps = true)
    (A : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG) {a : S × Fr.E.Str}
    {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    (hon : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (y : Yes seatS par q a τ fo o G) :
    ∃ (al al' : LayOwn) (g : Forest.Heard) (o' : Own) (G' : Fork), a.1.here = .lay al ∧
      (behindOf seatS q a τ o G).1.here = .lay al' ∧ Rest a.1 (behindOf seatS q a τ o G).1 ∧
      (behindOf seatS q a τ o G).1.fork? = some G' ∧ Later al.F G' ∧ G'.trees = al.F.trees ∧
      al.lookHeard = some g ∧ (∀ f ∈ g.rows.toList, f.ents.toList = []) ∧ PscRun.Sized al.F ∧
      K9.mergeOf (behindOf seatS q a τ o G).1 = some o'.wo.sFv ∧ al.F.next ≤ o'.wo.sFv ∧
      (K9.readersOfLink Hh l).forms 1 "objects" a.1 =
        K9.readerOf (K9.statesOfLink l) 1 "objects" a.1 ∧
      (K9.readersOfLink Hh l).forms 1 "objects" (behindOf seatS q a τ o G).1 =
        K9.readerOf (K9.statesOfLink l) 1 "objects" (behindOf seatS q a τ o G).1 := by
  obtain ⟨al, fo', o', G', hal, hfo, hfork, hLat, hown, _, _, _, hR, _, _, t, u, hh0⟩ :=
    kept_of_yes y
  have hlay : isLay D.links m = true := by
    rw [hlinks]
    unfold isLay
    rw [H.sub]
    rfl
  have hlook := k4_pub_front D.N Mg Z H hfit hon hu (.look m) (by simp)
  rw [E.look m _ hlay] at hlook
  have hh : al.lookHeard = some fo' := (look_agrees hlook hal).symm.trans hfo
  have hne := hne_of_bare (A.bare a al fo' hon hu hal hh)
  have hled := k4_pub_front D.N Mg Z H hfit hon hu (.ledger m) (by simp)
  rw [E.ledger] at hled
  have hS : PscRun.Sized al.F := sized_of_ledgerB hal hled
  obtain ⟨al', hal', _, _, _, hlh⟩ := hR.here al hal
  have hown' : al'.own = some o' := by
    have e : (behindOf seatS q a τ o G).1.own? = al'.own := by simp only [S.own?, hal']
    rw [← e]
    exact hown
  have hmg : K9.mergeOf (behindOf seatS q a τ o G).1 = some o'.wo.sFv := by
    simp only [K9.mergeOf, hal', hown', Option.map_some]
  have rO : K9.readerOf (K9.statesOfLink l) 1 "objects" a.1 =
      some { forms := fo'.rows.toList, late := [] } := by
    rw [reader_objects A.fO A.oRun hal hh, if_pos (rowsOwn_of_hne al.F hne)]
  have rO' : K9.readerOf (K9.statesOfLink l) 1 "objects" (behindOf seatS q a τ o G).1 =
      some { forms := fo'.rows.toList, late := [] } := by
    rw [reader_objects A.fO A.oRun hal' (hlh.trans hh), if_pos (rowsOwn_of_hne al'.F hne)]
  exact ⟨al, al', fo', o', G', hal, hal', hR, hfork, hLat, hear_trees hS hh0, hh, hne, hS, hmg,
    next_le_sFv hS hh0, link_forms (by decide) rO, link_forms (by decide) rO'⟩

/-- **The line hobj.** -/
theorem hobj_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hfit : pubFit Mg.more links ps = true)
    (A : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG) :
    ∀ a τ fo o G w, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G →
      meansQ D.N Mg (fun s => (Z, s)) (.formsT m 2 "objects") (behindOf seatS q a τ o G) w →
      meansQ D.N Mg (fun s => (Z, s)) (.formsT m 2 "objects") a w := by
  intro a τ fo o G w hon hu y hm
  obtain ⟨al, al', g, o', G', hal, hal', hR, hfork, hLat, htr, hh, hne, hS, hmg, hsF, e, e'⟩ :=
    at_yes E H hlinks hfit A hon hu y
  have hin := A.front a hon hu
  rw [pub_objects E A, Bool.and_eq_true] at hin
  have hm' : Mg.formsT m 2 "objects" (Z, (behindOf seatS q a τ o G).1)
      (strsOf Fr (behindOf seatS q a τ o G).2) w := hm
  rw [E.formsT] at hm'
  obtain ⟨h1, _⟩ := hm'
  have hb := h1 (1, "objects") (by rw [A.runs]; simp)
  rw [A.Rd] at hb
  have hb' := objects_back hal hR hfork hLat htr A.fO A.oRun hh hne e e' hin.1
    (A.St _ _ ⟨⟨al, hal⟩, hR⟩) hb
  show Mg.formsT m 2 "objects" (Z, a.1) (strsOf Fr a.2) w
  rw [E.formsT]
  refine ⟨fun p hp => ?_, fun e0 => absurd e0 (by decide)⟩
  rw [A.runs] at hp
  rw [A.Rd]
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hb'
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact guests_holds hal A.fG A.gRun
        (link_forms (by decide) (reader_guests A.fG A.gRun hal))
    · cases hp

/-- **The line hObj.** -/
theorem hObj_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hfit : pubFit Mg.more links ps = true)
    (A : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → Mg.pub (.formsInT m 2 "objects") (Z, a.1) = true →
      Mg.pub (.formsInT m 2 "objects") (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G hon hu y hin
  obtain ⟨al, al', g, o', G', hal, hal', hR, hfork, hLat, htr, hh, hne, hS, hmg, hsF, e, e'⟩ :=
    at_yes E H hlinks hfit A hon hu y
  have hfa := k4_pub_front D.N Mg Z H hfit hon hu (.freeAbove m) (by simp)
  rw [E.freeAbove] at hfa
  have hfree : ∀ j, al.F.next ≤ j → ¬ Filled al.F j := by
    cases hn : D.nsOf m with
    | none =>
      rw [hn] at hfa
      cases hfa
    | some n =>
      rw [hn] at hfa
      exact free_of_freeAboveB hal hS hfa
  rw [pub_objects E A, Bool.and_eq_true] at hin
  have hf := objects_forward hal hR hfork hLat htr A.fO A.oRun hh hmg hsF hS hfree e e' hin.1
  rw [pub_objects E A, hf, guests_in hal' A.fG A.gRun
    (link_forms (by decide) (reader_guests A.fG A.gRun hal'))]
  rfl

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.link_forms
#print axioms OnBytes.Road.K4.Riders.sized_of_ledgerB
#print axioms OnBytes.Road.K4.Riders.free_of_freeAboveB
#print axioms OnBytes.Road.K4.Riders.next_le_sFv
#print axioms OnBytes.Road.K4.Riders.pub_objects
#print axioms OnBytes.Road.K4.Riders.at_yes
#print axioms OnBytes.Road.K4.Riders.hobj_of_means
#print axioms OnBytes.Road.K4.Riders.hObj_of_means
