-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkPscRead.lean: the arithmetic of the program's zero-knowledge sumcheck, read in the
field.

OnBytes/Iop/Psc.lean computes on elements of three machine words. OnBytes/Slice/KeyPscF.lean and
OnBytes/Slice/KeyPscRun.lean have the same functions on lists over the field. This file compares
them: each function of the program, read in the field (readE, OnBytes/Slice/ProgField.lean), is the
function over the field at the arguments read in the field.

A summand holds a function (its coefficients at a point and at shown values), so it is not read by a
map: SummandReads S SF says that SF has the numbers of S and that its function is that of S, read.

Main definitions: readForm, readPC, readW, readClaim, readRound, readHeard, readOut, SummandReads.

Main theorems: read_polyAt, read_dot, read_powers, read_complete, read_hidingWalk, read_claimAfter,
read_varsOf, read_masksOf, read_formOK, read_run, read_run_some.

Not claimed. Nothing on a run on a view, on a protocol, on soundness or on hiding. readE is not
injective (a word that is not below the prime counts as its residue), so no statement here leads
from the field back to the program's words.

-/
import OnBytes.Slice.KeyPscRun
import OnBytes.Slice.ProgField

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb

/-! ## How the sumcheck's records are read -/

/-- A mask form, read: each coefficient is read; the entries stay. -/
def readForm (m : MaskForm) : PscF.MaskForm := m.map fun t => (t.1, readE t.2)

/-- A claim on a map at a point, read. -/
def readPC (c : PointClaim) : PscF.PointClaim :=
  ⟨c.point.map readE, readForm c.masks, readE c.value⟩

/-- A weight, read. -/
def readW (w : Psc.Weight) : PscF.Weight :=
  ⟨w.d, w.moment.map readE, w.psi.map readE, w.fixed, readE w.fixedInv⟩

/-- A sumcheck's claim, read. -/
def readClaim (c : Psc.Claim) : PscF.Claim := ⟨c.vars.map readW, readForm c.masks, readE c.target⟩

/-- What was sent and drawn in one round, read. -/
def readRound (r : List E × E) : List GE × GE := (r.1.map readE, readE r.2)

/-- What was heard in one run, read. -/
def readHeard (h : Psc.Heard) : PscF.Heard :=
  ⟨readE h.mu, readE h.eps, h.rounds.map readRound, h.values.map readE⟩

/-- What one run hands on, read. -/
def readOut (o : Psc.Out) : PscF.Out :=
  ⟨o.point.map readE, readForm o.rowMasks, o.rowMaps.map readE, readE o.rowTarget,
    o.ends.map readPC, readE o.eps, o.beta.map readE⟩

/-- SF is the summand S, read: the same three numbers, and the coefficients of S at a point and at
shown values, read, are those of SF at the point and the values, read. -/
structure SummandReads (S : Psc.Summand) (SF : PscF.Summand) : Prop where
  shown : SF.shown = S.shown
  kept : SF.kept = S.kept
  degree : SF.degree = S.degree
  coeffs : ∀ p v, (S.coeffs p v).map readE = SF.coeffs (p.map readE) (v.map readE)

/-! ## Polynomials, sums of products, powers -/

/-- The value of a polynomial. -/
theorem read_polyAt (x : E) : ∀ g : List E,
    readE (Psc.polyAt g x) = PscF.polyAt (g.map readE) (readE x)
  | [] => readE_zero
  | c :: g => by
    show readE (addE (mulE (Psc.polyAt g x) x) c) = PscF.polyAt (g.map readE) (readE x) * readE x +
      readE c
    rw [readE_add, readE_mul, read_polyAt x g]

/-- The loop of a sum of products, from any value. -/
theorem read_dotLoop : ∀ (l : List (E × E)) (r : E),
    readE (l.foldl (fun r p => addE r (mulE p.1 p.2)) r) =
      (l.map fun p => (readE p.1, readE p.2)).foldl (fun r p => r + p.1 * p.2) (readE r)
  | [], _ => rfl
  | p :: l, r => by
    rw [List.foldl_cons, read_dotLoop l, readE_add, readE_mul]
    rfl

/-- Reading the members of two lists and pairing them is pairing them and reading the pairs. -/
theorem zip_read {α β α' β' : Type} (f : α → α') (g : β → β') : ∀ (a : List α) (b : List β),
    (a.map f).zip (b.map g) = (a.zip b).map fun p => (f p.1, g p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => congrArg ((f x, g y) :: ·) (zip_read f g a b)

/-- The same where only the second list is read. -/
theorem zip_read_right {α β β' : Type} (g : β → β') : ∀ (a : List α) (b : List β),
    a.zip (b.map g) = (a.zip b).map fun p => (p.1, g p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => congrArg ((x, g y) :: ·) (zip_read_right g a b)

/-- The sum of products. -/
theorem read_dot (a b : List E) :
    readE (Psc.dot a b) = PscF.dot (a.map readE) (b.map readE) := by
  unfold Psc.dot PscF.dot
  rw [read_dotLoop, zip_read, readE_zero]

/-- The loop of powers. -/
theorem read_powersLoop (x : E) : ∀ (n : ℕ) (c : E) (done : List E),
    (Psc.powersLoop x n c done).map readE =
      PscF.powersLoop (readE x) n (readE c) (done.map readE)
  | 0, _, done => List.map_reverse
  | n + 1, c, done => by
    show (Psc.powersLoop x n (mulE c x) (c :: done)).map readE =
      PscF.powersLoop (readE x) n (readE c * readE x) (readE c :: done.map readE)
    rw [read_powersLoop x n, readE_mul]
    rfl

/-- The powers. -/
theorem read_powers (c x : E) (n : ℕ) :
    (Psc.powers c x n).map readE = PscF.powers (readE c) (readE x) n :=
  read_powersLoop x n c []

/-- A mask form times an element. -/
theorem read_scaleForm (c : E) (m : MaskForm) :
    readForm (Psc.scaleForm c m) = PscF.scaleForm (readE c) (readForm m) := by
  unfold readForm Psc.scaleForm PscF.scaleForm
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  show (t.1, readE (mulE c t.2)) = (t.1, readE c * readE t.2)
  rw [readE_mul]

/-- Two mask forms, one behind the other. -/
theorem readForm_append (m m' : MaskForm) : readForm (m ++ m') = readForm m ++ readForm m' :=
  List.map_append

/-! ## Weights -/

/-- The weight under one factor of the equality polynomial. -/
theorem readW_equality (z : E) (d : ℕ) :
    readW (Psc.Weight.equality z d) = PscF.Weight.equality (readE z) d := by
  unfold readW Psc.Weight.equality PscF.Weight.equality
  simp only [List.map_cons, List.map_replicate, List.map_nil, readE_one]

/-- The weight that reads at 0. -/
theorem readW_atZero (d : ℕ) : readW (Psc.Weight.atZero d) = PscF.Weight.atZero d := by
  unfold Psc.Weight.atZero PscF.Weight.atZero
  rw [readW_equality, readE_zero]

/-- The weight of the plain sum. -/
theorem readW_plain (d : ℕ) : readW (Psc.Weight.plain d) = PscF.Weight.plain d := by
  unfold readW Psc.Weight.plain PscF.Weight.plain
  simp only [List.map_cons, List.map_replicate, List.map_nil, readE_one, readE_zero, readE_add]

/-- The test of a weight's sizes. -/
theorem read_fits (w : Psc.Weight) : (readW w).fits = w.fits := by
  unfold PscF.Weight.fits Psc.Weight.fits readW
  simp only [List.length_map]

/-- The whole polynomial of a round. -/
theorem read_complete (w : Psc.Weight) (sent : List E) (claim : E) :
    (w.complete sent claim).map readE = (readW w).complete (sent.map readE) (readE claim) := by
  unfold Psc.Weight.complete PscF.Weight.complete readW
  simp only [List.map_append, List.map_cons, List.map_take, List.map_drop, readE_mul, readE_sub,
    read_dot, readE_zero]

/-- The number of coefficients of the hiding polynomial. -/
theorem read_hidingEntries (ws : List Psc.Weight) :
    PscF.hidingEntries (ws.map readW) = Psc.hidingEntries ws := by
  unfold PscF.hidingEntries Psc.hidingEntries
  rw [List.map_map]
  rfl

/-- A weight with a challenge, read. -/
def readWG (p : Psc.Weight × E) : PscF.Weight × GE := (readW p.1, readE p.2)

/-- The hiding polynomial's linear form and the product of the polynomials psi. -/
theorem read_hidingWalk : ∀ l : List (Psc.Weight × E),
    ((Psc.hidingWalk l).1.map readE, readE (Psc.hidingWalk l).2) =
      PscF.hidingWalk (l.map readWG)
  | [] => by
    show (([] : List GE), readE oneE) = ([], 1)
    rw [readE_one]
  | [(w, g)] => by
    show ((Psc.powers oneE g w.d).map readE, readE (Psc.polyAt w.psi g)) =
      (PscF.powers 1 (readE g) w.d, PscF.polyAt (w.psi.map readE) (readE g))
    rw [read_powers, read_polyAt, readE_one]
  | (w, g) :: p :: rest => by
    have ih := read_hidingWalk (p :: rest)
    show ((Psc.powers (mulE (Psc.hidingWalk (p :: rest)).2 g) g (w.d - 1) ++
        (Psc.hidingWalk (p :: rest)).1).map readE,
        readE (mulE (Psc.hidingWalk (p :: rest)).2 (Psc.polyAt w.psi g))) =
      (PscF.powers ((PscF.hidingWalk ((p :: rest).map readWG)).2 * readE g) (readE g) (w.d - 1) ++
        (PscF.hidingWalk ((p :: rest).map readWG)).1,
        (PscF.hidingWalk ((p :: rest).map readWG)).2 * PscF.polyAt (w.psi.map readE) (readE g))
    rw [← ih, List.map_append, read_powers, readE_mul, readE_mul, read_polyAt]

/-- The running claim after the rounds. -/
theorem read_claimAfter : ∀ (ws : List Psc.Weight) (rs : List (List E × E)) (R : E),
    readE (Psc.claimAfter ws rs R) =
      PscF.claimAfter (ws.map readW) (rs.map readRound) (readE R)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | w :: ws, (q, g) :: rs, R => by
    show readE (Psc.claimAfter ws rs (Psc.polyAt (w.complete q R) g)) =
      PscF.claimAfter (ws.map readW) (rs.map readRound)
        (PscF.polyAt ((readW w).complete (q.map readE) (readE R)) (readE g))
    rw [read_claimAfter ws rs, read_polyAt, read_complete]

/-! ## One run -/

section
variable {S : Psc.Summand} {SF : PscF.Summand}

/-- The variables of the masked sumcheck. -/
theorem read_varsOf (hS : SummandReads S SF) (c : Psc.Claim) :
    PscF.varsOf (readClaim c) SF = (Psc.varsOf c S).map readW := by
  unfold PscF.varsOf Psc.varsOf
  rw [hS.shown, hS.degree]
  split
  · rfl
  · rw [List.map_append, List.map_cons, List.map_nil, readW_atZero]
    rfl

/-- The number of mask entries that one run uses. -/
theorem read_masksOf (hS : SummandReads S SF) (c : Psc.Claim) :
    PscF.masksOf (readClaim c) SF = Psc.masksOf c S := by
  unfold PscF.masksOf Psc.masksOf
  rw [read_varsOf hS, read_hidingEntries, hS.shown]

/-- The test of the form of claim and summand. -/
theorem read_formOK (hS : SummandReads S SF) (c : Psc.Claim) :
    PscF.formOK (readClaim c) SF = Psc.formOK c S := by
  unfold PscF.formOK Psc.formOK readClaim
  rw [hS.shown, hS.degree]
  simp only [List.all_map, List.isEmpty_map]
  congr 1
  exact congrArg (fun f => c.vars.all f) (funext read_fits)

/-- What the program's run tests: the condition in the text of Psc.run. -/
def pscTests (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) : Bool :=
  Psc.formOK c S && fresh.length == Psc.masksOf c S &&
    h.rounds.length == (Psc.varsOf c S).length && h.values.length == S.shown &&
    (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length == 1 + S.kept &&
    (((Psc.varsOf c S).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)

/-- What the program's run returns if its tests pass: the record in the text of Psc.run. -/
def pscOut (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) : Psc.Out :=
  let vars := Psc.varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := Psc.hidingWalk (vars.zip challenges)
  let last := Psc.claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if S.shown == 0 then none else challenges.getLast?
  { point := point
    rowMasks := fresh.zip hw.1 ++ Psc.scaleForm (mulE h.eps hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => mulE h.eps x
    rowTarget := subE last (mulE h.eps (a.headD zeroE))
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
    eps := h.eps
    beta := beta }

/-- The program's run, in two parts. -/
theorem psc_run_eq (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) :
    Psc.run c S fresh h = if pscTests c S fresh h then some (pscOut c S fresh h) else none := rfl

/-- The challenges of rounds that are read. -/
theorem read_challenges (rs : List (List E × E)) :
    (rs.map readRound).map (·.2) = (rs.map (·.2)).map readE := by
  rw [List.map_map, List.map_map]
  rfl

/-- Entries with coefficients from a list. -/
theorem readForm_zip : ∀ (fr : List Slot) (l : List E),
    readForm (fr.zip l) = fr.zip (l.map readE)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: fr, a :: l => congrArg ((s, readE a) :: ·) (readForm_zip fr l)

/-- The first member of a list; 0 if there is none. -/
theorem read_headD (l : List E) : (l.map readE).headD 0 = readE (l.headD zeroE) := by
  cases l with
  | nil => exact readE_zero.symm
  | cons _ _ => rfl

/-- A value that may be missing; 0 if it is. -/
theorem read_optD (b : Option E) : (b.map readE).getD 0 = readE (b.getD zeroE) := by
  cases b with
  | none => exact readE_zero.symm
  | some _ => rfl

/-- A member of a list; 0 beyond the end. -/
theorem read_getD (l : List E) (i : ℕ) : (l.map readE).getD i 0 = readE (l.getD i zeroE) := by
  rw [← readE_zero, List.getD_map]

/-- The coefficients of the summand at the point of the challenges and at the shown values. -/
theorem read_coeffs (hS : SummandReads S SF) (c : Psc.Claim) (h : Psc.Heard) :
    SF.coeffs (((readHeard h).rounds.map (·.2)).take (readClaim c).vars.length)
        (readHeard h).values =
      (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).map readE := by
  show SF.coeffs (((h.rounds.map readRound).map (·.2)).take (c.vars.map readW).length)
    (h.values.map readE) = _
  rw [read_challenges, List.length_map, ← List.map_take, hS.coeffs]

/-- **What a run tests.** -/
theorem read_tests (hS : SummandReads S SF) (c : Psc.Claim) (fresh : List Slot) (h : Psc.Heard) :
    PscF.tests (readClaim c) SF fresh (readHeard h) = pscTests c S fresh h := by
  unfold PscF.tests pscTests
  rw [read_coeffs hS, read_formOK hS, read_masksOf hS, read_varsOf hS, hS.shown, hS.kept]
  have h1 : (((Psc.varsOf c S).map readW).zip (readHeard h).rounds).all
      (fun p => p.2.1.length + 1 == p.1.d) =
      ((Psc.varsOf c S).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d := by
    show (((Psc.varsOf c S).map readW).zip (h.rounds.map readRound)).all _ = _
    rw [zip_read, List.all_map]
    refine congrArg (fun f => ((Psc.varsOf c S).zip h.rounds).all f) (funext fun p => ?_)
    show ((p.2.1.map readE).length + 1 == p.1.d) = _
    rw [List.length_map]
  rw [h1]
  show (_ && _ && (h.rounds.map readRound).length == _ && (h.values.map readE).length == _ &&
    _ && _) = _
  simp only [List.length_map]

/-- **What a run returns.** -/
theorem read_out (hS : SummandReads S SF) (c : Psc.Claim) (fresh : List Slot) (h : Psc.Heard) :
    PscF.outOf (readClaim c) SF fresh (readHeard h) = readOut (pscOut c S fresh h) := by
  have hw : PscF.hidingWalk ((PscF.varsOf (readClaim c) SF).zip
      ((readHeard h).rounds.map (·.2))) =
      ((Psc.hidingWalk ((Psc.varsOf c S).zip (h.rounds.map (·.2)))).1.map readE,
        readE (Psc.hidingWalk ((Psc.varsOf c S).zip (h.rounds.map (·.2)))).2) := by
    show PscF.hidingWalk ((PscF.varsOf (readClaim c) SF).zip
      ((h.rounds.map readRound).map (·.2))) = _
    rw [read_varsOf hS, read_challenges, zip_read, read_hidingWalk]
    rfl
  have hp : ((readHeard h).rounds.map (·.2)).take (readClaim c).vars.length =
      ((h.rounds.map (·.2)).take c.vars.length).map readE := by
    show ((h.rounds.map readRound).map (·.2)).take (c.vars.map readW).length = _
    rw [read_challenges, List.length_map, List.map_take]
  have hb : (if SF.shown == 0 then none else ((readHeard h).rounds.map (·.2)).getLast?) =
      (if S.shown == 0 then none else (h.rounds.map (·.2)).getLast?).map readE := by
    show (if SF.shown == 0 then none else ((h.rounds.map readRound).map (·.2)).getLast?) = _
    rw [hS.shown, read_challenges, List.getLast?_map]
    split <;> rfl
  have hl : PscF.claimAfter (PscF.varsOf (readClaim c) SF) (readHeard h).rounds
      ((readHeard h).mu + (readHeard h).eps * (readClaim c).target) =
      readE (Psc.claimAfter (Psc.varsOf c S) h.rounds (addE h.mu (mulE h.eps c.target))) := by
    rw [read_claimAfter, read_varsOf hS, readE_add, readE_mul]
    rfl
  unfold PscF.outOf
  simp only []
  rw [hw, hb, hl, read_coeffs hS, hp]
  unfold readOut pscOut
  simp only [readForm_append, readForm_zip, read_scaleForm, readE_mul, readE_sub, read_headD,
    List.length_map, List.map_map, List.map_drop]
  refine congrArg₂ (fun a b => (⟨_, _, a, _, b, _, _⟩ : PscF.Out)) ?_ ?_
  · refine congrArg (List.drop 1) (List.map_congr_left fun x _ => ?_)
    exact (readE_mul _ _).symm
  · show List.map _ (List.zip _ (h.values.map readE)) = _
    rw [zip_read_right, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    show (⟨_, [(p.1, _)], readE p.2⟩ : PscF.PointClaim) = ⟨_, [(p.1, _)], readE p.2⟩
    rw [read_optD]

/-- **The program's run, read in the field, is the run over the field** at the claim, the summand
and what was heard, read in the field. -/
theorem read_run (hS : SummandReads S SF) (c : Psc.Claim) (fresh : List Slot) (h : Psc.Heard) :
    (Psc.run c S fresh h).map readOut = PscF.run (readClaim c) SF fresh (readHeard h) := by
  rw [psc_run_eq, PscF.run_eq, read_tests hS, read_out hS]
  split <;> rfl

/-- If the program's run returns a value, the tests over the field pass, and the value, read, is
what the run over the field returns. -/
theorem read_run_some (hS : SummandReads S SF) (c : Psc.Claim) (fresh : List Slot) (h : Psc.Heard)
    (o : Psc.Out) (ho : Psc.run c S fresh h = some o) :
    PscF.tests (readClaim c) SF fresh (readHeard h) = true ∧
      readOut o = PscF.outOf (readClaim c) SF fresh (readHeard h) := by
  rw [psc_run_eq] at ho
  rw [read_tests hS, read_out hS]
  split at ho
  · next ht => exact ⟨ht, congrArg readOut (Option.some.inj ho).symm⟩
  · cases ho

end

end OnBytes.Slice
