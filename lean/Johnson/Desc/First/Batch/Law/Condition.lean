-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Condition.lean (kind K9): THEOREMS BY AN EVALUATION
IN LEAN's KERNEL: THE CONDITION OF K9's OWN LEMMA ON PUBLIC NUMBERS HOLDS AT EVERY ONE OF K9's
ROUNDS OF THE TWO WRITTEN EXAMPLES.
K9 uses no proved block of the library: its soundness lemma is its own (Law/AtCap.lean and the rows
above it). That lemma has one condition on public numbers: the bound d on the exponents of the
batching element is at most 2^60. At a segment d is the round's entry's "rows" less 1: the exponents
are below the number of rows that the element combines. So the condition reads: 1 ≤ rows and
rows - 1 ≤ 2^60.
THE NUMBERS are the library's written lists of a proof file's rounds (Johnson/G/DryProofLit.lean:
dryProofFull, dryProofSmall: the first chain's list). No file is read here. A written list stands
there as distinct RECORDS and a list of RUNS (how often, which record), unrolled by unrunR. The
kernel walks the records and the runs here, never the unrolled list (48,293 rounds at the full
size); two small lemmas carry the results to the unrolled list's members.
  of_mem_unrunR, mem_unrunR_of   a member of the unrolled list is a record; a record of a run that
                is not empty is a member.
  rowsOk r, full_named, small_named   the two bounds AT EVERY ROUND OF THE FIRST CHAIN's LIST THAT
                BEARS THE NAME "BAT-sigma", whichever kind's it is.
  at_written    THE FORM FOR A LAW TO SPEND: a place p of K9 whose round (K9's entry at p; elements
                drawn; nothing sent or opened) IS A MEMBER of one of the two written lists has
                1 ≤ p.rows, p.rows - 1 ≤ 2^60, and K9's count at d := p.rows - 1 is at most the cap
                (Err.cap 128). It asks nothing on WHERE in the list the round stands. (A description
                whose test seatPinnedProof, Johnson/Desc/Ok/PlanWritten/Test.lean, says yes at the
                full size's key has the full size's written list as its declared rounds, written
                out: so its blocks' rounds are members. That step is not made here.)
  workOk r, full_work, small_work, no_work   at such a member p.work = 0: NO WORK STANDS AT A ROUND
                OF THAT NAME in either list: so the cap there counts no bits of work among the
                round's written challenges. (The bound itself holds at any work: Law/AtCap.lean:
                num_k9.)
  k9Runs recs runs   THAT THE PREMISE CAN BE MET, AND BY WHAT: the records of the runs that stand at
                K9's places: named "BAT-sigma", AND THE NEXT RUN's RECORD IS NAMED "BAT": the
                closing's first round; AND THE RUN IS ONE ROUND. (named: the records' numbers under
                a name; walk: along the runs, on these numbers alone; at the full size in the
                written file's own nine parts, joined by walk_append.)
                (Other kinds have rounds of that name. By a program over the written file's text, NO
                THEOREM HERE: of K9's very form, one element drawn and nothing sent: 61 at the full
                size, 11 at the small, each with at most 32 rows, none in front of a round named
                "BAT". THESE TOO MEET at_written's PREMISE: it admits more than K9's places:
                harmless: the bounds hold of them.)
  k9Ok r        r is K9's own round at r's rows and work (K9.entry; elements are drawn; nothing
                sent, no tree opened, nothing stored) · 1 ≤ rows · rows - 1 ≤ 2^60.
  full_rows, small_rows   the rows at these runs, in the chain's order: 25 and 5 numbers: one a
                segment. The largest: 32,005,923, below 2^25.
  full_ok, small_ok       k9Ok at each of them.
  K09Condition, k09Condition   THE ROW, a closed proposition: at_written's sentence; no_work's; and
                25 and 5 rounds, each A MEMBER of its written list and K9's own round at a place p,
                with the two bounds and the cap.
WHAT IT DOES NOT SAY. (1) That d := rows - 1 bounds the exponents: that is the hypothesis hok of
K9's law; at run time the door's test "K9.rows-counted" holds the claims and equations against rows.
(2) That the written lists are a file's plan's: by their own file's head they were written from a
print of the dry runs at one made-up request and the key of zeros; at the small example a test that
a build runs holds them against the program's dry runs; AT THE FULL SIZE NO SUCH TEST RUNS.
(3) That a description's block of kind K9 stands just at k9Runs' rounds: "in front of a run named
BAT" is this file's own reading of the chain's order, held against no driver's table: at_written
does not lean on it.
(4) That the data of the piece which a description makes of K9's draw ([k9Round p]: the format's
record of a round with what it declares) follow from a member of a written list (a round with what
is stored): a second step, not made here.

-/
import Johnson.G.DryProofLit
import Johnson.Desc.First.Batch.Law.AtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Flat OnBytes.Maker
open OnBytes.Params (Rounds)
open Johnson.G
open _root_.Run (ckP)
open _root_.Iop (Err)

/-- A member of the unrolled list is one of the records. -/
theorem of_mem_unrunR {recs : Rounds} {runs : List (Nat × Nat)} {r : Fmt.Round × List Fmt.Stored}
    (h : r ∈ unrunR recs runs) : r ∈ recs := by
  unfold unrunR at h
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 h
  cases e : recs[x.2]? with
  | none => simp [e] at hx
  | some a =>
    simp only [e, Option.elim, List.mem_replicate] at hx
    rw [hx.2]
    exact List.mem_of_getElem? e

/-- The record of a run that is not empty is a member of the unrolled list. -/
theorem mem_unrunR_of {recs : Rounds} {runs : List (Nat × Nat)} {r : Fmt.Round × List Fmt.Stored}
    (x : Nat × Nat) (hx : x ∈ runs) (hk : 0 < x.1) (hr : recs[x.2]? = some r) :
    r ∈ unrunR recs runs := by
  unfold unrunR
  refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
  simp only [hr, Option.elim, List.mem_replicate]
  exact ⟨by omega, trivial⟩

/-- The two bounds, at a round that bears the name. -/
def rowsOk (r : Fmt.Round × List Fmt.Stored) : Bool :=
  r.1.entry.name != "BAT-sigma" ||
    (decide (1 ≤ r.1.entry.rows) && decide (r.1.entry.rows - 1 ≤ 2 ^ 60))

theorem full_recs : dryProofRecsFull.all rowsOk = true := by
  decide +kernel

theorem small_recs : dryProofRecsSmall.all rowsOk = true := by
  decide +kernel

theorem full_named (r : Fmt.Round × List Fmt.Stored) (h : r ∈ dryProofFull.1) :
    rowsOk r = true :=
  List.all_eq_true.1 full_recs r (of_mem_unrunR h)

theorem small_named (r : Fmt.Round × List Fmt.Stored) (h : r ∈ dryProofSmall.1) :
    rowsOk r = true :=
  List.all_eq_true.1 small_recs r (of_mem_unrunR h)

/-- **The form for a law to spend.** -/
theorem at_written (p : K9.Where) (st : List Fmt.Stored)
    (h : ({ entry := K9.entry p, kind := .elems }, st) ∈ dryProofFull.1 ++ dryProofSmall.1) :
    1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧
      Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
        (Err.cap 128 (uLT (ckP .two) [k9Round p])) := by
  have hr : rowsOk ({ entry := K9.entry p, kind := .elems }, st) = true := by
    rcases List.mem_append.1 h with h | h
    · exact full_named _ h
    · exact small_named _ h
  have h2 : 1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 := by
    simpa [rowsOk, K9.entry] using hr
  exact ⟨h2.1, h2.2, herr_cap_k9 p _ h2.2⟩

/-- No work, at a round that bears the name. -/
def workOk (r : Fmt.Round × List Fmt.Stored) : Bool :=
  r.1.entry.name != "BAT-sigma" || decide (r.1.entry.work = 0)

theorem full_work : dryProofRecsFull.all workOk = true := by
  decide +kernel

theorem small_work : dryProofRecsSmall.all workOk = true := by
  decide +kernel

/-- **No work stands at such a round**: so the cap there counts no bits of work among the round's
written challenges. -/
theorem no_work (p : K9.Where) (st : List Fmt.Stored)
    (h : ({ entry := K9.entry p, kind := .elems }, st) ∈ dryProofFull.1 ++ dryProofSmall.1) :
    p.work = 0 := by
  have hr : workOk ({ entry := K9.entry p, kind := .elems }, st) = true := by
    rcases List.mem_append.1 h with h | h
    · exact List.all_eq_true.1 full_work _ (of_mem_unrunR h)
    · exact List.all_eq_true.1 small_work _ (of_mem_unrunR h)
  simpa [workOk, K9.entry] using hr

/-! ## That the premise can be met: K9's own rounds in the two lists -/

/-- The numbers of the records that bear a name. -/
def named (recs : Rounds) (nm : String) : List Nat :=
  (List.range recs.length).filter fun i => (recs[i]?).any fun a => a.1.entry.name == nm

/-- A run x and the next run y: x is ONE round; y is not empty; x's record is among sig, y's among
bat. -/
def hit (sig bat : List Nat) (x y : Nat × Nat) : Bool :=
  decide (x.1 = 1) && decide (0 < y.1) && sig.contains x.2 && bat.contains y.2

/-- The walk along the runs, on numbers alone: the record's number of each run that is hit. -/
def walk (sig bat : List Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | x :: l =>
    (match l.head? with
      | some y => if hit sig bat x y then [x.2] else []
      | none => []) ++ walk sig bat l

/-- The walk can be cut: the front part sees one run of the back part. -/
theorem walk_append (sig bat : List Nat) (a b : List (Nat × Nat)) :
    walk sig bat (a ++ b) = walk sig bat (a ++ b.take 1) ++ walk sig bat b := by
  induction a with
  | nil =>
    cases b with
    | nil => rfl
    | cons y t => simp [walk]
  | cons x a ih =>
    have hh : (a ++ b).head? = (a ++ b.take 1).head? := by
      cases a with
      | nil => cases b <;> rfl
      | cons _ _ => rfl
    simp only [List.cons_append, walk]
    rw [ih, hh, List.append_assoc]

theorem take_one_append {a : List (Nat × Nat)} (b : List (Nat × Nat)) (h : a ≠ []) :
    (a ++ b).take 1 = a.take 1 := by
  cases a with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- What the walk gives is the record's number of a run of one round. -/
theorem walk_mem {sig bat : List Nat} {runs : List (Nat × Nat)} {i : Nat}
    (h : i ∈ walk sig bat runs) : (1, i) ∈ runs := by
  induction runs with
  | nil => simp [walk] at h
  | cons x l ih =>
    simp only [walk, List.mem_append] at h
    rcases h with h | h
    · cases e : l.head? with
      | none => simp [e] at h
      | some y =>
        simp only [e] at h
        split at h
        · rename_i hh
          simp only [hit, Bool.and_eq_true, decide_eq_true_eq] at hh
          have hx : x = (1, i) := Prod.ext hh.1.1.1 (List.mem_singleton.1 h).symm
          rw [hx]
          exact List.mem_cons_self
        · simp at h
    · exact List.mem_cons_of_mem _ (ih h)

/-- The records of the runs that stand at K9's places. -/
def k9Runs (recs : Rounds) (runs : List (Nat × Nat)) : Rounds :=
  (walk (named recs "BAT-sigma") (named recs "BAT") runs).filterMap fun i => recs[i]?

theorem k9Runs_mem {recs : Rounds} {runs : List (Nat × Nat)} {r : Fmt.Round × List Fmt.Stored}
    (h : r ∈ k9Runs recs runs) : r ∈ unrunR recs runs := by
  obtain ⟨i, hi, hr⟩ := List.mem_filterMap.1 h
  exact mem_unrunR_of (1, i) (walk_mem hi) Nat.one_pos hr

/-- The numbers of the full size's records named "BAT-sigma"; named "BAT". -/
def sigF : List Nat := [18, 20, 25, 28, 33, 47, 48, 55, 59, 60, 85, 86, 89, 90, 106]

def batF : List Nat := [34, 56, 61, 91, 94, 114, 122, 129]

theorem full_sigma : named dryProofRecsFull "BAT-sigma" = sigF := by
  decide +kernel

theorem full_bat : named dryProofRecsFull "BAT" = batF := by
  decide +kernel

theorem small_sigma : named dryProofRecsSmall "BAT-sigma" =
    [18, 20, 25, 28, 34, 47, 48, 55, 59, 60, 65, 66, 69, 70, 83] := by
  decide +kernel

theorem small_bat : named dryProofRecsSmall "BAT" = [35, 56, 61, 71, 73, 92, 98, 103] := by
  decide +kernel

/-! THE WALK AT THE FULL SIZE, IN THE WRITTEN FILE's OWN NINE PARTS, each with the next part's first
run behind it: so that no evaluation is long. -/

theorem full_w0 : walk sigF batF (dryProofRunsFull0p0 ++ dryProofRunsFull0p1.take 1) =
    [33, 55] := by
  decide +kernel

theorem full_w1 : walk sigF batF (dryProofRunsFull0p1 ++ dryProofRunsFull0p2.take 1) =
    [60, 55, 60] := by
  decide +kernel

theorem full_w2 : walk sigF batF (dryProofRunsFull0p2 ++ dryProofRunsFull0p3.take 1) =
    [55, 60, 55] := by
  decide +kernel

theorem full_w3 : walk sigF batF (dryProofRunsFull0p3 ++ dryProofRunsFull0p4.take 1) =
    [60, 55, 60] := by
  decide +kernel

theorem full_w4 : walk sigF batF (dryProofRunsFull0p4 ++ dryProofRunsFull0p5.take 1) =
    [55, 60, 55] := by
  decide +kernel

theorem full_w5 : walk sigF batF (dryProofRunsFull0p5 ++ dryProofRunsFull0p6.take 1) =
    [60, 55, 60] := by
  decide +kernel

theorem full_w6 : walk sigF batF (dryProofRunsFull0p6 ++ dryProofRunsFull0p7.take 1) =
    [55, 60, 55] := by
  decide +kernel

theorem full_w7 : walk sigF batF (dryProofRunsFull0p7 ++ dryProofRunsFull0p8.take 1) =
    [60, 55, 60] := by
  decide +kernel

theorem full_w8 : walk sigF batF (dryProofRunsFull0p8) =
    [55, 90] := by
  decide +kernel

theorem full_ne1 : dryProofRunsFull0p1 ≠ [] := by
  decide +kernel

theorem full_ne2 : dryProofRunsFull0p2 ≠ [] := by
  decide +kernel

theorem full_ne3 : dryProofRunsFull0p3 ≠ [] := by
  decide +kernel

theorem full_ne4 : dryProofRunsFull0p4 ≠ [] := by
  decide +kernel

theorem full_ne5 : dryProofRunsFull0p5 ≠ [] := by
  decide +kernel

theorem full_ne6 : dryProofRunsFull0p6 ≠ [] := by
  decide +kernel

theorem full_ne7 : dryProofRunsFull0p7 ≠ [] := by
  decide +kernel

theorem full_ne8 : dryProofRunsFull0p8 ≠ [] := by
  decide +kernel

theorem full_idx : walk sigF batF dryProofRunsFull0 =
    [
    33, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60,
    55, 90] := by
  simp only [dryProofRunsFull0, List.append_assoc]
  rw [walk_append, take_one_append _ full_ne1, full_w0,
    walk_append, take_one_append _ full_ne2, full_w1,
    walk_append, take_one_append _ full_ne3, full_w2,
    walk_append, take_one_append _ full_ne4, full_w3,
    walk_append, take_one_append _ full_ne5, full_w4,
    walk_append, take_one_append _ full_ne6, full_w5,
    walk_append, take_one_append _ full_ne7, full_w6,
    walk_append, full_w7, full_w8]
  rfl

theorem small_idx :
    walk [18, 20, 25, 28, 34, 47, 48, 55, 59, 60, 65, 66, 69, 70, 83]
      [35, 56, 61, 71, 73, 92, 98, 103] dryProofRunsSmall0 = [34, 55, 60, 55, 70] := by
  decide +kernel

theorem full_runs : k9Runs dryProofRecsFull dryProofRunsFull0 =
    ([
    33, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60, 55, 60,
    55, 90] : List Nat).filterMap
      fun i => dryProofRecsFull[i]? := by
  unfold k9Runs
  rw [full_sigma, full_bat, full_idx]

theorem small_runs : k9Runs dryProofRecsSmall dryProofRunsSmall0 =
    ([34, 55, 60, 55, 70] : List Nat).filterMap fun i => dryProofRecsSmall[i]? := by
  unfold k9Runs
  rw [small_sigma, small_bat, small_idx]

/-- K9's numbers off a written round; the place's own numbers, which its entry does not hold, are 0.
-/
def whereOf (r : Fmt.Round × List Fmt.Stored) : K9.Where :=
  { chain := 1, link := 0, piece := 0, pieceEq := 0, rows := r.1.entry.rows
    work := r.1.entry.work, sent := 0 }

/-- The test. -/
def k9Ok (r : Fmt.Round × List Fmt.Stored) : Bool :=
  decide (r.1 = { entry := K9.entry (whereOf r), kind := .elems }) && r.2.isEmpty &&
    decide (1 ≤ r.1.entry.rows) && decide (r.1.entry.rows - 1 ≤ 2 ^ 60)

theorem full_rows : (k9Runs dryProofRecsFull dryProofRunsFull0).map (·.1.entry.rows) =
    [
    32005923, 14166783, 32005793, 14166783, 32005793, 14166783, 32005793, 14166783, 32005793,
    14166783, 32005793, 14166783, 32005793, 14166783, 32005793, 14166783, 32005793, 14166783,
    32005793, 14166783, 32005793, 14166783, 32005793, 14166783, 24653737] := by
  rw [full_runs]
  decide +kernel

theorem small_rows : (k9Runs dryProofRecsSmall dryProofRunsSmall0).map (·.1.entry.rows) =
    [4347789, 2074535, 4343660, 2074535, 2712833] := by
  rw [small_runs]
  decide +kernel

theorem full_ok : (k9Runs dryProofRecsFull dryProofRunsFull0).all k9Ok = true := by
  rw [full_runs]
  decide +kernel

theorem small_ok : (k9Runs dryProofRecsSmall dryProofRunsSmall0).all k9Ok = true := by
  rw [small_runs]
  decide +kernel

/-- What the test's yes gives. -/
theorem of_k9Ok (r : Fmt.Round × List Fmt.Stored) (h : k9Ok r = true) :
    ∃ p : K9.Where, r = ({ entry := K9.entry p, kind := .elems }, []) ∧ 1 ≤ p.rows ∧
      p.rows - 1 ≤ 2 ^ 60 ∧
      Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
        (Err.cap 128 (uLT (ckP .two) [k9Round p])) := by
  simp only [k9Ok, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨whereOf r, Prod.ext h1 h2, h3, h4, herr_cap_k9 (whereOf r) _ h4⟩

/-- What is said of one of K9's rounds in a written list l. -/
def K9RoundIn (l : Rounds) (r : Fmt.Round × List Fmt.Stored) : Prop :=
  r ∈ l ∧ ∃ p : K9.Where, r = ({ entry := K9.entry p, kind := .elems }, []) ∧ 1 ≤ p.rows ∧
    p.rows - 1 ≤ 2 ^ 60 ∧
    Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
      (Err.cap 128 (uLT (ckP .two) [k9Round p]))

/-- **Row K09_condition.** -/
def K09Condition : Prop :=
  (∀ (p : K9.Where) (st : List Fmt.Stored),
      ({ entry := K9.entry p, kind := .elems }, st) ∈ dryProofFull.1 ++ dryProofSmall.1 →
        1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧
          Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
            (Err.cap 128 (uLT (ckP .two) [k9Round p]))) ∧
    (∀ (p : K9.Where) (st : List Fmt.Stored),
      ({ entry := K9.entry p, kind := .elems }, st) ∈ dryProofFull.1 ++ dryProofSmall.1 →
        p.work = 0) ∧
    (k9Runs dryProofRecsFull dryProofRunsFull0).length = 25 ∧
    (k9Runs dryProofRecsSmall dryProofRunsSmall0).length = 5 ∧
    (∀ r ∈ k9Runs dryProofRecsFull dryProofRunsFull0, K9RoundIn dryProofFull.1 r) ∧
    ∀ r ∈ k9Runs dryProofRecsSmall dryProofRunsSmall0, K9RoundIn dryProofSmall.1 r

theorem k09Condition : K09Condition := by
  refine ⟨at_written, no_work, ?_, ?_, ?_, ?_⟩
  · have h := congrArg List.length full_rows
    simpa using h
  · have h := congrArg List.length small_rows
    simpa using h
  · intro r hr
    exact ⟨k9Runs_mem hr, of_k9Ok r (List.all_eq_true.1 full_ok r hr)⟩
  · intro r hr
    exact ⟨k9Runs_mem hr, of_k9Ok r (List.all_eq_true.1 small_ok r hr)⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.full_recs
#print axioms VerifiableInference.Desc.K9L.small_recs
#print axioms VerifiableInference.Desc.K9L.at_written
#print axioms VerifiableInference.Desc.K9L.no_work
#print axioms VerifiableInference.Desc.K9L.full_idx
#print axioms VerifiableInference.Desc.K9L.small_idx
#print axioms VerifiableInference.Desc.K9L.full_rows
#print axioms VerifiableInference.Desc.K9L.small_rows
#print axioms VerifiableInference.Desc.K9L.full_ok
#print axioms VerifiableInference.Desc.K9L.small_ok
#print axioms VerifiableInference.Desc.K9L.k09Condition
