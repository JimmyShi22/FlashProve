-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12MemberOfParts
import Johnson.Desc.K12.Law.StartOfMade
import Johnson.G.Runs
/-
H2K12/K12CutSplit.lean: FOR THE PROXIMITY TEST's
(the kind K12's) ROW AMONG THE ROWS THAT "the proof file's description returns, with its cut" WANTS
OF EACH LOT: WHAT H2U.placesOfMade ASKS OF THE FIRST CHAIN's LONG LIST OF ROUNDS, BROUGHT TO FORMS
THAT LEAN's KERNEL CAN EVALUATE WITHOUT A NUMBER THAT GROWS ALONG THE LIST (Johnson/G/Eager.lean
says why that matters). General laws; nothing is evaluated here; no value is named.
  foldl_add_sum    l.foldl (· + ·) a = a + l.sum: the tie between H2U.testCutAt's sum and
                   Johnson.G.sumE_eq's
  splitB           the test with code: what is left of es behind its first i members begins with an
                   entry named "BAT", and no entry behind that one bears the name. last_of_split:
                   then i is the last of H2U.batPlaces es. By H2K.Made.batPlaces_last
                   (Johnson/Desc/K12/Law/StartOfMade.lean) at es.take i ++ es.drop i
  cutAtP_of        cutAtP (H2K12/K12MemberOfParts.lean: H2U.testCutAt's text) returns where its one
                   test says no
  cutLAt_of_split  cutLAt's value, from four premises, by name: hP: the first of the planner's lists
                   is P; hb: splitB at i; hs: the eager sum (Johnson.G.sumE) of the roots of the
                   first i entries is s; hn: testCutAt's test on the names says no at i
  cutTestL_eq      H2U.cutTestL C = cutLAt C.proof C.sized.proof.request.last: by unfolding
  count_of_lit     how many rounds with q the plan of a written list L has (records and runs:
                   Johnson/G/RunsDefs.lean): one eager count along the runs (cntG,
                   Johnson/G/Runs.lean). By count_unrunG there, behind a map and two filters
  off_of_lit       the plan's entries less its rounds: the number of entries named "RECORD": one
                   eager count
TWO LISTS, NOT TO BE TAKEN FOR EACH OTHER: splitB, cutAtP_of and cutLAt_of_split speak of
P.rounds.map (·.entry): ALL entries of the planner's list; count_of_lit speaks of the plan's rounds:
these without "RECORD". A number on the one is no number on the other unless off_of_lit's count is
0.
WHAT IT IS NOT: no soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params H2U
open Johnson.G (sumE sumE_eq)
open Johnson.G.Runs (unrunG valRuns cntG count_unrunG)
open VerifiableInference.Number.ByRuns (Lit)

theorem foldl_add_sum (l : List Nat) : ∀ a, l.foldl (· + ·) a = a + l.sum := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    rw [List.foldl_cons, ih, List.sum_cons]
    omega

/-- Behind its first i members es begins with its last "BAT". -/
def splitB (es : List Fmt.Entry) (i : Nat) : Bool :=
  match es.drop i with
  | e :: rest => e.name == "BAT" && decide (H2K.Made.bats rest = 0)
  | [] => false

theorem last_of_split {es : List Fmt.Entry} {i : Nat} (h : splitB es i = true) :
    (batPlaces es).getLast? = some i := by
  unfold splitB at h
  cases hd : es.drop i with
  | nil =>
    rw [hd] at h
    cases h
  | cons e rest =>
    rw [hd] at h
    have h' : (e.name == "BAT" && decide (H2K.Made.bats rest = 0)) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    have hlt : i < es.length := Nat.lt_of_not_le fun hc => by
      rw [List.drop_eq_nil_of_le hc] at hd
      cases hd
    have hl : (es.take i).length = i := by
      rw [List.length_take]
      exact Nat.min_eq_left (Nat.le_of_lt hlt)
    have hs : es.take i ++ e :: rest = es := by
      rw [← hd]
      exact List.take_append_drop i es
    have hb := H2K.Made.batPlaces_last (es.take i) e rest h'.1 h'.2
    rw [hs, hl] at hb
    exact hb

theorem cutAtP_of {Pl : List Planned} {P : Planned} {st : List IoppStage} {i : Nat}
    (hP : Pl[0]? = some P)
    (hn : (decide (st.length < 2) ||
      (((P.rounds.map (·.entry)).drop i).take (1 + towerLen st)).map (·.name) !=
        "BAT" :: towerNames st) = false) :
    cutAtP Pl 0 i st = some ⟨0, i, ((P.rounds.map (·.entry)).drop i).take (1 + towerLen st),
      (((P.rounds.map (·.entry)).take i).map (·.roots)).foldl (· + ·) 0, st⟩ := by
  unfold cutAtP
  rw [hP]
  show (if (decide (st.length < 2) ||
      (((P.rounds.map (·.entry)).drop i).take (1 + towerLen st)).map (·.name) !=
        "BAT" :: towerNames st) = true then _ else _) = _
  rw [hn]
  rfl

/-- **cutLAt's value, without a number that grows along the list.** -/
theorem cutLAt_of_split {Pl : List Planned} {P : Planned} {st : List IoppStage} {i s : Nat}
    (hP : Pl[0]? = some P) (hb : splitB (P.rounds.map (·.entry)) i = true)
    (hs : sumE 0 (((P.rounds.map (·.entry)).take i).map (·.roots)) = s)
    (hn : (decide (st.length < 2) ||
      (((P.rounds.map (·.entry)).drop i).take (1 + towerLen st)).map (·.name) !=
        "BAT" :: towerNames st) = false) :
    cutLAt Pl st =
      some ⟨0, i, ((P.rounds.map (·.entry)).drop i).take (1 + towerLen st), s, st⟩ := by
  have hr : (((P.rounds.map (·.entry)).take i).map (·.roots)).foldl (· + ·) 0 = s := by
    rw [foldl_add_sum, ← sumE_eq, hs]
  unfold cutLAt
  rw [hP]
  show ((batPlaces (P.rounds.map (·.entry))).getLast?.bind fun j => cutAtP Pl 0 j st) = _
  rw [last_of_split hb]
  show cutAtP Pl 0 i st = _
  rw [cutAtP_of hP hn, hr]

theorem cutTestL_eq (C : Configured) :
    cutTestL C = cutLAt C.proof C.sized.proof.request.last := rfl

/-- **A count on a written list's plan's rounds: one eager count along the runs.** -/
theorem count_of_lit (L : Lit) (q : Fmt.Entry → Bool) :
    (L.plan.plan.rounds.filter q).length =
      cntG (fun r : PlanRound => q r.entry && (r.entry.name != Fmt.recordName)) 0
        (valRuns L.recs L.runs) := by
  rw [← count_unrunG]
  show (((((unrunG L.recs L.runs).map (·.entry)).filter fun r => r.name != Fmt.recordName).filter
    q).length) = _
  rw [List.filter_filter, List.filter_map, List.length_map]
  rfl

theorem length_sub_filter {α : Type} (p : α → Bool) (l : List α) :
    l.length - (l.filter p).length = (l.filter fun a => !p a).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hle : (l.filter p).length ≤ l.length := List.length_filter_le p l
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp]), List.length_cons,
        List.length_cons, ← ih]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos (by simp [hp]),
        List.length_cons, List.length_cons, ← ih]
      omega

/-- **The entries that are no rounds: one eager count.** -/
theorem off_of_lit (L : Lit) :
    L.plan.plan.entries.length - L.plan.plan.rounds.length =
      cntG (fun r : PlanRound => !(r.entry.name != Fmt.recordName)) 0
        (valRuns L.recs L.runs) := by
  rw [← count_unrunG]
  show ((unrunG L.recs L.runs).map (·.entry)).length -
    (((unrunG L.recs L.runs).map (·.entry)).filter fun r => r.name != Fmt.recordName).length = _
  rw [length_sub_filter, List.filter_map, List.length_map]
  rfl

end H2K12

#print axioms H2K12.foldl_add_sum
#print axioms H2K12.last_of_split
#print axioms H2K12.cutAtP_of
#print axioms H2K12.cutLAt_of_split
#print axioms H2K12.cutTestL_eq
#print axioms H2K12.count_of_lit
#print axioms H2K12.length_sub_filter
#print axioms H2K12.off_of_lit
