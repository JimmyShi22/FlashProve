-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RowIsPlan.lean: CONDITIONAL. THE ROW OF THE LAYERS' OWN
ROUNDS (kind K4; `k4RowIn`, Honest/K4/Part.lean) HAS AS MANY PARTS AS THE ROW INTO WHICH THE BOOK's
MAKER CUTS K4's SUB-PROTOCOL, AND PART FOR PART THE SAME STATED RUNS: WHAT OF THE FORM `K4RowIsPlan`
(Law/W/RowIsPlanForm.lean) FOLLOWS FROM K4's TABLE OF ROUNDS, AT EVERY PLAN WHOSE FOUR COUNTS ARE
NOT 0.

What is here. PUBLIC DATA ALONE: names of rounds, counts of scalars, addresses. Over
Law/W/PlanRow.lean, which writes the maker's parts out. Statements and proofs.

  `own_rounds`, `ends_rounds`, `ownScalars_masked`, `endScalars_masked`: a masked sumcheck's own
      scalars and end scalars, by the maker's count.
  `states_quiet`, `states_scal`, `states_sum`: what the maker lays (`partStates`,
      Honest/Small/SpentOfWants.lean) for a round that sends nothing; for a round "BAT-sigma" with c
      scalars, c not 0; for a masked sumcheck with e end values, e not 0.
  `sum_states`, `seen_states`: K4's two sorts of sumcheck state just that.
  `k4Tail_states`, `k4Row_states_list`, `k4_row_states`: **the field states**: part for part,
      K4's part states the names and counts that the maker lays.
  `k4_rowIsPlan`: **the form's ten fields.**
  Small tools: `laidAt`, `fst_of_zipIdx_replicate`, `k4Units_eq`, `k4RowIn_len`, `merges_of`.

Not shown here. THE EDGE: WHERE ONE OF FOUR PUBLIC COUNTS OF THE PLAN IS 0 (`K4Counts`: the two
long lists of scalars; the end values of the two sumchecks over the tokens) THE MAKER LAYS NO ENTRY
FOR THAT COUNT, AND K4's PART STATES A RUN OF COUNT 0 ALL THE SAME: THE TWO LISTS THEN HAVE OTHER
LENGTHS, AND UNDER hpl AND hr THE FIELD states IS FALSE [by reading of the two texts; NO THEOREM
HERE SHOWS IT]. SO hpos IS A HYPOTHESIS OF BOTH TOPS. `k4TableFits` does not give it: it compares
sums of counts; Law/W/CountsOfLayout.lean has it at every layout that the verifier's own function
returns, where K4 covers the plan. The seven fields that call no count can be had from
`k4_rowIsPlan` alone, so under all five hypotheses. hfront AND hmerge ARE HYPOTHESES ON THE LETTER
M, the maker's list of merges: that of K4's addresses it holds the last part's alone.
Law/W/MergesByName.lean shows both at `mergesByName` (Honest/BookWhole.lean), the list that `onlineProverFromPublicFiles`
(Honest/AtPure.lean) hands the book's maker; nothing compares a list with the format. hpl and hr,
that the sub-protocol stands at K4's place and declares the entries of K4's table:
Law/MemberAt.lean's `k4_member_rounds` has hr AT THE FULL SIZE ALONE, under eight hypotheses, of
which the place is one; Law/W/LockAtMember.lean's `k4_member_there` has both, in the goals' scope.
THE ROUNDS OF A PART ARE NOT COMPARED HERE: Law/W/CutIsOurs.lean. Nothing on a book, on coins, or on
what a part sends. What stands in front of K4's row in its segment is not spoken of. No example of
the five hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanRow
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlanForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (entries k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Part.MaskedSum (Call Ends)

variable {S Cl : Type}

/-! ## 1 The maker's counts at a unit -/

/-- The rounds "PSC round" add two own scalars each. -/
theorem own_rounds : ∀ (k n : Nat),
    (List.replicate k ("PSC round", 2)).foldl
      (fun (n : Nat) (r : String × Nat) => if frameNames.contains r.1 then n else n + r.2) n =
      n + 2 * k
  | 0, _ => rfl
  | k + 1, n => by
    rw [List.replicate_succ, List.foldl_cons]
    have e : (if frameNames.contains ("PSC round", 2).1 then n else n + ("PSC round", 2).2) =
        n + 2 := if_neg (by decide)
    rw [e, own_rounds k]
    omega

/-- They add no end scalar. -/
theorem ends_rounds : ∀ (k n : Nat),
    (List.replicate k ("PSC round", 2)).foldl
      (fun (n : Nat) (r : String × Nat) => if r.1 == "PSC values" then n + r.2 else n) n = n
  | 0, _ => rfl
  | k + 1, n => by
    rw [List.replicate_succ, List.foldl_cons]
    have e : (if ("PSC round", 2).1 == "PSC values" then n + ("PSC round", 2).2 else n) = n :=
      if_neg (by decide)
    rw [e]
    exact ends_rounds k n

theorem ownScalars_masked (a : Addr) (k f y e : Nat) :
    (⟨a, maskedP k f y e⟩ : PartAt).ownScalars = f + 2 * k + y + e := by
  show (("PSC epsilon", f) :: (List.replicate k ("PSC round", 2) ++
    [("PSC Y", y), ("PSC values", e)])).foldl
      (fun (n : Nat) (r : String × Nat) => if frameNames.contains r.1 then n else n + r.2) 0 = _
  rw [List.foldl_cons, List.foldl_append]
  have e0 : (if frameNames.contains ("PSC epsilon", f).1 then 0 else 0 + ("PSC epsilon", f).2) =
      f := by
    show (if frameNames.contains "PSC epsilon" then 0 else 0 + f) = f
    rw [if_neg (by decide)]
    omega
  rw [e0, own_rounds]
  show (if frameNames.contains "PSC values" then
      (if frameNames.contains "PSC Y" then f + 2 * k else f + 2 * k + y)
    else (if frameNames.contains "PSC Y" then f + 2 * k else f + 2 * k + y) + e) = _
  rw [if_neg (by decide), if_neg (by decide)]

theorem endScalars_masked (a : Addr) (k f y e : Nat) :
    (⟨a, maskedP k f y e⟩ : PartAt).endScalars = e := by
  show (("PSC epsilon", f) :: (List.replicate k ("PSC round", 2) ++
    [("PSC Y", y), ("PSC values", e)])).foldl
      (fun (n : Nat) (r : String × Nat) => if r.1 == "PSC values" then n + r.2 else n) 0 = _
  rw [List.foldl_cons, List.foldl_append]
  have e0 : (if ("PSC epsilon", f).1 == "PSC values" then 0 + ("PSC epsilon", f).2 else 0) = 0 := by
    show (if "PSC epsilon" == "PSC values" then 0 + f else 0) = 0
    rw [if_neg (by decide)]
  rw [e0, ends_rounds]
  show (if "PSC values" == "PSC values" then
    (if "PSC Y" == "PSC values" then 0 + y else 0) + e
      else (if "PSC Y" == "PSC values" then 0 + y else 0)) = e
  rw [if_pos (by decide), if_neg (by decide)]
  omega

/-! ## 2 What the maker lays for a unit -/

/-- For a round that sends nothing: nothing. -/
theorem states_quiet (r i : String) (mg : Bool) (a : Addr) (n : String) :
    partStates r i mg ⟨a, [(n, 0)]⟩ = [] := by
  have h : (⟨a, [(n, 0)]⟩ : PartAt).ownScalars = 0 := by
    show (if frameNames.contains n then 0 else 0 + 0) = 0
    split <;> rfl
  unfold partStates
  simp only [h, beq_self_eq_true, if_true]

/-- CONDITIONAL: on hc. For a round "BAT-sigma" with c scalars: one run "scalars" of c. -/
theorem states_scal (r i : String) (mg : Bool) (a : Addr) {c : Nat} (hc : c ≠ 0) :
    partStates r i mg ⟨a, [("BAT-sigma", c)]⟩ = [(runName r a "scalars", ⟨0, c⟩)] := by
  have h : (⟨a, [("BAT-sigma", c)]⟩ : PartAt).ownScalars = c := by
    show (if frameNames.contains "BAT-sigma" then 0 else 0 + c) = c
    rw [if_neg (by decide)]
    omega
  have hs : (⟨a, [("BAT-sigma", c)]⟩ : PartAt).isSum = false := by
    show ((some "BAT-sigma" : Option String) == some "PSC epsilon") = false
    decide
  have h0 : (c == 0) = false := beq_false_of_ne hc
  unfold partStates
  simp only [h, hs, h0, Bool.not_false, if_true, Bool.false_eq_true, if_false]

/-- CONDITIONAL: on he. For a masked sumcheck with e end values: a run "sum" and a run "ends". -/
theorem states_sum (r i : String) (mg : Bool) (a : Addr) (k f y : Nat) {e : Nat} (he : e ≠ 0) :
    partStates r i mg ⟨a, maskedP k f y e⟩ =
      [(runName r a "sum", ⟨0, f + 2 * k + y⟩),
        (runName (if mg then i else r) a "ends", ⟨0, e⟩)] := by
  have hs : (⟨a, maskedP k f y e⟩ : PartAt).isSum = true := by
    show ((some "PSC epsilon" : Option String) == some "PSC epsilon") = true
    decide
  have h0 : (f + 2 * k + y + e == 0) = false := beq_false_of_ne (by omega)
  have h1 : (e == 0) = false := beq_false_of_ne he
  have h2 : f + 2 * k + y + e - e = f + 2 * k + y := by omega
  unfold partStates
  simp only [ownScalars_masked, endScalars_masked, hs, h0, h1, h2, Bool.not_true,
    Bool.false_eq_true, if_false]

/-! ## 3 What K4's parts state -/

/-- CONDITIONAL: on he, hown, hne, hmg. K4's sumcheck states what the maker lays. -/
theorem sum_states (Q : K4Pub) (sh : Call) (e : Ends) (he : sh.ends = some e) (owner : String)
    (job : K4Pub → K4In → Pts → Option Job) (i k f y : Nat) (hown : ownRun sh = f + 2 * k + y)
    (hne : e.n ≠ 0) (mg : Bool) (hmg : (if mg then indexMaskRun else maskRowRun) = owner) :
    (k4Sum Q sh owner job i).spends =
      partStates maskRowRun indexMaskRun mg ⟨k4Addr Q i, maskedP k f y e.n⟩ := by
  rw [states_sum _ _ _ _ _ _ _ hne, hmg, ← hown]
  show ((runName maskRowRun (k4Addr Q i) "sum", (⟨0, ownRun sh⟩ : Due)) ::
    endRuns (runName owner (k4Addr Q i) "ends") sh.ends) = _
  rw [he]
  rfl

/-- CONDITIONAL: on he, hown, hne, hmg. The like for the sumcheck that reads what was shown. -/
theorem seen_states (Q : K4Pub) (sh : Call) (e : Ends) (he : sh.ends = some e)
    (job : K4Pub → K4In → Pts → Array OnBytes.E → Option Job) (i k f y : Nat)
    (hown : ownRun sh = f + 2 * k + y) (hne : e.n ≠ 0) (mg : Bool) (hmg : mg = false) :
    (k4SumSeen Q sh job i).spends =
      partStates maskRowRun indexMaskRun mg ⟨k4Addr Q i, maskedP k f y e.n⟩ := by
  rw [states_sum _ _ _ _ _ _ _ hne, hmg, ← hown]
  show ((runName maskRowRun (k4Addr Q i) "sum", (⟨0, ownRun sh⟩ : Due)) ::
    endRuns (runName maskRowRun (k4Addr Q i) "ends") sh.ends) = _
  rw [he]
  rfl

variable {M : Merges} {Q : K4Pub}

/-- What the maker lays for the part at an address with these rounds. -/
abbrev laidAt (M : Merges) (Q : K4Pub) (x : List (String × Nat) × Nat) : List (String × Due) :=
  partStates maskRowRun indexMaskRun (M.ends.contains (k4Addr Q x.2)) ⟨k4Addr Q x.2, x.1⟩

/-- CONDITIONAL: on hpos, hf, hm. **The sixteen parts behind the points in front.** -/
theorem k4Tail_states (hpos : K4Counts Q)
    (hf : ∀ j, j < 15 → M.ends.contains (k4Addr Q (k0 Q.g + j)) = false)
    (hm : M.ends.contains (k4Addr Q (k0 Q.g + 15)) = true) :
    (k4Tail Q).map (·.spends) = ((k4TailUnits Q).zipIdx (k0 Q.g)).map (laidAt M Q) := by
  obtain ⟨p1, p2, p3, p4⟩ := hpos
  have row : ∀ j, j < 15 →
      (if M.ends.contains (k4Addr Q (k0 Q.g + j)) then indexMaskRun else maskRowRun) =
        maskRowRun := fun j hj => by rw [hf j hj]; rfl
  have q : ∀ (j : Nat) (n : String), (k4Quiet : Part Unit K4In Unit).spends =
      laidAt M Q ([(n, 0)], k0 Q.g + j) := fun j n => (states_quiet _ _ _ _ n).symm
  have e0 : (k4Scalars Q (ledNS Q.P.y.h.xl * Q.P.y.NI) wSums (k0 Q.g)).spends =
      laidAt M Q ([("BAT-sigma", ledNS Q.P.y.h.xl * Q.P.y.NI)], k0 Q.g) :=
    (states_scal _ _ _ _ p1).symm
  have e2 := sum_states Q (k4LevelShape Q.P.rd.muV) ⟨2, 2⟩ rfl maskRowRun jobSquares (k0 Q.g + 2)
    Q.P.rd.muV 1 2 (by rw [ownRun_level]; omega) (by decide) _ (row 2 (by omega))
  have e4 : (k4Scalars Q (ledNP Q.P.y.h.xl * Q.P.y.NI) rowProducts (k0 Q.g + 4)).spends =
      laidAt M Q ([("BAT-sigma", ledNP Q.P.y.h.xl * Q.P.y.NI)], k0 Q.g + 4) :=
    (states_scal _ _ _ _ p2).symm
  have e5 := sum_states Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) ⟨2, _⟩ rfl
    maskRowRun jobRows (k0 Q.g + 5) Q.P.y.h.lt 2 2 (by rw [ownRun_token]; omega) p3 _
    (row 5 (by omega))
  have e6 := sum_states Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) ⟨1, _⟩ rfl maskRowRun jobTerms
    (k0 Q.g + 6) Q.P.y.h.lt 2 1 (by rw [ownRun_token]; omega) p4 _ (row 6 (by omega))
  have e8 := seen_states Q (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) ⟨2, _⟩ rfl jobStack
    (k0 Q.g + 8) Q.hp.lamS 1 2 (by rw [(ownRun_shapes 0 0 Q.hp.lamS 2 _).2.2]; unfold ownOf; omega)
    (by show nStack Q.P Q.hp Q.g ≠ 0; unfold nStack; omega) _ (hf 8 (by omega))
  have e9 := sum_states Q (k4LevelShape Q.P.rd.muH) ⟨2, 2⟩ rfl maskRowRun jobGated (k0 Q.g + 9)
    Q.P.rd.muH 1 2 (by rw [ownRun_level]; omega) (by decide) _ (row 9 (by omega))
  have e12 := sum_states Q (k4LevelShape Q.P.rd.muH2) ⟨2, 2⟩ rfl maskRowRun jobGated2 (k0 Q.g + 12)
    Q.P.rd.muH2 1 2 (by rw [ownRun_level]; omega) (by decide) _ (row 12 (by omega))
  have e14 : (if Q.g == 0 then k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)
      else k4Quiet).spends =
      laidAt M Q ([("BAT-sigma", if Q.g == 0 then 1 else 0)], k0 Q.g + 14) := by
    cases hg : (Q.g == 0)
    · exact (states_quiet _ _ _ _ _).symm
    · exact (states_scal _ _ _ _ (by decide)).symm
  have e15 := sum_states Q (k4PlainShape Q.P.wsLay.lk 1 1) ⟨1, 1⟩ rfl indexMaskRun jobMerge
    (k0 Q.g + 15) Q.P.wsLay.lk 1 1
    (by rw [(ownRun_shapes 0 0 Q.P.wsLay.lk 1 1).2.2]; unfold ownOf; omega) (by decide)
    (M.ends.contains (k4Addr Q (k0 Q.g + 15))) (by rw [hm]; rfl)
  exact congrArg₂ List.cons e0 <| congrArg₂ List.cons (q 1 "JOIN") <| congrArg₂ List.cons e2 <|
    congrArg₂ List.cons (q 3 "LINE") <| congrArg₂ List.cons e4 <| congrArg₂ List.cons e5 <|
    congrArg₂ List.cons e6 <| congrArg₂ List.cons (q 7 "BAT-sigma") <| congrArg₂ List.cons e8 <|
    congrArg₂ List.cons e9 <| congrArg₂ List.cons (q 10 "LINE") <|
    congrArg₂ List.cons (q 11 "JOIN") <| congrArg₂ List.cons e12 <|
    congrArg₂ List.cons (q 13 "LINE") <| congrArg₂ List.cons e14 <| congrArg₂ List.cons e15 rfl

/-- Each member of a list of one thing again and again, numbered, holds that thing. -/
theorem fst_of_zipIdx_replicate {α : Type} (a : α) : ∀ (n k : Nat) (x : α × Nat),
    x ∈ (List.replicate n a).zipIdx k → x.1 = a
  | 0, _, _, h => by simp at h
  | n + 1, k, x, h => by
    rw [List.replicate_succ, List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact fst_of_zipIdx_replicate a n (k + 1) x h

/-- The points in front, as a list of one unit again and again. -/
theorem k4Units_eq (Q : K4Pub) :
    k4Units Q = List.replicate (k0 Q.g) [("ZERO", 0)] ++ k4TailUnits Q := by
  unfold k4Units
  rcases k0_cases Q.g with ⟨hg, hk⟩ | ⟨hg, hk⟩
  · rw [hk, if_pos hg]
    rfl
  · rw [hk, if_neg (by rw [hg]; exact Bool.false_ne_true)]
    rfl

/-- CONDITIONAL: on hpos, hf, hm. **The whole row, as two lists.** -/
theorem k4Row_states_list (hpos : K4Counts Q)
    (hf : ∀ j, j < 15 → M.ends.contains (k4Addr Q (k0 Q.g + j)) = false)
    (hm : M.ends.contains (k4Addr Q (k0 Q.g + 15)) = true) :
    (k4RowIn Q).map (·.spends) = (k4Units Q).zipIdx.map (laidAt M Q) := by
  have hT : k4RowIn Q = List.replicate (k0 Q.g) k4Quiet ++ k4Tail Q := k4RowIn_all Q
  rw [hT, k4Units_eq, List.zipIdx_append, List.map_append, List.map_append, List.length_replicate,
    Nat.zero_add, k4Tail_states hpos hf hm]
  congr 1
  rw [List.map_replicate]
  refine (List.eq_replicate_iff.2 ⟨by simp, fun s hs => ?_⟩).symm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  have hx1 : x.1 = [("ZERO", 0)] := fst_of_zipIdx_replicate _ _ _ _ hx
  show partStates maskRowRun indexMaskRun _ ⟨k4Addr Q x.2, x.1⟩ = _
  rw [hx1]
  exact states_quiet _ _ _ _ _

variable {b : Block S Cl}

theorem k4RowIn_len (Q : K4Pub) : (k4RowIn Q).length = k0 Q.g + 16 := by
  rw [k4RowIn_all, List.length_append, List.length_replicate]
  rfl

/-- hfront and hmerge, as the tests that the maker makes. -/
theorem merges_of (hfront : ∀ i, i + 1 < (k4RowIn Q).length → k4Addr Q i ∉ M.ends)
    (hmerge : k4Addr Q ((k4RowIn Q).length - 1) ∈ M.ends) :
    (∀ j, j < 15 → M.ends.contains (k4Addr Q (k0 Q.g + j)) = false) ∧
      M.ends.contains (k4Addr Q (k0 Q.g + 15)) = true := by
  rw [k4RowIn_len] at hmerge
  refine ⟨fun j hj => ?_, ?_⟩
  · have h := hfront (k0 Q.g + j) (by rw [k4RowIn_len]; omega)
    cases hc : M.ends.contains (k4Addr Q (k0 Q.g + j))
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) h
  · exact List.contains_iff_mem.2 hmerge

/-- CONDITIONAL: on all five hypotheses. **THE FIELD states: PART FOR PART, K4's PART STATES THE
NAMES AND COUNTS THAT THE MAKER LAYS FOR THE PLAN's PART.** -/
theorem k4_row_states (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound))
    (hpos : K4Counts Q)
    (hfront : ∀ i, i + 1 < (k4RowIn Q).length → k4Addr Q i ∉ M.ends)
    (hmerge : k4Addr Q ((k4RowIn Q).length - 1) ∈ M.ends) :
    ∀ (i : Nat) (q : PartAt) (P : Part Unit K4In Unit),
      (planParts b)[i]? = some q → (k4RowIn Q)[i]? = some P →
        P.spends = partStates maskRowRun indexMaskRun (M.ends.contains q.addr) q := by
  intro i q P hq hP
  obtain ⟨hf, hm⟩ := merges_of hfront hmerge
  have hL := congrArg (·[i]?) (k4Row_states_list hpos hf hm)
  simp only [List.getElem?_map, hP, Option.map_some] at hL
  rw [k4_planParts hpl hr] at hq
  unfold k4PlanRow at hq
  rw [List.getElem?_map] at hq
  cases hx : (k4Units Q).zipIdx[i]? with
  | none =>
    rw [hx] at hq
    cases hq
  | some x =>
    rw [hx] at hq hL
    obtain rfl : (⟨k4Addr Q x.2, x.1⟩ : PartAt) = q := Option.some.inj hq
    exact Option.some.inj hL

/-- CONDITIONAL: on all five hypotheses. **K4's ROW IS THE MAKER's ROW, PART FOR PART: THE FORM's
TEN FIELDS.** -/
theorem k4_rowIsPlan (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound))
    (hpos : K4Counts Q)
    (hfront : ∀ i, i + 1 < (k4RowIn Q).length → k4Addr Q i ∉ M.ends)
    (hmerge : k4Addr Q ((k4RowIn Q).length - 1) ∈ M.ends) :
    ∃ A m, K4RowIsPlan M b Q A m ∧ m.addr = k4Addr Q ((k4RowIn Q).length - 1) := by
  have hP := k4_planParts hpl hr
  have hlenU : (k4Units Q).length = k0 Q.g + 16 := by
    rw [k4Units_eq, List.length_append, List.length_replicate]
    rfl
  have hsplit : k4Units Q = (k4Units Q).dropLast ++ [maskedP Q.P.wsLay.lk 1 1 1] := by
    rw [k4Units_eq]
    unfold k4TailUnits
    simp
  have hdl : (k4Units Q).dropLast.length = k0 Q.g + 15 := by
    rw [List.length_dropLast, hlenU]
    rfl
  have hrow : k4PlanRow Q =
      ((k4Units Q).dropLast.zipIdx.map fun x => (⟨k4Addr Q x.2, x.1⟩ : PartAt)) ++
        [⟨k4Addr Q (k0 Q.g + 15), maskedP Q.P.wsLay.lk 1 1 1⟩] := by
    unfold k4PlanRow
    conv_lhs => rw [hsplit]
    rw [List.zipIdx_append, List.map_append, hdl, Nat.zero_add]
    rfl
  have hlast : (k4RowIn Q).length - 1 = k0 Q.g + 15 := by
    rw [k4RowIn_len]
    rfl
  refine ⟨_, _, ⟨hpl, ?_, hP.trans hrow, ?_, ?_, ?_, ?_, ?_, ?_,
    k4_row_states hpl hr hpos hfront hmerge⟩, hlast.symm ▸ rfl⟩
  · rw [hP, k4RowIn_len]
    unfold k4PlanRow
    rw [List.length_map, List.length_zipIdx, hlenU]
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    have hlt : x.2 < k0 Q.g + 15 := by
      have := List.snd_lt_of_mem_zipIdx hx
      rw [hdl] at this
      omega
    exact hfront x.2 (by rw [k4RowIn_len]; omega)
  · rw [hlast] at hmerge
    exact hmerge
  · show ((some "PSC epsilon" : Option String) == some "PSC epsilon") = true
    decide
  · exact endScalars_masked _ _ _ _ _
  · rw [ownScalars_masked, endScalars_masked]
    omega
  · intro r hrm
    rw [hr] at hrm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hrm
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
    show d.name.name ≠ "FOLD epsilon"
    cases d.name <;> decide

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.own_rounds
#print axioms ProofFile.Honest.K4.W.ends_rounds
#print axioms ProofFile.Honest.K4.W.ownScalars_masked
#print axioms ProofFile.Honest.K4.W.endScalars_masked
#print axioms ProofFile.Honest.K4.W.states_quiet
#print axioms ProofFile.Honest.K4.W.states_scal
#print axioms ProofFile.Honest.K4.W.states_sum
#print axioms ProofFile.Honest.K4.W.sum_states
#print axioms ProofFile.Honest.K4.W.seen_states
#print axioms ProofFile.Honest.K4.W.k4Tail_states
#print axioms ProofFile.Honest.K4.W.fst_of_zipIdx_replicate
#print axioms ProofFile.Honest.K4.W.k4Units_eq
#print axioms ProofFile.Honest.K4.W.k4Row_states_list
#print axioms ProofFile.Honest.K4.W.k4RowIn_len
#print axioms ProofFile.Honest.K4.W.merges_of
#print axioms ProofFile.Honest.K4.W.k4_row_states
#print axioms ProofFile.Honest.K4.W.k4_rowIsPlan
