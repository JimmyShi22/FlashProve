-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/AddLight.lean: the adding of a list of claims on shapes (addListS,
Johnson/Desc/First/Batch/Shape/AddShape.lean) written a second time, so that the list of marks
"this claim's weight has been handed out" is walked a few times for the whole list of claims, not
thrice for each claim, and a law that the two texts are the same function.

Why. addListS adds claim by claim. For each claim it asks the length of the list of marks, reads the
mark at the claim's number and writes it: three walks from the list's head. At a plan of n claims
that is of the order of n * n steps. The second text asks the length once, drops the marks in front
of the first claim's number once, goes down the rest of the marks and the claims side by side, and
lays the marks in front back on (laidL).

  claimB: a claim's three tests (its entries, its slots, its runs). They read the ledger's arrays
    and its number of slots, which the adding does not turn.
  goL: down the marks and the claims side by side: each mark must be unset and is set.
  openB: what is asked of the ledger once: the door is open, the batching element is drawn, there
    are as many marks as the plan has claims.
  laidL: the ledger behind the adding.
  addListL: the second text.
  **addListS_eq : addListS L cs = addListL L cs**, at every ledger's shape and every list: no
    premise.

Limits. General laws on shapes. Nothing is evaluated here, and what either text costs Lean's kernel
is not said here. openB here is another thing than First.Shape.openB (a sumcheck's) and
Walk.Shape.openB (a link's "opened"). nextB_nil's premise on openB is idle. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.AddShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape

/-! ## 1 The second text -/

/-- A claim's three tests, as addOneS asks them. -/
def claimB (trees : List TreeSh) (ns : Nat) (c : ClaimSh) : Bool :=
  c.form.ents.all (entryS trees) && c.form.slots.all (fun j => decide (j < ns)) &&
    c.runs.all (runS trees)

/-- Down the marks and the claims side by side: each claim meets an unset mark, which is set, and
passes its three tests. What is returned: the marks, those met set. -/
def goL (trees : List TreeSh) (ns : Nat) : List Bool → List ClaimSh → Option (List Bool)
  | w, [] => some w
  | [], _ :: _ => none
  | b :: w, c :: cs =>
    if !b && claimB trees ns c then (goL trees ns w cs).map (true :: ·) else none

/-- At no claim the marks come back as they are. (By cases on the marks: goL looks at them
first.) -/
theorem goL_nil (trees : List TreeSh) (ns : Nat) (w : List Bool) : goL trees ns w [] = some w := by
  cases w <;> rfl

/-- What is asked of the ledger once: three of nextB's five tests. The other two are asked claim by
claim in goL: "the claim's number lies below the plan's number of claims" is goL's second line (no
mark is left), given that there are as many marks as the plan has claims; "the mark is unset" is the
`!b` in its third. -/
def openB (L : LedSh) : Bool := !L.shut && L.drawn && L.handed.length == L.planClaims

/-- The ledger with n claims more counted; w: the marks from the first of these claims on. -/
def laidL (L : LedSh) (n : Nat) (w : List Bool) : LedSh :=
  LedSh.mk L.ns L.shown L.factors L.got L.owed L.planClaims L.trees L.next L.coefs (L.claims + n)
    L.drawn (L.handed.take L.claims ++ w) L.shut

/-- **The adding of a list of claims on shapes, the marks walked a few times in all.** -/
def addListL (L : LedSh) : List ClaimSh → Option LedSh
  | [] => some L
  | c :: cs =>
    if openB L then
      (goL L.trees L.ns (L.handed.drop L.claims) (c :: cs)).map (laidL L (cs.length + 1))
    else none

/-! ## 2 The marks from a number on -/

/-- No mark is left from k on: k is no place of the list. -/
theorem win_nil : ∀ (h : List Bool) (k : Nat), h.drop k = [] → ¬ k < h.length
  | [], _, _ => by simp
  | _ :: _, 0, e => by simp at e
  | _ :: h, k + 1, e => by
    have := win_nil h k (by simpa using e)
    simp only [List.length_cons]
    omega

/-- A mark b stands at k, and w behind it: k is a place of the list; the read at k gives b; behind
the write at k the marks from k + 1 on are w, and those up to k are the old ones and `true`. -/
theorem win_cons : ∀ (h : List Bool) (k : Nat) (b : Bool) (w : List Bool), h.drop k = b :: w →
    k < h.length ∧ h.getD k true = b ∧ (h.set k true).drop (k + 1) = w ∧
      (h.set k true).take (k + 1) = h.take k ++ [true]
  | [], _, _, _, e => by simp at e
  | _ :: _, 0, _, _, e => by
    simp only [List.drop_zero, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp
  | x :: h, k + 1, b, w, e => by
    obtain ⟨h1, h2, h3, h4⟩ := win_cons h k b w (by simpa using e)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simpa using h2
    · simpa using h3
    · simpa using h4

/-! ## 3 One claim -/

/-- addOneS with its last three tests gathered in claimB. -/
theorem addOneS_eq (L : LedSh) (c : ClaimSh) :
    addOneS L c = if nextB L && claimB L.trees L.ns c then some (nextS L) else none := by
  unfold addOneS claimB
  simp only [Bool.and_assoc]

/-- Where openB fails, nextB fails. -/
theorem nextB_shut {L : LedSh} (h : ¬ openB L = true) : nextB L = false := by
  revert h
  unfold openB nextB
  generalize (!L.shut) = a
  generalize L.drawn = b
  generalize (L.handed.length == L.planClaims) = c
  cases a <;> cases b <;> cases c <;> simp

/-- Under openB, with no mark left from the claim's number on, nextB fails. -/
theorem nextB_nil {L : LedSh} (hw : L.handed.drop L.claims = []) (ho : openB L = true) :
    nextB L = false := by
  have h1 := win_nil _ _ hw
  unfold openB at ho
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨-, l⟩ := ho
  unfold nextB
  rw [← l]
  simp [h1]

/-- Under openB, with the mark b at the claim's number, nextB says: b is unset. -/
theorem nextB_cons {L : LedSh} {b : Bool} {w : List Bool} (hw : L.handed.drop L.claims = b :: w)
    (ho : openB L = true) : nextB L = !b := by
  obtain ⟨h1, h2, -, -⟩ := win_cons _ _ _ _ hw
  unfold openB at ho
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨⟨s, d⟩, l⟩ := ho
  unfold nextB
  rw [s, d, h2, ← l]
  simp [h1]

/-- openB stays behind a claim's adding: the write of a mark keeps the list's length, and nextS
turns neither the door, nor the draw, nor the plan's number of claims. -/
theorem open_next {L : LedSh} (ho : openB L = true) : openB (nextS L) = true := by
  have e : (L.handed.set L.claims true).length = L.handed.length := by simp
  unfold openB at ho ⊢
  show (!L.shut && L.drawn && (L.handed.set L.claims true).length == L.planClaims) = true
  rw [e]
  exact ho

/-! ## 4 The law -/

/-- Under openB the first text is the walk down the marks and the claims side by side. -/
theorem addListS_open : ∀ (cs : List ClaimSh) (L : LedSh), openB L = true →
    addListS L cs = (goL L.trees L.ns (L.handed.drop L.claims) cs).map (laidL L cs.length)
  | [], L, _ => by
    rw [goL_nil]
    show some L = some (laidL L 0 (L.handed.drop L.claims))
    unfold laidL
    rw [List.take_append_drop]
    rfl
  | c :: cs, L, ho => by
    show (addOneS L c).bind (fun L' => addListS L' cs) = _
    rw [addOneS_eq]
    cases hw : L.handed.drop L.claims with
    | nil =>
      rw [nextB_nil hw ho]
      rfl
    | cons b w =>
      rw [nextB_cons hw ho]
      show _ = (if !b && claimB L.trees L.ns c then (goL L.trees L.ns w cs).map (true :: ·)
        else none).map _
      by_cases hb : (!b && claimB L.trees L.ns c) = true
      · rw [if_pos hb, if_pos hb]
        show addListS (nextS L) cs = _
        rw [addListS_open cs (nextS L) (open_next ho)]
        obtain ⟨-, -, h3, h4⟩ := win_cons _ _ _ _ hw
        have e1 : (nextS L).handed.drop (nextS L).claims = w := h3
        rw [e1, Option.map_map]
        show (goL L.trees L.ns w cs).map (laidL (nextS L) cs.length) = _
        congr 1
        funext w'
        have a1 : L.claims + 1 + cs.length = L.claims + (cs.length + 1) := by omega
        have a2 : (L.handed.set L.claims true).take (L.claims + 1) ++ w' =
            L.handed.take L.claims ++ true :: w' := by
          rw [h4]
          simp
        show LedSh.mk L.ns L.shown L.factors L.got L.owed L.planClaims L.trees L.next L.coefs
          (L.claims + 1 + cs.length) L.drawn
          ((L.handed.set L.claims true).take (L.claims + 1) ++ w') L.shut = _
        rw [a1, a2]
        rfl
      · rw [if_neg hb, if_neg hb]
        rfl

/-- **The two texts are one function.** -/
theorem addListS_eq (L : LedSh) (cs : List ClaimSh) : addListS L cs = addListL L cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    show _ = if openB L then _ else none
    by_cases ho : openB L = true
    · rw [if_pos ho, addListS_open _ _ ho]
      rfl
    · rw [if_neg ho]
      show (addOneS L c).bind _ = none
      rw [addOneS_eq, nextB_shut ho]
      rfl

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.goL_nil
#print axioms VerifiableInference.Desc.K9.Shape.win_nil
#print axioms VerifiableInference.Desc.K9.Shape.win_cons
#print axioms VerifiableInference.Desc.K9.Shape.addOneS_eq
#print axioms VerifiableInference.Desc.K9.Shape.nextB_shut
#print axioms VerifiableInference.Desc.K9.Shape.nextB_nil
#print axioms VerifiableInference.Desc.K9.Shape.nextB_cons
#print axioms VerifiableInference.Desc.K9.Shape.open_next
#print axioms VerifiableInference.Desc.K9.Shape.addListS_open
#print axioms VerifiableInference.Desc.K9.Shape.addListS_eq
#print axioms VerifiableInference.Desc.K9.Shape.claimB
#print axioms VerifiableInference.Desc.K9.Shape.goL
#print axioms VerifiableInference.Desc.K9.Shape.openB
#print axioms VerifiableInference.Desc.K9.Shape.laidL
#print axioms VerifiableInference.Desc.K9.Shape.addListL
