-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicOkReadsAt.lean: THE FINER FORM OF PublicOkReads.lean: THE
CODE SWITCH's PUBLIC TEST ON A FILLING (`K2.publicOk`, Honest/K2/Sim.lean) IS THE SAME AT ANY TWO
DATA THAT AGREE WHERE THE TEST WALKS: IN lays AT THE ADDRESSES OF THE OWN MESSAGES OF THE SEGMENTS
OF ITS LIST, AND IN lays AND `RowData.readyAt` AT NO CHALLENGE AT THE ADDRESSES OF THE SWITCH's OWN
MESSAGES. General: no filling, no plan, no book is named. Four theorems; no definition.

  `forIn_congr_mem`        two loops over one list, in `Except`, are one where their bodies agree at
                           the list's members
  `arraysLaid_of_lays_at`  D.lays a = D'.lays a ⊢ `K2.arraysLaid` at the address a is the same
  `ownLaid_of_lays_at`     hl, ho, hr ⊢ `K2.ownLaid` returns the same at D and D'
  `publicOk_of_lays_at`    the same of `K2.publicOk`, at D x and D' x'

The three premises. hl: at every seg below the list's length, every m and every a with p.addrs seg m
= some a: lays a is the same. ho: at every n below p.others.size - 1: lays (p.ownAddr n) is the
same. hr: at every such n: readyAt [] (p.ownAddr n) is the same (by `readyAt_nil`,
PublicOkReads.lean: heardAt ≤ 0 there, and ready [] there). The bound on n is the test's own: it
walks the switch's own sending but its last.

Why the finer form. `publicOk_of_lays` (PublicOkReads.lean) asks lays as a whole function. The field
addrs of a place speaks of the segments behind the list too: a filling whose lays hangs on the
instance at a message of such a segment does not meet that premise at two instances, and may meet
this one: the bound "seg below the list's length" is what lets it.

How. By `K2.ownLaid`'s text (Honest/K2/AtPlan.lean): its first loop walks the list with its numbers,
and asks `K2.arraysLaid` at the address that p.addrs gives for that number; its second walks the
switch's own sending.

Limits. ENOUGH, NOT NEEDED: hl asks at every m: the text walks the numbers of the segment's own
shapes; hl and ho ask lays a as a whole function of the row and the place: `K2.arraysLaid` reads it
at the rows below the shape's mainRows and the places below the code's ell; and the test stops at
its first refusal: what stands behind that is not read. That two given fillings agree so is proved
of no filling here. Nothing on whether the test says yes anywhere. All limits of K2/Sim.lean and
K2/AtPlan.lean hold.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Sim
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

/-- Two loops over one list, in `Except`, are one where their bodies agree at the list's members. -/
theorem forIn_congr_mem {ε α β : Type} (l : List α) (f g : α → β → Except ε (ForInStep β))
    (h : ∀ x ∈ l, ∀ b, f x b = g x b) : ∀ b : β, forIn l b f = forIn l b g := by
  induction l with
  | nil => intro b; rfl
  | cons a l ih =>
    intro b
    rw [List.forIn_cons, List.forIn_cons, h a List.mem_cons_self b]
    cases g a b with
    | error e => rfl
    | ok r =>
      cases r with
      | done b' => rfl
      | yield b' => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) b'

/-- The test on one message reads of a filling its field lays at that message's address alone.
CONDITIONAL: hl. -/
theorem arraysLaid_of_lays_at {D D' : RowData} {a : MsgAddr} (hl : D.lays a = D'.lays a)
    (lay : OnBytes.Params.ReqLayout) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (seg m : Nat) :
    K2.arraysLaid D lay codes s seg m a = K2.arraysLaid D' lay codes s seg m a := by
  unfold K2.arraysLaid
  rw [hl]

/-- **`K2.ownLaid` RETURNS THE SAME AT TWO DATA THAT AGREE WHERE IT WALKS.** CONDITIONAL: hl, ho,
hr. -/
theorem ownLaid_of_lays_at {D D' : RowData} (lay : OnBytes.Params.ReqLayout) (p : K2.SwitchPlace)
    (segs : List K2.SegmentPub)
    (hl : ∀ seg m a, seg < segs.length → p.addrs seg m = some a → D.lays a = D'.lays a)
    (ho : ∀ n, n < p.others.size - 1 → D.lays (p.ownAddr n) = D'.lays (p.ownAddr n))
    (hr : ∀ n, n < p.others.size - 1 →
      D.readyAt [] (p.ownAddr n) = D'.readyAt [] (p.ownAddr n)) :
    K2.ownLaid D lay p segs = K2.ownLaid D' lay p segs := by
  unfold K2.ownLaid
  congr 1
  · refine forIn_congr_mem _ _ _ (fun x hx b => ?_) _
    congr 1
    refine forIn_congr_mem _ _ _ (fun s _ b' => ?_) _
    have hx2 : x.2 < segs.length := by
      have := List.mem_zipIdx hx
      omega
    cases h : p.addrs x.2 s.2 with
    | none => rfl
    | some a => simp only [arraysLaid_of_lays_at (hl x.2 s.2 a hx2 h)]
  · funext _
    congr 1
    refine forIn_congr_mem _ _ _ (fun n hn b => ?_) _
    have hn2 : n.2 < p.others.size - 1 := by
      have h1 := List.mem_zipIdx hn
      have h2 : (p.others.toList.take (p.others.size - 1)).length ≤ p.others.size - 1 := by
        rw [List.length_take]
        exact Nat.min_le_left _ _
      omega
    simp only [arraysLaid_of_lays_at (ho n.2 hn2), hr n.2 hn2]

/-- **THE PUBLIC TEST IS THE SAME AT ANY TWO DATA THAT AGREE WHERE IT WALKS.** CONDITIONAL: hl, ho,
hr. -/
theorem publicOk_of_lays_at {Xi Xi' : Type} (D : RowDataOf Xi) (D' : RowDataOf Xi')
    (lay : OnBytes.Params.ReqLayout) (p : K2.SwitchPlace) (segs : List K2.SegmentPub) (x : Xi)
    (x' : Xi')
    (hl : ∀ seg m a, seg < segs.length → p.addrs seg m = some a →
      (D x).lays a = (D' x').lays a)
    (ho : ∀ n, n < p.others.size - 1 → (D x).lays (p.ownAddr n) = (D' x').lays (p.ownAddr n))
    (hr : ∀ n, n < p.others.size - 1 →
      (D x).readyAt [] (p.ownAddr n) = (D' x').readyAt [] (p.ownAddr n)) :
    K2.publicOk D lay p segs x = K2.publicOk D' lay p segs x' := by
  unfold K2.publicOk
  rw [ownLaid_of_lays_at lay p segs hl ho hr]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.forIn_congr_mem
#print axioms ProofFile.Honest.K5.arraysLaid_of_lays_at
#print axioms ProofFile.Honest.K5.ownLaid_of_lays_at
#print axioms ProofFile.Honest.K5.publicOk_of_lays_at
