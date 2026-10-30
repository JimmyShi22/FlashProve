-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05BehindLay3.lean: kind K5: WHAT HOLDS OF THE RECORD BEHIND THE HEARING's
LAY, for the three clauses that the table of joints' promise (Johnson/Desc/First/Borders.lean)
has beside those of Johnson/Desc/First/Att/K05BehindLay.lean: "every slot from the
next free number on is free"; "nothing is heard at the digits' seat, and the link's table of arrays
is the plan's"; and the caller's condition in front with the room taken out of it.

Main names:
  `freeFromB`: a Bool on the record: every slot from the open ledger's next free number on, up to
    its number of slots, is free.
  `freeAboveB nsPlan`: a Bool, OFFERED as what the table's item freeAbove says: THE OPEN LEDGER's
    NUMBER OF SLOTS IS nsPlan, and freeFromB.
  `k5CallerIn3 first`: a Bool, OFFERED as what callerIn says at attention: an attention segment is
    open; its own rounds are not heard; the lookup's return is laid; the ledger stands at `first`.
  `callerIn_of3`: "the ledger is well laid", freeAboveB nsPlan, k5CallerIn3 first and the inequality
    first + kr ≤ nsPlan (a fact on the plan) give k5CallerIn first kr (K05BehindLay.lean): so
    lookIn_behind and lay_returns are spent as they lie.
  `freeAbove_behind`: **freeAboveB nsPlan is kept over the lay**, where the script's slots fit.
  `linkFresh_behind`: linkFreshB reads alike in front of the lay and behind it.
  `above_no_room`: A CONTROL: at a ledger whose next free number is its number of slots freeFromB is
    true and there is no room for one slot: "free from next on" does not say how many slots there
    are: so freeAboveB holds the number.
Limits: as at K05BehindLay.lean. Nothing is tried at a stored proof's record.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Free)
open VerifiableInference.Desc.K3 (sizedB freeB)

/-- Every slot from the open ledger's next free number on is free. -/
def freeFromB (s : First.S) : Bool :=
  s.fork?.any fun G => (List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true

/-- OFFERED: the open ledger has the plan's number of slots, and every slot from its next free
number on is free. -/
def freeAboveB (nsPlan : Nat) (s : First.S) : Bool :=
  (s.fork?.any fun G => G.ns == nsPlan) && freeFromB s

/-- OFFERED: the caller's condition in front at attention, the room taken out. -/
def k5CallerIn3 (first : Nat) (s : First.S) : Bool :=
  match s.here with
  | .att a => a.heard5.isNone && a.g.isSome && a.F.next == first
  | _ => false

section
variable {s : First.S} {a : First.AttOwn} {own : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : Heard} {G : Fork} {first kr nsPlan : Nat}

theorem callerIn3_at (e : s.here = .att a) (hc : k5CallerIn3 first s = true) :
    a.heard5 = none ∧ a.g.isSome = true ∧ a.F.next = first := by
  unfold k5CallerIn3 at hc
  rw [e] at hc
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

theorem freeAbove_at (e : s.here = .att a) (hf : freeAboveB nsPlan s = true) :
    a.F.ns = nsPlan ∧ freeFromB s = true := by
  unfold freeAboveB at hf
  rw [fork_front e] at hf
  simp only [Bool.and_eq_true, Option.any_some, beq_iff_eq] at hf
  exact hf

/-- The slots from the next free number on, any n of them that the ledger has, are free. -/
theorem freeB_of_from (e : s.here = .att a) (hf : freeFromB s = true) {n : Nat}
    (hn : a.F.next + n ≤ a.F.ns) : freeB a.F a.F.next n = true := by
  unfold freeFromB at hf
  rw [fork_front e] at hf
  simp only [Option.any_some, List.all_eq_true, List.mem_range] at hf
  unfold freeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  exact ⟨hn, fun j hj => hf j (by omega)⟩

/-- **The three, and one inequality on the plan, give the elder Bool.** -/
theorem callerIn_of3 (e : s.here = .att a) (hz : s.fork?.any sizedB = true)
    (hf : freeAboveB nsPlan s = true) (hc : k5CallerIn3 first s = true)
    (hfit : first + kr ≤ nsPlan) : k5CallerIn first kr s = true := by
  obtain ⟨h1, h2, h3⟩ := callerIn3_at e hc
  obtain ⟨h4, h5⟩ := freeAbove_at e hf
  rw [fork_front e] at hz
  have hfree := freeB_of_from e h5 (n := kr) (by omega)
  rw [h3] at hfree
  unfold k5CallerIn
  rw [e]
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, hz⟩, hfree⟩

/-- **The item is kept over the lay.** -/
theorem freeAbove_behind (e : s.here = .att a) (hh : hear own (a.F, rs, 0) = some (h, G, [], 0))
    (hz : s.fork?.any sizedB = true) (hf : freeAboveB nsPlan s = true)
    (hn : a.F.next + slotsOf (script own) ≤ nsPlan) : freeAboveB nsPlan (behind s a h G) = true := by
  obtain ⟨h4, h5⟩ := freeAbove_at e hf
  rw [fork_front e] at hz
  have z := sized_of_B hz
  have hfree := freeB_of_from e h5
    (n := slotsOf (script own) + (a.F.ns - a.F.next - slotsOf (script own))) (by omega)
  have R : Room a.F a.F.ns a.F.next
      (slotsOf (script own) + (a.F.ns - a.F.next - slotsOf (script own))) :=
    ⟨rfl, rfl, z, free_of_B z hfree⟩
  have RG := room_behind hh R
  have hB := freeB_of RG.free
  unfold freeB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hB
  show ((some G).any (fun G => G.ns == nsPlan) && (some G).any (fun G =>
    (List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true)) = true
  simp only [Bool.and_eq_true, Option.any_some, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨RG.ns.trans h4, fun j hj => ?_⟩
  rw [RG.ns, RG.next] at hj
  rw [RG.next]
  exact hB.2 j (by omega)

/-- A CONTROL: "free from next on" does not say how many slots there are. -/
theorem above_no_room (e : s.here = .att a) (hn : a.F.ns = a.F.next) :
    freeFromB s = true ∧ ∀ n, 0 < n → freeB a.F a.F.next n = false := by
  refine ⟨?_, fun n h0 => ?_⟩
  · unfold freeFromB
    rw [fork_front e]
    simp [hn]
  · unfold freeB
    have : ¬ (a.F.next + n ≤ a.F.ns) := by omega
    simp [this]

/-- The lay turns nothing that linkFreshB reads. -/
theorem linkFresh_behind (arr : Array (Nat × String)) (e : s.here = .att a) :
    linkFreshB arr (behind s a h G) = linkFreshB arr s := by
  unfold linkFreshB
  rw [tl_front e, link_front e]
  rfl

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.callerIn_of3
#print axioms VerifiableInference.Desc.First.Att.P.freeAbove_behind
#print axioms VerifiableInference.Desc.First.Att.P.above_no_room
#print axioms VerifiableInference.Desc.First.Att.P.linkFresh_behind
