-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown here at which K3LeftAt holds.
Johnson/Top/H/Keep/K3LeftWindow.lean: The kind "lookup" (K3): WHAT THE SENTENCE "WHAT THE LOOKUP ON
THE CALLS LEFT" (K3Left, K3LeftAt: Johnson/Top/H/K3LeftStatement.lean; k3LeftItem:
Johnson/Desc/First/Look/K3LeftItem.lean) SAYS OF THE SLOTS OF THE SUMCHECK OVER THE LEAVES, OF THE
SLOT OF THE BITS' SHOWN VALUE, OF THE LEDGER's ROOM AND OF THE THREE DEBTS: all that the lookup's
two later runs of claims ("planes", "join") ask of the ledger and of what was heard, but for the
calling kind's own forms. FROM THE SENTENCE ALONE: no accept of a decide is a premise. Statements
and proofs. Ties of texts and numbers: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: K3Left and K3LeftAt; K3.unpaid (Johnson/Desc/First/Look/K3Runs.lean); the test in front of
  leavesRowOwn (Johnson/Desc/First/Look/LookPlanesOwn.lean).
Used by Johnson/Desc/First/Look/K3CallsLeftAt.lean, Johnson/Desc/Kinds/Law/LeavesReadyPaid.lean,
  Johnson/P4R/LeavesFilledAt341.lean and others.
LETTERS: K, ρ, h, lm, F (the ledger in front of the lookup), F' (the ledger that it leaves), g (what
  the lookup's verifier has heard), rs free.
Compiled with the whole library.

Why. K3Left holds the library's HeardIs and PadLeft. They name the first slot of the leaves' window
and the slot of the bits' shown value through the end values endsOf, and the window's length through
the sumcheck's variables. Here these are numbers.

Main names:
  left_numbers: the window begins fEnd slots behind F.next; it has 1 + 2 d + 5 slots in the count of
    Forest.elems; the slot of the bits' shown value IS THE LOOKUP's LAST SLOT.
  left_first, left_within, left_sBit: the same, one by one.
  left_len: the walk of the sumcheck over the leaves has 1 + 2 d + 5 members: as many slots as the
    run "planes" fills.
  left_sBitIn: the slot of the bits' shown value is below the number of slots, and filled.
  left_room: SO ALL THE LOOKUP's SLOTS ARE BELOW THE NUMBER OF SLOTS: its last one is filled, and a
    filled slot of a ledger with its sizes is there. No premise on room is needed.
  left_flags: the test of leavesRowOwn: no claim made yet, begun, a variable, a challenge for each.
  left_unpaid: none of the three debts is marked as paid.
  left_free: the window is free in F' where F was free from its next slot on.
  leavesReady_of_leftAt: THE BRIDGE: K3LeftAt at Q := LeftQ n gives, of the ledger and of what was
    heard at that state, five clauses, WRITTEN OUT IN THE ORDER OF THE FIELDS OF THE
    STRUCTURE LeavesReady (Johnson/Desc/Kinds/Law/SilentPlanes.lean),
    which this file does not import.
  leavesFree_of_leftAt: the window in the word Part.MaskedSum.Free
    (Johnson/Desc/Part/MaskedSumLaw.lean), with the clause "below the next slot".
  leftAt_numbers: the numbers at the state.
  leavesReady_of_item, leavesFree_of_item: from k3LeftItem p s.
  LeavesFilled s: every slot that the starting form of the sumcheck over the leaves names is there
    and filled in the ledger in hand. THE SENTENCE K3LeftAt DOES NOT SAY IT (it speaks of that
    form's worth, not of its text); LeavesBare has the half on entries.
  k3_calls_leavesFilled: an accept of the kind's decide at the calls' seat makes it.
  leavesFilled_stays: it stands at every later state at which what was heard stays.

Limits. Nothing on what lies under a slot. Nothing on the calling kind's forms. That the run
"planes" accepts from these clauses is planesRun_answers (SilentPlanes.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.Part.MaskedSumReturns
import Johnson.Desc.Part.MaskedSumLaw
import Johnson.Top.H.K3OnOutOfLeft
import Johnson.Top.H.K3SeatFits
import Johnson.Top.H.Keep.K3Named
import OnBytes.Tie.Pv.Lookup.Forest.FoLedAt
import OnBytes.Tie.Pv.Lookup.Forest.FoPscForm
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun

/-! ## Three debts more -/

/-- The three entries that were pushed last. -/
theorem pushed3_at {α : Type} (a : Array α) (x y z : α) :
    (((a.push x).push y).push z)[a.size]? = some x ∧
      (((a.push x).push y).push z)[a.size + 1]? = some y ∧
      (((a.push x).push y).push z)[a.size + 2]? = some z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega),
      Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega),
      Array.getElem?_push, if_pos rfl]
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega),
      Array.getElem?_push, if_pos (by simp only [Array.size_push])]
  · rw [Array.getElem?_push, if_pos (by simp only [Array.size_push])]

section
variable {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : Forest.Shape} {lm : ℕ}
  {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds K}

/-! ## The numbers -/

/-- **Where the leaves' window and the slot of the bits' shown value lie among the lookup's
slots.** -/
theorem left_numbers (L : K3Left ρ h lm F F' g rs) :
    g.leaves.first = F.next + (FoNums.S h).fEnd ∧
      g.sBit = F.next + (FoNums.S h).fEnd + (1 + 2 * h.d + 5) + (1 + (5 + h.d) * 2 + 2) ∧
      Forest.elems h = (FoNums.S h).fEnd + (1 + 2 * h.d + 5) + (1 + (5 + h.d) * 2 + 2 + 1) := by
  have e0 : g.sBit = _root_.Fo.slotNo ((_root_.Fo.ledF F.next (FoNums.S h).pBitC).sh 0) :=
    L.heardIs.sBit
  rw [(_root_.Fo.ledAt_bit h F.next).sh 0 Nat.one_pos] at e0
  have e1 : g.sBit =
      F.next + (FoNums.S h).fBit + 1 + (List.replicate (5 + h.d) 2 ++ [2]).sum + 0 := e0
  have e2 : (List.replicate (5 + h.d) 2 ++ [2]).sum = (5 + h.d) * 2 + 2 := by simp
  have e3 : (FoNums.S h).fBit + (1 + (5 + h.d) * 2 + 2 + 1) = Forest.elems h :=
    Cb.Fo.Walk.first_all h
  have e4 := Cb.Fo.Walk.first_bit h
  refine ⟨L.heardIs.lvFirst, ?_, ?_⟩
  · omega
  · omega

theorem left_first (L : K3Left ρ h lm F F' g rs) :
    g.leaves.first = F.next + (FoNums.S h).fEnd := (left_numbers L).1

/-- The window ends within the lookup's slots. -/
theorem left_within (L : K3Left ρ h lm F F' g rs) :
    g.leaves.first + (1 + 2 * h.d + 5) ≤ F.next + Forest.elems h := by
  obtain ⟨a, _, c⟩ := left_numbers L
  omega

/-- **The slot of the bits' shown value is the lookup's last slot.** -/
theorem left_sBit (L : K3Left ρ h lm F F' g rs) : g.sBit + 1 = F.next + Forest.elems h := by
  obtain ⟨_, b, c⟩ := left_numbers L
  omega

/-- The sumcheck over the leaves has run, with the degrees of the lookup's own list. -/
theorem left_ran (L : K3Left ρ h lm F F' g rs) :
    ∃ (mu : E) (zd : List (E × ℕ)) (rs' : List (List E × E)),
      Ran g.leaves (F.next + (FoNums.S h).fEnd) mu g.leaves.eps zd rs' ∧
        (_root_.Fo.dgOf zd).sum = 5 + 2 * h.d ∧ zd ≠ [] := by
  obtain ⟨mu, zd, rs', hRan, _, hdg⟩ := L.heardIs.lvRan
  have hdg' : _root_.Fo.dgOf zd = (FoNums.S h).scEnd.degs := by
    have e1 : _root_.Fo.dgOf zd = (zd.map fun p => p.2).map (· - 1) := by
      unfold _root_.Fo.dgOf
      rw [List.map_map]
      rfl
    rw [e1, hdg, List.map_map]
    have e2 : ((fun x : ℕ => x - 1) ∘ fun x => x + 1) = id := funext fun x => by simp
    rw [e2, List.map_id]
    exact (_root_.Fo.nums_led h F.next lm (_root_.Fo.thetaOf h rs)).2.2.2.2.2.2
  have hsum : (FoNums.S h).scEnd.degs.sum = 5 + 2 * h.d := by
    show ((List.range (5 + h.d)).reverse.map fun t => if t < 5 then 1 else 2).sum = _
    rw [List.map_reverse, List.sum_reverse, FoLedger.end_sum]
  refine ⟨mu, zd, rs', hRan, by rw [hdg', hsum], fun h0 => ?_⟩
  rw [h0] at hdg'
  have h2 := congrArg List.sum hdg'
  rw [hsum] at h2
  have h1 : (_root_.Fo.dgOf ([] : List (E × ℕ))).sum = 0 := rfl
  omega

/-- **The walk has as many members as the window has slots.** -/
theorem left_len (L : K3Left ρ h lm F F' g rs) : g.leaves.walk.1.length = 1 + 2 * h.d + 5 := by
  obtain ⟨mu, zd, rs', hRan, hsum, hne⟩ := left_ran L
  rw [_root_.Fo.walk_len hRan hne, hsum]
  omega

/-! ## The ledger -/

/-- **The slot of the bits' shown value is there and filled.** -/
theorem left_sBitIn (L : K3Left ρ h lm F F' g rs) : g.sBit < F'.ns ∧ Filled F' g.sBit := by
  obtain ⟨a, b, c⟩ := left_numbers L
  have hf : Filled F' g.sBit :=
    L.padLeft.filled g.sBit (by omega) (by omega) (by omega)
  exact ⟨filled_lt L.padLeft.fit.2.2 hf, hf⟩

/-- **So all the lookup's slots are there.** -/
theorem left_room (L : K3Left ρ h lm F F' g rs) : F.next + Forest.elems h ≤ F'.ns := by
  have a := left_sBit L
  have b := (left_sBitIn L).1
  omega

/-- **The test in front of the claim that the sumcheck over the leaves leaves.** -/
theorem left_flags (L : K3Left ρ h lm F F' g rs) :
    (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
      g.leaves.r.size == g.leaves.vars.size) = true := by
  obtain ⟨mu, zd, rs', hRan, _, hne⟩ := left_ran L
  have hl : g.leaves.vars.toList ≠ [] := by
    rw [hRan.vars_eq]
    unfold OnBytes.PscTie.eqW
    intro h0
    exact hne (List.map_eq_nil_iff.1 h0)
  have hv : g.leaves.vars.isEmpty = false := by
    cases e : g.leaves.vars.isEmpty with
    | false => rfl
    | true => exact absurd (congrArg Array.toList (Array.isEmpty_iff.1 e)) hl
  rw [L.heardIs.lvFlags.2.2, L.heardIs.lvFlags.1, hv, L.heardIs.lvSize]
  simp

/-- **None of the three debts is marked as paid.** -/
theorem left_unpaid (L : K3Left ρ h lm F F' g rs) :
    Desc.K3.unpaid F' g.owedObjects = true ∧ Desc.K3.unpaid F' g.owedPlanes = true ∧
      Desc.K3.unpaid F' g.owedJoin = true := by
  have P := L.padLeft
  obtain ⟨a, b, c⟩ := pushed3_at F.owed ({ what := "look-up-mask-claims" } : Owed)
    { what := "look-up-plane-claims" } { what := "look-up-join" }
  refine ⟨?_, ?_, ?_⟩
  · unfold Desc.K3.unpaid
    rw [P.owedAt.1, P.owed, a]
    rfl
  · unfold Desc.K3.unpaid
    rw [P.owedAt.2.1, P.owed, b]
    rfl
  · unfold Desc.K3.unpaid
    rw [P.owedAt.2.2, P.owed, c]
    rfl

/-- **The window is free behind the lookup**, where the ledger in front was free from its next slot
on. -/
theorem left_free (L : K3Left ρ h lm F F' g rs)
    (hfree : ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false) :
    ∀ j, g.leaves.first ≤ j → j < g.leaves.first + g.leaves.walk.1.length →
      F'.gotF.getD j true = false := by
  intro j h1 h2
  rw [left_len L] at h2
  have hw := left_within L
  have hf := left_first L
  have hr := left_room L
  have hns : F'.ns = F.ns := L.padLeft.rest.2.1
  have hj : j < F'.ns := by omega
  have nF : ¬ Filled F j := by
    intro hc
    have q := getD_in _ _ (hfree j (by omega) (by omega))
    unfold Filled at hc
    rw [q] at hc
    cases hc
  have nF' : ¬ Filled F' j := fun hc => nF ((L.padLeft.leaves j h1 h2).1.1 hc)
  exact free_getD L.padLeft.fit.2.2 hj nF'

end

/-! ## At a state of the verifier -/

section
variable {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
  {h : Forest.Shape} {lm first n : ℕ} {s : S}

/-- **THE BRIDGE.** The five clauses stand in the order of the fields flags, free, below, planes,
join. -/
theorem leavesReady_of_leftAt (L : K3LeftAt fork heard h lm first (LeftQ n) s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧
      (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
        g.leaves.r.size == g.leaves.vars.size) = true ∧
      Desc.Part.MaskedSum.FreeIn F' g.leaves.first (g.leaves.first + g.leaves.walk.1.length) ∧
      g.leaves.first + g.leaves.walk.1.length ≤ F'.next ∧
      Desc.K3.unpaid F' g.owedPlanes = true ∧ Desc.K3.unpaid F' g.owedJoin = true := by
  obtain ⟨F, F', g, rs, hQ, _, L, hg, hf⟩ := L
  refine ⟨F', g, hf, hg, left_flags L, ⟨?_, L.padLeft.fit.2.2, left_free L hQ.2.2⟩, ?_,
    (left_unpaid L).2.1, (left_unpaid L).2.2⟩
  · rw [left_len L]
    exact Nat.le_trans (left_within L) (left_room L)
  · rw [left_len L, L.padLeft.next]
    exact left_within L

/-- The window in the word Free, with "below the next slot". -/
theorem leavesFree_of_leftAt (L : K3LeftAt fork heard h lm first (LeftQ n) s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧
      Desc.Part.MaskedSum.Free F' g.leaves.first g.leaves.walk.1.length ∧
      g.leaves.first + g.leaves.walk.1.length ≤ F'.next := by
  obtain ⟨F', g, a, b, _, c, d, _, _⟩ := leavesReady_of_leftAt L
  exact ⟨F', g, a, b, ⟨c.2.1, c.1, c.2.2⟩, d⟩

/-- **The numbers at the state.** -/
theorem leftAt_numbers (L : K3LeftAt fork heard h lm first (LeftQ n) s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧ Sized F' ∧ F'.ns = n ∧ g.shape = h ∧
      F'.next = first + Forest.elems h ∧ F'.next ≤ F'.ns ∧
      g.leaves.walk.1.length = 1 + 2 * h.d + 5 ∧ first ≤ g.leaves.first ∧
      g.leaves.first + (1 + 2 * h.d + 5) ≤ g.sBit ∧ g.sBit + 1 = F'.next ∧
      Filled F' g.sBit := by
  obtain ⟨F, F', g, rs, hQ, hn, L, hg, hf⟩ := L
  obtain ⟨a, b, c⟩ := left_numbers L
  have hx := L.padLeft.next
  have hr := left_room L
  refine ⟨F', g, hf, hg, L.padLeft.fit, L.padLeft.rest.2.1.trans hQ.2.1, L.shape, ?_, ?_,
    left_len L, ?_, ?_, ?_, (left_sBitIn L).2⟩
  · rw [hx, hn]
  · omega
  · omega
  · omega
  · omega

end

section
variable {p : Desc.First.Look.P} {s : Desc.First.S}

/-- The bridge from the item's own wording. -/
theorem leavesReady_of_item (L : k3LeftItem p s) :
    ∃ F' g, s.fork? = some F' ∧ s.lookHeard? = some g ∧
      (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
        g.leaves.r.size == g.leaves.vars.size) = true ∧
      Desc.Part.MaskedSum.FreeIn F' g.leaves.first (g.leaves.first + g.leaves.walk.1.length) ∧
      g.leaves.first + g.leaves.walk.1.length ≤ F'.next ∧
      Desc.K3.unpaid F' g.owedPlanes = true ∧ Desc.K3.unpaid F' g.owedJoin = true := by
  obtain ⟨⟨h, _, L⟩, _⟩ := L
  exact leavesReady_of_leftAt L

theorem leavesFree_of_item (L : k3LeftItem p s) :
    ∃ F' g, s.fork? = some F' ∧ s.lookHeard? = some g ∧
      Desc.Part.MaskedSum.Free F' g.leaves.first g.leaves.walk.1.length ∧
      g.leaves.first + g.leaves.walk.1.length ≤ F'.next := by
  obtain ⟨⟨h, _, L⟩, _⟩ := L
  exact leavesFree_of_leftAt L

end

/-! ## The slots that the leaves' starting form names -/

/-- Every slot that the starting form of the sumcheck over the leaves names is there and filled in
the ledger in hand. The sister of LeavesBare. -/
def LeavesFilled (s : Desc.First.S) : Prop :=
  ∀ g G, s.lookHeard? = some g → s.fork? = some G → _root_.Fo.FilledA G g.leaves.start

/-- **An accept of the kind's decide at the calls' seat makes it.** -/
theorem k3_calls_leavesFilled {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hz : Sized F) : LeavesFilled s' := by
  obtain ⟨F1, x, hF1, hn, e, hN⟩ :=
    decide_named (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : s'.lookHeard? = some x.1 := by
    rw [e]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn
  have hf1 : s'.fork? = some x.2 := by
    rw [e]
    exact seatCalls_keeps claim _ _ _ hsome hn
  intro g G hg hG
  obtain rfl : x.1 = g := Option.some.inj (hg1.symm.trans hg)
  obtain rfl : x.2 = G := Option.some.inj (hf1.symm.trans hG)
  exact (hN hz).start.filledA

/-- **It stands at every later state** at which what was heard stays. -/
theorem leavesFilled_stays {s t : Desc.First.S} {Fs Ft : Fork}
    (hh : t.lookHeard? = s.lookHeard?) (hs : s.fork? = some Fs) (ht : t.fork? = some Ft)
    (hl : _root_.Fo.Later Fs Ft) (L : LeavesFilled s) : LeavesFilled t := by
  intro g G hg hG
  obtain rfl : Ft = G := Option.some.inj (ht.symm.trans hG)
  intro x hx
  obtain ⟨a, b⟩ := L g Fs (hh.symm.trans hg) hs x hx
  exact ⟨by rw [hl.ns]; exact a, (hl.keep _ b).1⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.left_numbers
#print axioms VerifiableInference.OnPublicFiles.left_len
#print axioms VerifiableInference.OnPublicFiles.left_sBitIn
#print axioms VerifiableInference.OnPublicFiles.left_room
#print axioms VerifiableInference.OnPublicFiles.left_flags
#print axioms VerifiableInference.OnPublicFiles.left_unpaid
#print axioms VerifiableInference.OnPublicFiles.left_free
#print axioms VerifiableInference.OnPublicFiles.leavesReady_of_leftAt
#print axioms VerifiableInference.OnPublicFiles.leavesFree_of_leftAt
#print axioms VerifiableInference.OnPublicFiles.leftAt_numbers
#print axioms VerifiableInference.OnPublicFiles.leavesReady_of_item
#print axioms VerifiableInference.OnPublicFiles.leavesFree_of_item
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leavesFilled
#print axioms VerifiableInference.OnPublicFiles.leavesFilled_stays
