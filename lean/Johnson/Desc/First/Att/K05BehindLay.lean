-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BehindLay.lean: kind K5: WHAT HOLDS OF THE RECORD BEHIND THE HEARING's LAY,
clause by clause, for those clauses of a table's promise that read what the lay turns (the count of
rows owed; the open attention segment's ledger): "no count waits"; "the ledger is well laid"; the
lookup's promise behind its block (k3OnOut); the digits' lookup's promise in front of its block
(k3OnIn).

OBJECT: the seat seatSO (Att/SeatO.lean) and the kind's hearing `hear`. No block, no piece: whoever
has a yes of the kind's block has the two returns (decide_lays, Att/K5Shape.lean).
BUILT ON Johnson/Desc/First/Look/K3Borders.lean: imported, not turned.


Main names:
  `behind s a h G`: the record that the lay returns. `lay_is`: it is that.
  `sized_of_B`, `sizedB_of`, `free_of_B`, `freeB_of`: that file's two Bools are Sized and Free.
  `noneWaits_behind`. `ledger_behind`.
  `lookOut_behind`: **k3OnOut at the calls' seat is kept**: from itself alone.
  `k5CallerIn first kr`: a Bool on the record, OFFERED as what a table's public item "the caller's
    condition in front" says at attention: an attention segment is open; its own rounds are not
    heard; the lookup's return is laid; the ledger stands at `first`, is sized, and the kr slots
    from there on are free. `callerIn_at`, `callerIn_of`: it is just these.
  `linkFreshB arr`: a Bool, OFFERED as an item that the table lacks: nothing is heard at the digits'
    seat; the open link's arrayOf is arr.
  `lookIn_behind`: **k3OnIn at the digits' seat, and the link's number and arrayOf, hold behind the
    lay.**
  `lay_returns`: under k5CallerIn, at a record without a mark, the lay returns at every (h, G).
  `callerIn_spent`: behind the lay k5CallerIn is false: so the item cannot ride: it is rightly
    dropped.

Premises of lookIn_behind: k5CallerIn at kr := the script's slots + the digits' lookup's; linkFreshB;
one equation on the plan (the digits' first slot); the open link's number. The ledger in the
conclusion is the one behind the hearing; in the premises the one in front.
Limits. That any block in front makes k5CallerIn or linkFreshB true is not shown. That no block
between this one and the digits' lookup takes a slot is not shown. Nothing is tried at a stored
proof's record. EMPTY AT: a record at which the hearing does not return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05HearBelow
import Johnson.Desc.First.Att.K05LeavesTl
import Johnson.Desc.First.Att.SeatOFork
import Johnson.Desc.First.Look.K3Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Free)
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-- The record that the hearing's lay returns. -/
def behind (s : First.S) (a : First.AttOwn) (h : Heard) (G : Fork) : First.S :=
  { s with rowsOwed := none, here := .att { a with F := G, heard5 := some h } }

theorem lay_is {s s' : First.S} {h : Heard} {F0 G : Fork} (hl : seatSO.ledger s = some F0)
    (hy : seatSO.lay s h G = some s') : ∃ a, s.here = .att a ∧ a.F = F0 ∧ s' = behind s a h G := by
  obtain ⟨a, e, rfl⟩ := seatSO_lay hy
  obtain ⟨a', e', rfl⟩ := ledgerO_att hl
  rw [e] at e'
  cases e'
  exact ⟨a, e, rfl, rfl⟩

/-! ## The two Bools -/

theorem sized_of_B {G : Fork} (h : sizedB G = true) : Sized G := by
  unfold sizedB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sizedB_of {G : Fork} (h : Sized G) : sizedB G = true := by
  unfold sizedB
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨h.vp, h.mf⟩, h.got⟩

theorem free_of_B {G : Fork} {a n : Nat} (z : Sized G) (h : freeB G a n = true) : Free G a n := by
  unfold freeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  refine ⟨z.got, h.1, fun j h1 h2 => ?_⟩
  have := h.2 (j - a) (by omega)
  rwa [show a + (j - a) = j by omega] at this

theorem freeB_of {G : Fork} {a n : Nat} (h : Free G a n) : freeB G a n = true := by
  unfold freeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  exact ⟨h.2.1, fun j hj => h.2.2 _ (Nat.le_add_right _ _) (by omega)⟩

/-! ## What the lay makes anew -/

section
variable {s : First.S} {a : First.AttOwn} {own : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : Heard} {G : Fork}

theorem fork_front (e : s.here = .att a) : s.fork? = some a.F := by
  unfold First.S.fork?
  rw [e]

theorem tl_front (e : s.here = .att a) : s.tl? = some a.tl := by
  unfold First.S.tl?
  rw [e]

theorem link_front (e : s.here = .att a) : s.link? = some a.L := by
  unfold First.S.link?
  rw [e]

theorem lookHeard_front (e : s.here = .att a) : s.lookHeard? = a.lookHeard := by
  unfold First.S.lookHeard?
  rw [e]

theorem noneWaits_behind : (behind s a h G).noneWaits = true := rfl

/-- **The ledger is well laid behind, if it was in front.** -/
theorem ledger_behind (e : s.here = .att a) (hh : hear own (a.F, rs, 0) = some (h, G, [], 0))
    (hz : s.fork?.any sizedB = true) : (behind s a h G).fork?.any sizedB = true := by
  rw [fork_front e] at hz
  exact sizedB_of (hear_below hh (sized_of_B hz)).1

/-- **The lookup's promise behind its block is kept over the hearing's lay.** -/
theorem lookOut_behind (p : Look.P) (hp : p.digits = false) (e : s.here = .att a)
    (hh : hear own (a.F, rs, 0) = some (h, G, [], 0)) (ho : k3OnOut p s = true) :
    k3OnOut p (behind s a h G) = true := by
  have hk : heardAt p.digits s = a.lookHeard := by
    unfold heardAt
    rw [hp]
    simp only [Bool.false_eq_true, if_false]
    exact lookHeard_front e
  have hk' : heardAt p.digits (behind s a h G) = a.lookHeard := by
    unfold heardAt
    rw [hp]
    simp only [Bool.false_eq_true, if_false]
    rfl
  have hf' : (behind s a h G).fork? = some G := rfl
  unfold k3OnOut at ho ⊢
  rw [hk, fork_front e] at ho
  rw [hk', hf']
  cases hs : p.shape with
  | none =>
    rw [hs] at ho
    simp at ho
  | some hS =>
    cases hg : a.lookHeard with
    | none =>
      rw [hs, hg] at ho
      simp at ho
    | some g =>
      rw [hs, hg] at ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ho ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨h16, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := ho
      obtain ⟨zG, bl⟩ := hear_below hh (sized_of_B h8)
      exact ⟨⟨⟨⟨⟨⟨⟨h16, Nat.le_trans h7 bl.1⟩, sizedB_of zG⟩,
        freeB_of (free_below bl zG (Nat.le_trans h11 h7) (free_of_B (sized_of_B h8) h9))⟩, h10⟩,
        h11⟩, h12⟩, h13⟩

end

/-! ## The caller's condition in front, as a Bool -/

/-- OFFERED: what "the caller's condition in front" says at attention. -/
def k5CallerIn (first kr : Nat) (s : First.S) : Bool :=
  match s.here with
  | .att a => a.heard5.isNone && a.g.isSome && a.F.next == first && sizedB a.F && freeB a.F first kr
  | _ => false

/-- OFFERED: an item that the table lacks. -/
def linkFreshB (arr : Array (Nat × String)) (s : First.S) : Bool :=
  (s.tl?.bind (·.heard)).isNone && s.link?.any fun L => L.arrayOf == arr

section
variable {s : First.S} {a : First.AttOwn} {own : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : Heard} {G : Fork} {first kr : Nat}

theorem callerIn_open (hc : k5CallerIn first kr s = true) : ∃ a, s.here = .att a := by
  unfold k5CallerIn at hc
  split at hc
  · exact ⟨_, by assumption⟩
  · cases hc

theorem callerIn_at (e : s.here = .att a) (hc : k5CallerIn first kr s = true) :
    a.heard5 = none ∧ a.g.isSome = true ∧ Room a.F a.F.ns first kr := by
  unfold k5CallerIn at hc
  rw [e] at hc
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨h1, h2, rfl, h3, sized_of_B h4, free_of_B (sized_of_B h4) h5⟩

theorem callerIn_of (e : s.here = .att a) (h1 : a.heard5 = none) (h2 : a.g.isSome = true) {ns : Nat}
    (R : Room a.F ns first kr) : k5CallerIn first kr s = true := by
  unfold k5CallerIn
  rw [e]
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none]
  exact ⟨⟨⟨⟨h1, h2⟩, R.next⟩, sizedB_of R.sized⟩, freeB_of R.free⟩

/-- **The digits' lookup's promise in front of its block holds behind the hearing's lay.** -/
theorem lookIn_behind (pD : Look.P) (hD : pD.digits = true) {hS : Forest.Shape}
    (hs : pD.shape = some hS) {arr : Array (Nat × String)} (e : s.here = .att a)
    (hh : hear own (a.F, rs, 0) = some (h, G, [], 0))
    (hc : k5CallerIn first (slotsOf (script own) + Forest.elems hS) s = true)
    (hf : linkFreshB arr s = true) (h1 : pD.first = first + slotsOf (script own))
    (h2 : s.link?.any (fun L => L.link == pD.link) = true) :
    k3OnIn pD (behind s a h G) = true ∧
      (behind s a h G).link?.any (fun L => L.link == pD.link && L.arrayOf == arr) = true := by
  obtain ⟨_, _, R⟩ := callerIn_at e hc
  have RG := room_behind hh R
  unfold linkFreshB at hf
  rw [tl_front e, link_front e] at hf
  rw [link_front e] at h2
  simp only [Bool.and_eq_true] at hf
  refine ⟨?_, ?_⟩
  · unfold k3OnIn
    rw [hs]
    have hk : heardAt pD.digits (behind s a h G) = a.tl.heard := by
      unfold heardAt
      rw [hD]
      rfl
    have hf' : (behind s a h G).fork? = some G := rfl
    have hr : First.Tape.RowsOwed.noneWaits (behind s a h G).rowsOwed = true := rfl
    simp only [hk, hf', hr, Option.any_some, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hf.1, trivial⟩, ⟨RG.next.trans h1.symm, sizedB_of RG.sized⟩,
      freeB_of (h1 ▸ RG.free)⟩
  · show (some a.L).any (fun L => L.link == pD.link && L.arrayOf == arr) = true
    simp only [Option.any_some, Bool.and_eq_true] at h2 hf ⊢
    exact ⟨h2, hf.2⟩

/-- **Under the caller's condition, at a record without a mark, the lay returns.** -/
theorem lay_returns (e : s.here = .att a) (hc : k5CallerIn first kr s = true)
    (hu : s.failed = none) (h : Heard) (G : Fork) : seatSO.lay s h G = some (behind s a h G) := by
  obtain ⟨h5, hg, _⟩ := callerIn_at e hc
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hg
  show (match s.here with
      | .att a => a.g.bind fun _ =>
        (First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h).toOption
      | _ => none) = _
  rw [e]
  simp only [hg, Option.bind_some, First.S.hear5?, First.S.hear5, h5, Option.isSome_none,
    Bool.false_eq_true, if_false, First.S.unmarked, hu, Except.toOption, behind]

/-- Behind the lay the caller's condition is false: the item does not ride. -/
theorem callerIn_spent : k5CallerIn first kr (behind s a h G) = false := rfl

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lay_is
#print axioms VerifiableInference.Desc.First.Att.P.noneWaits_behind
#print axioms VerifiableInference.Desc.First.Att.P.ledger_behind
#print axioms VerifiableInference.Desc.First.Att.P.lookOut_behind
#print axioms VerifiableInference.Desc.First.Att.P.callerIn_at
#print axioms VerifiableInference.Desc.First.Att.P.callerIn_of
#print axioms VerifiableInference.Desc.First.Att.P.lookIn_behind
#print axioms VerifiableInference.Desc.First.Att.P.lay_returns
#print axioms VerifiableInference.Desc.First.Att.P.callerIn_spent
