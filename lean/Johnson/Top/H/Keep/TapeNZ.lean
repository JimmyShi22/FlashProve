--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/TapeNZ.lean: A TAPE's DRAWS THAT MAY NEVER BE 0 ARE NOT 0, AS WORDS: an invariant
on tapes (OnBytes/K/Kc/Flat.lean) that every call on a tape keeps, that every tape has which the
maker of tapes makes of a view (Johnson/Desc/First/Tape/Tape.lean: its seventh clause), and that
gives, at each call "close the round, one element drawn by the rule that never gives 0", that the
drawn element's three words are not all 0. Definitions, statements and proofs.

Main names:
  NZ x: of the round x the last x.nz drawn elements are not (0, 0, 0). AllNZ t: every round of t.
  recv_nz, recvLoop_nz, closeN_nz, closeOne_nz: the four ground functions keep it.
  at_nz: every call keeps it. evs_nz: so do calls in a row; AND EVERY ELEMENT THAT A CALL ansNZ OF
    THE ROW RETURNS IS NOT ZERO AS WORDS.
  roundT_nz, tapeT_nz: of the maker's tapes.

Limits. isZeroE tests the three WORDS. On words below the prime that says that the field element is
not 0 (the library's isZeroE_iff asks okE); the maker of tapes has no clause on that: a view whose
draw spells the prime itself passes. Nothing here says that a view's draws are canonical.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Tape.Tape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (roundT tapeT TapeRule)

/-- The last x.nz drawn elements of the round are not (0, 0, 0). -/
def NZ (x : FlatRound) : Prop := ∀ d ∈ x.drawn.drop (x.drawn.length - x.nz), isZeroE d = false

def AllNZ (t : Tape) : Prop := ∀ x ∈ t, NZ x

theorem AllNZ.tail {x : FlatRound} {t : Tape} (h : AllNZ (x :: t)) : AllNZ t :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem recv_nz {c c' : Tape} {x : E} (h : recv c = some (x, c')) (hc : AllNZ c) : AllNZ c' := by
  unfold recv at h
  split at h
  · rename_i nm z w y s d t
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hc ⟨nm, z, w, y :: s, d⟩ List.mem_cons_self
    · exact hc r (List.mem_cons_of_mem _ hr)
  · cases h

theorem recvLoop_nz : ∀ (n : Nat) (a v : Array E) (c c' : Tape), recvLoop n a c = some (v, c') →
    AllNZ c → AllNZ c'
  | 0, a, v, c, c', h, hc => by
    unfold recvLoop at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hc
  | n + 1, a, v, c, c', h, hc => by
    unfold recvLoop at h
    split at h
    · rename_i x u hx
      exact recvLoop_nz n _ v u c' h (recv_nz hx hc)
    · cases h

theorem closeN_nz {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) (hc : AllNZ c) : AllNZ c' := by
  obtain ⟨_, nm, z, w, rfl⟩ := closeN_some h
  exact hc.tail

/-- The round's flag is what was asked; so at the flag 1 the one drawn element is not zero. -/
theorem closeOne_nz {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) (hc : AllNZ c) :
    AllNZ c' ∧ (nz = 1 → isZeroE x = false) := by
  unfold closeOne at h
  split at h
  · rename_i nm z w y t
    split at h
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      refine ⟨hc.tail, fun h1 => ?_⟩
      have hz : z = 1 := hb.2.trans h1
      have := hc ⟨some nm, z, w, [], [y]⟩ List.mem_cons_self y
      rw [hz] at this
      exact this (by simp)
    · cases h
  · cases h

/-- **Every call keeps it.** -/
theorem at_nz {e : Ev} {c c' : Tape} (h : At e c c') (hc : AllNZ c) : AllNZ c' := by
  cases e with
  | sum x => exact recv_nz h hc
  | ans r x => exact (closeOne_nz h hc).1
  | ansNZ r x => exact (closeOne_nz h hc).1
  | read n v => exact recvLoop_nz n _ v c c' h hc
  | empty r =>
    have h' : (closeN r.name 0 0 c).map (fun x => ((), x.2)) = some ((), c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact closeN_nz (d := y.1) (c' := y.2) hy hc
  | point r n v =>
    have h' : (closeN r.name 0 n c).map (fun x => (x.1.toArray, x.2)) = some (v, c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact closeN_nz (d := y.1) (c' := y.2) hy hc

/-- **Calls in a row.** -/
theorem evs_nz : ∀ (l : List Ev) (c c' : Tape), Evs l c c' → AllNZ c →
    AllNZ c' ∧ ∀ r x, Ev.ansNZ r x ∈ l → isZeroE x = false
  | [], c, c', h, hc => by
    obtain rfl : c' = c := h
    exact ⟨hc, fun _ _ hm => nomatch hm⟩
  | e :: l, c, c', h, hc => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨a, b⟩ := evs_nz l c1 c' h2 (at_nz h1 hc)
    refine ⟨a, fun r x hm => ?_⟩
    rcases List.mem_cons.1 hm with rfl | hm
    · exact (closeOne_nz (nz := 1) h1 hc).2 rfl
    · exact b r x hm

/-! ## The maker's tapes -/

theorem roundT_nz {rule : TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound}
    (h : roundT rule r e = some x) : NZ x := by
  unfold roundT at h
  split at h
  · cases h
  · split at h
    · rename_i hb
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨⟨⟨⟨⟨hlen, _⟩, _⟩, _⟩, _⟩, _⟩, h7⟩ := hb
      intro d hd
      have hd' : d ∈ ((r.drawn.elems.map E.ofTriple).drop
          ((r.drawn.elems.map E.ofTriple).length - e.drawNZ)) := hd
      rw [List.length_map, hlen, ← List.map_drop] at hd'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd'
      exact h7 y hy
    · cases h

theorem tapeT_nz (rule : TapeRule) : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    tapeT rule rs es = some t → AllNZ t
  | [], [], t, h => by
    obtain rfl : [] = t := Option.some.inj h
    exact fun _ hx => nomatch hx
  | r :: rs, e :: es, t, h => by
    unfold tapeT at h
    split at h
    · rename_i x u hx hu
      obtain rfl := Option.some.inj h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact roundT_nz hx
      · exact tapeT_nz rule rs es u hu y hy
    · cases h
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

end Fo.Tp

#print axioms Fo.Tp.at_nz
#print axioms Fo.Tp.evs_nz
#print axioms Fo.Tp.roundT_nz
#print axioms Fo.Tp.tapeT_nz
