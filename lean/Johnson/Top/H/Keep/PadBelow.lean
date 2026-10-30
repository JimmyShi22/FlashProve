-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/PadBelow.lean: The kind "lookup" (K3): A LOOKUP's HEARING TURNS NOTHING UNDER A
SLOT BELOW THE NEXT SLOT OF THE LEDGER IN FRONT, OR FROM THE NEXT SLOT OF THE LEDGER BEHIND ON: the
mark, the shown value and the factor are as they were: AT FREE SLOTS TOO. At the library's flat
copy of the routine, and at an accept of K3.block's decide at any seat. Statements and proofs:
joinings.

OBJECT: lkPad; K3.block's decide.
Used by Johnson/Desc/First/Look/K3DigitsSameBelow.lean.
LETTERS: all free.
Compiled with the whole library.

Why. The library's Stretch F G n (OnBytes/Tie/Pv/Lookup/Forest/FoStretch.lean) has the clause
"out": outside the n slots from F.next on the shown values and the factors are F's. The hearing is
two stretches with the leaves' window, which it leaves free, between them (as in
Johnson/Top/H/Keep/PadExact.lean).

Main names:
  pad_out, lkPad_out: the shown value and the factor.
  decide_out: THE END: with the mark (PadExact.marks): IN THE UNFOLDED TEXT OF
    SameAt F G j (Johnson/Road/K4/Slots/HearSpares.lean): (Filled G j ↔ Filled F j) ∧
    G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE; at
    j < F.next ∨ G.next ≤ j: the second field of that file's Fresh F G.

Limits. The ledger in front has its sizes: a premise. Over the decision's own accept: the seated
sub-protocol is K3's block and then a step without a round: that step's share is not here.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

/-- From the two stretches. -/
theorem pad_out {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (nA nL nB : ℕ)
    (sA : Stretch (owed3 F) M.F7 nA) (sB : Stretch (took M.F7 nL) M.G8 nB) :
    ∀ j, (j < F.next ∨ F'.next ≤ j) →
      F'.vp.getD j zeroE = F.vp.getD j zeroE ∧ F'.mf.getD j zeroE = F.mf.getD j zeroE := by
  have h7 : M.F7.next = F.next + nA := sA.next
  have h8 : M.G8.next = F.next + nA + nL + nB := by
    rw [sB.next]
    show M.F7.next + nL + nB = _
    rw [h7]
  rw [P.fork]
  intro j hj
  have a : M.F7.vp.getD j zeroE = F.vp.getD j zeroE ∧
      M.F7.mf.getD j zeroE = F.mf.getD j zeroE :=
    sA.out j (by
      show j < F.next ∨ F.next + nA ≤ j
      omega)
  have b : M.G8.vp.getD j zeroE = M.F7.vp.getD j zeroE ∧
      M.G8.mf.getD j zeroE = M.F7.mf.getD j zeroE :=
    sB.out j (by
      show j < M.F7.next + nL ∨ M.F7.next + nL + nB ≤ j
      omega)
  exact ⟨b.1.trans a.1, b.2.trans a.2⟩

/-- **Of the library's flat copy**, wherever it returns from a ledger that has its sizes. -/
theorem lkPad_out (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F) :
    ∀ j, (j < F.next ∨ F'.next ≤ j) →
      F'.vp.getD j zeroE = F.vp.getD j zeroE ∧ F'.mf.getD j zeroE = F.mf.getD j zeroE := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  exact pad_out P _ _ _
    ((R.f4 ▸ R.tieSt).trans ((⟨R.keys.same, R.keys.filled, R.keys.out⟩ :
      Stretch M.F5 M.F6 _).trans ⟨R.table.same, R.table.filled, R.table.out⟩))
    R.r5.stretch

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide: nothing turns below the next slot in front, or from the next slot behind
on.** -/
theorem decide_out {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ s' = seat.put s x.1 x.2 ∧
      (Sized F → F.next ≤ x.2.next ∧ ∀ j, (j < F.next ∨ x.2.next ≤ j) →
        (Filled x.2 j ↔ Filled F j) ∧ x.2.vp.getD j zeroE = F.vp.getD j zeroE ∧
          x.2.mf.getD j zeroE = F.mf.getD j zeroE) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, rfl, fun hS => ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      have E := _root_.Fo.Tp.lkPad_exact p.calls p.pub p.lid F x.2 t [] x.1 hl hS
      have O := _root_.Fo.Tp.lkPad_out p.calls p.pub p.lid F x.2 t [] x.1 hl hS
      have en := E.next
      refine ⟨by omega, fun j hj => ⟨?_, O j hj⟩⟩
      rw [E.marks]
      exact ⟨fun y => y.elim id fun z => absurd z.1 (by
        have := z.2.1
        omega), Or.inl⟩
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.pad_out
#print axioms Fo.Tp.lkPad_out
#print axioms VerifiableInference.OnPublicFiles.decide_out
