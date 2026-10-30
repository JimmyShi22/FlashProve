-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which the kind's decide accepts.
Johnson/Top/H/Keep/K3LeftAnyWords.lean: The kind "lookup" (K3): WHAT AN ACCEPT OF THE KIND's decide
LEAVES (K3Left, K3LeftAt: Johnson/Top/H/K3LeftStatement.lean; k3LeftItem:
Johnson/Desc/First/Look/K3LeftItem.lean), WITH NO PREMISE ON THE ROUNDS' WORDS: whether or not each
word of a field's element in the rounds shown is below the prime. Statements and proofs. Ties of
texts: no error term. NO SOUNDNESS IS CLAIMED.

Why. k3Leaves_seat (Johnson/Desc/First/Look/K3LeftBodyLaw.lean) and k3_calls_left_any | _leftItem
(K3LeftItem.lean) ask okRoundsE rs = true. At a seated piece that is had off the transcript's type.
Along a fold of sub-protocols it is not: a step tests the rounds' lengths and positions, and holds
no word below the prime. In these proofs ONE step spends that premise, and only to NAME the rounds:
"what was heard holds the end values AT rs, READ IN K". K3LeftAt, K3LeftOn and k3LeftItem say "there
are rounds": they never name them. The library's law on the flat hearing (lkPad_law,
Johnson/Top/H/FlPort/LkPadLaw.lean) gives the same sentence at the rounds that the hearing took off
its tape, under no premise on a word.

OBJECT: Desc.K3.block's decide, at any seat; at Desc.K3.seatCalls claim.
Used by Johnson/Desc/First/Link/Law/KxAtFront.lean, Johnson/Desc/First/Look/K03ReachedAt.lean,
  Johnson/Desc/First/Look/K3CallsLeftAt.lean and others.
LETTERS: seat, piece, laid, before, p, guests, h, K, ρ, lm, s, s', rs, cols, F, Q free.
Compiled with the whole library.

Main names:
  decide_marks: in decide_named's form (Johnson/Top/H/Keep/K3Named.lean), at any seat, with no law
    on the seat: the sumcheck over the leaves is begun, its claim is not made, it has as many
    challenges as variables; and what was heard has the place's shape.
  decide_left_some: the whole: K3Left AT SOME ROUNDS, at any seat that reads back what was heard
    (SeatReads). Its proof is k3Leaves_seat's but for the first step.
  k3_calls_left_anyWords, k3_calls_leftItem_anyWords: so the sharp promise and the item are made at
    every accept at the calls' seat: the binders of k3_calls_left_any and k3_calls_leftItem less
    their premise on the words.

Limits. WHOEVER NEEDS THE END VALUES AT THE ROUNDS THAT WERE SHOWN (K3DecideLeaves: the side of the
claims' worth) STILL NEEDS THAT PREMISE: nothing here ties the rounds under "there are" to rs.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Top.H.K3SeatFits
import Johnson.Top.H.FlPort.LkPadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

section
variable {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
  (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))

/-- **The marks of the sumcheck over the leaves, and the shape, behind an accept.** -/
theorem decide_marks (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧
      (OnBytes.PscRun.Sized F → x.1.leaves.started = true ∧ x.1.leaves.rowMade = false ∧
        x.1.leaves.r.size = x.1.leaves.vars.size ∧ ∀ h, p.shape = some h → x.1.shape = h) := by
  obtain ⟨F, F', g, t, hF, hn, hl, e⟩ :=
    decide_lkPad seat piece laid before p guests s s' rs cols hd
  refine ⟨F, (g, F'), hF, hn, e, fun hS => ?_⟩
  obtain ⟨_, _, _, hlaw⟩ := _root_.Fo.Tp.lkPad_law Reading.gl p.calls p.pub p.lid 5 F F' t [] g hl
  obtain ⟨hShape, _, hI⟩ := hlaw hS
  exact ⟨hI.lvFlags.1, hI.lvFlags.2.2, hI.lvSize,
    fun h hsh => shapeOf_unique hShape (shape_some p h hsh)⟩

/-- **WHAT AN ACCEPT LEAVES, AT SOME ROUNDS.** -/
theorem decide_left_some (hr : Desc.K3.SeatReads seat) (h : Forest.Shape)
    (hsh : p.shape = some h) {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ)
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧
      (OnBytes.PscRun.Sized F → ∃ rs' : Rounds K, K3Left ρ h lm F x.2 x.1 rs') := by
  obtain ⟨F, F', g, t, hF, hn, hl, e⟩ :=
    decide_lkPad seat piece laid before p guests s s' rs cols hd
  refine ⟨F, (g, F'), hF, hn, e, fun hSz => ?_⟩
  have hsome : (seat.fork s).isSome = true := by
    rw [hF]
    rfl
  have hg : seat.heard s' = some g := by
    rw [e]
    exact hr _ _ _ hsome hn
  obtain ⟨taken, _, _, hlaw⟩ := _root_.Fo.Tp.lkPad_law ρ p.calls p.pub p.lid lm F F' t [] g hl
  obtain ⟨hShape, hPad, hI⟩ := hlaw hSz
  obtain rfl : g.shape = h := shapeOf_unique hShape (shape_some p h hsh)
  obtain ⟨g1, hg1, -, hx, hy, hkk, hz⟩ :=
    Desc.K3.block_point seat hr piece laid before p guests hd
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans hg1)
  obtain ⟨g2, hg2, hnn⟩ := decide_zk_size seat piece laid before p guests hr s s' rs cols hd
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans hg2)
  obtain ⟨c1, c2⟩ := Fo.Tp.lkPadCEnd _ _ _ _ _ _ _ _ hl hSz
  exact ⟨_,
    { heardIs := hI, padLeft := hPad, shape := rfl, zx := hx, zy := hy, zkSize := hkk, zkRaw := hz,
      zkLen := hnn, eRaw := Fo.Tp.lkPad_e _ _ _ _ _ _ _ _ hl, cEndEnts := c1, cEndFilled := c2 }⟩

end

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **AN ACCEPT MAKES THE SHARP PROMISE, WHATEVER THE ROUNDS' WORDS.** -/
theorem k3_calls_left_anyWords (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hz : OnBytes.PscRun.Sized F) (Q : Fork → Prop)
    (hQ : Q F) :
    K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) h p.lm
      p.first Q s' := by
  obtain ⟨F1, x, hF1, hn, e, hL⟩ :=
    decide_left_some (Desc.K3.seatCalls claim) piece laid before p guests
      (Desc.K3.seatCalls_reads claim) h hs Reading.gl p.lm s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  obtain ⟨rs', L⟩ := hL hz
  refine ⟨F, x.2, x.1, rs', hQ,
    decide_first (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols F hF1 hd, L,
    ?_, ?_⟩
  · show s'.lookHeard? = some x.1
    rw [e]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn
  · show s'.fork? = some x.2
    rw [e]
    exact seatCalls_keeps claim _ _ _ hsome hn

/-- **So it makes the item.** -/
theorem k3_calls_leftItem_anyWords (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F) : k3LeftItem p s' :=
  ⟨⟨h, hs, k3_calls_left_anyWords claim piece laid before p guests s s' rs cols hs hd hF hQ.1 _ hQ⟩,
    k3_calls_leavesBare claim piece laid before p guests s s' rs cols hd hF hQ.1⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_marks
#print axioms VerifiableInference.OnPublicFiles.decide_left_some
#print axioms VerifiableInference.OnPublicFiles.k3_calls_left_anyWords
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leftItem_anyWords
