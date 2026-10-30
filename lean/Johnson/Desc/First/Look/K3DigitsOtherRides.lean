-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsOtherRides.lean: the lookup on the digits of a link's smallness
test: THE PROMISE BEHIND THE LINK's OTHER LOOKUP (k3OnOut at a place with digits = false,
Johnson/Desc/First/Look/K3Borders.lean) RIDES OVER A YES OF THE DIGITS' BLOCK. Facts on the block's
text: no premise on a filling, no letter of the table of joints. Statements and proofs. A tie: no
error term.

Why. Behind the digits' block the public item lookOut of the table of joints,
that of the lookup on the calls, is still open: it reads what that lookup heard and the
ledger, which the digits' yes turns. SameBut (K3CallsTurns.lean) says nothing of either.

Main names.
  putDigits_look: what the digits' seat lays leaves what the lookup on the calls heard, where a
    ledger is open.
  freeB_below: a stretch of free slots that ends at or below the ledger's next slot in front is free
    behind a hearing (by PadExact.marks, Johnson/Top/H/Keep/PadExact.lean).
  k3OnOut_other_rides: THE END, at decide.
OBJECT. Desc.K3.block's decide at Desc.K3.seatDigits; the Bool Desc.K3.k3OnOut at a place pc with
pc.digits = false.
USER. K3DigitsSeatedLeaves.lean and K3DigitsStep.lean call putDigits_look and k3OnOut_other_rides.
LETTERS. claim, piece, laid, before, p, guests (the digits' block's); pc (the other lookup's place):
free; NOTHING TIES pc TO p: the theorem holds at every pc with digits = false at which k3OnOut holds
in front.
IS IT EMPTY? Its two premises are a yes of decide and a Bool. The Bool: an evaluation that came with
K3Borders.lean found k3OnOut true «behind each place of K3 and at every later border of
its link up to the front of the batching»: 37 of 37 borders of the small stored set, 177 of 177 of
the full-size one, in another build: by these words the border in front of the digits' block is
among them. A yes of decide there is what an accepted proof gives. NOT TRIED BY US, AND NOT BOTH IN
ONE RUN.
Compiled with the whole library.

Limits. Over the block's own yes alone: the step without a round that stands behind the digits'
rounds is not crossed here. Nothing where decide refuses.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OnOutOfLeft
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-- What the digits' seat lays leaves what the lookup on the calls heard. -/
theorem putDigits_look {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatDigits claim).fork s = some F) :
    ((Desc.K3.seatDigits claim).put s g Gk).lookHeard? = s.lookHeard? := by
  simp only [Desc.K3.seatDigits] at hF ⊢
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a =>
    simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
      Desc.First.S.lookHeard?, hh]
  | att a =>
    simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
      Desc.First.S.lookHeard?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true =>
      simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
        Desc.First.S.lookHeard?, hh, ho]

/-- Free slots below the ledger's next slot stay free behind a hearing. -/
theorem freeB_below {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (E : Fo.Tp.PadExact h F F' g) (hns : F'.ns = F.ns) (hz : Sized F') (first n : ℕ)
    (hb : first + n ≤ F.next) (hfree : freeB F first n = true) : freeB F' first n = true := by
  obtain ⟨f1, f2⟩ := (freeB_iff F first n).1 hfree
  refine (freeB_iff F' first n).2 ⟨by rw [hns]; exact f1, fun j hj => ?_⟩
  have hin : first + j < F'.gotF.size := by
    rw [hz.2.2, hns]
    omega
  refine getD_out _ _ hin ?_
  have hF : ¬ Filled F (first + j) := by
    intro hc
    have q' := getD_in _ _ (f2 j hj)
    unfold Filled at hc
    rw [q'] at hc
    cases hc
  have hF' : ¬ Filled F' (first + j) := by
    intro hc
    rcases (E.marks _).1 hc with h1 | ⟨h2, -, -⟩
    · exact hF h1
    · omega
  unfold Filled at hF'
  cases hv : F'.gotF.getD (first + j) false with
  | false => rfl
  | true => exact absurd hv hF'

/-- **The other lookup's promise behind rides over a yes of the digits' block.** -/
theorem k3OnOut_other_rides {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (pc : Desc.First.Look.P)
    (hdc : pc.digits = false) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') (hO : k3OnOut pc s = true) : k3OnOut pc s' = true := by
  obtain ⟨F, y, hF, hn, e, hE⟩ :=
    decide_exact (Desc.K3.seatDigits claim) piece laid before p guests s s' rs cols hd
  have hF0 : s.fork? = some F := hF
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have hF' : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have hL : heardAt pc.digits s' = heardAt pc.digits s := by
    rw [hdc, e]
    show ((Desc.K3.seatDigits claim).put s y.1 y.2).lookHeard? = s.lookHeard?
    exact putDigits_look claim s y.1 F y.2 hF
  unfold k3OnOut at hO ⊢
  rw [hF', hL]
  rw [hF0] at hO
  cases hs : pc.shape with
  | none =>
    rw [hs] at hO
    cases hO
  | some h₀ =>
    cases hg : heardAt pc.digits s with
    | none =>
      rw [hs, hg] at hO
      cases hO
    | some g =>
      rw [hs, hg] at hO
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hO ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨c16, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := hO
      have hz : Sized F := by
        simp only [sizedB, Bool.and_eq_true, beq_iff_eq] at c8
        exact ⟨c8.1.1, c8.1.2, c8.2⟩
      obtain ⟨E, hLat⟩ := hE hz
      have hz' : Sized y.2 := hLat.sized hz
      refine ⟨⟨⟨⟨⟨⟨⟨c16, ?_⟩, sizedB_of hz'⟩, ?_⟩, c10⟩, c11⟩, c12⟩, c13⟩
      · rw [E.next]
        omega
      · exact freeB_below E hLat.ns hz' _ _ (by omega) c9

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.putDigits_look
#print axioms VerifiableInference.OnPublicFiles.freeB_below
#print axioms VerifiableInference.OnPublicFiles.k3OnOut_other_rides
