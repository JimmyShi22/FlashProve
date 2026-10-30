-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which the premises of k3_calls_leftAt
hold together.
Johnson/Desc/First/Look/K3CallsLeftAt.lean: the lookup on a link's CALLS: WHERE THE KIND's decide
ACCEPTS, FROM A LEDGER THAT IS SIZED, HAS THE PUBLIC PARAMETERS' NUMBER OF SLOTS AND IS FREE FROM
ITS NEXT SLOT ON, THE TEST leftAtB (Johnson/Desc/First/FillBare.lean) IS TRUE OF WHAT WAS HEARD AND
OF THE LEDGER BEHIND: AT EVERY SORT OF LINK, WITHOUT A PREMISE ON ROOM, AND WITHOUT A PREMISE ON THE
ROUNDS' WORDS. Statements and proofs. A tie of texts: no error term. NO SOUNDNESS IS CLAIMED.

Why. k3_calls_lookLeft (Johnson/Desc/First/Look/K3CallsLookLeft.lean) ends in lookLeftB, which reads
a layers' link alone, and asks hroom: the place has room for the lookup's scalars. leftAtB itself is
general in what was heard and the ledger. And the room follows from the accept: the lookup's last
slot is filled behind it, so it is there (left_room, Johnson/Top/H/Keep/K3LeftWindow.lean). It also
asks that each word of the rounds is below the prime, which cannot be paid along a fold of
sub-protocols; what it draws from that premise is had without it (k3_calls_left_anyWords,
Johnson/Top/H/Keep/K3LeftAnyWords.lean).

OBJECT: Desc.K3.block's decide at Desc.K3.seatCalls claim; the Bool FillBare.leftAtB.
USER: K03LeftQ.lean, K3CallsMade.lean (k3_calls_leftAt).
  Meant: "leftAtB holds of what was heard and the ledger" at the states reached
  behind the lookup on the calls, at a layers' or an attention link.
LETTERS: claim, piece, laid, before, p, guests, h, s, s', rs, cols, F free.
Compiled with the whole library.

Main names:
  leftAt_of_left: leftAt_of (K3CallsLookLeft.lean) with its marks, its hns and ITS hroom paid by
    K3Left.
  k3_calls_leftAt: THE END, at decide. A SISTER OF k3_calls_lookLeft WITH A SHARED STRETCH OF PROOF:
    its first 35 lines are that proof's, and its conclusion is that proof's inner step "key". The
    clean form is k3_calls_lookLeft as its corollary: left for a later turn of that file.

WHAT IS LEFT, AND WHOSE IT IS. hs: a conjunct of the kind's test on the public parameters. hd: the
decision accepts. hF, hQ: of the ledger in front: it is sized, has the public parameters' number of
slots (THE DECISION DOES NOT TEST THAT NUMBER) and is free from its next slot on.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsLookLeft
import Johnson.Top.H.Keep.K3LeftWindow
import Johnson.Top.H.Keep.K3LeftAnyWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.FillBare (leftAtB)

/-- **The seven parts, the room paid.** -/
theorem leftAt_of_left {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : Forest.Shape}
    {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds K}
    (L : K3Left ρ h lm F F' g rs) (N : _root_.Fo.Tp.PadNames g F')
    (E : _root_.Fo.Tp.PadExact h F F' g) (hz : Sized F)
    (hfree : ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false) : leftAtB g F' = true :=
  leftAt_of N E L.heardIs.lvFlags.1 L.heardIs.lvFlags.2.2 L.heardIs.lvSize hz L.padLeft.rest.2.1
    hfree (by
      rw [← L.padLeft.rest.2.1]
      exact left_room L)

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **WHERE THE LOOKUP ON A LINK's CALLS ACCEPTS, leftAtB IS TRUE BEHIND IT.** -/
theorem k3_calls_leftAt (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F) :
    ∃ g F', s'.lookHeard? = some g ∧ s'.fork? = some F' ∧ leftAtB g F' = true := by
  obtain ⟨F1, x, hF1, hn, e, hN⟩ :=
    decide_named (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  obtain ⟨F2, y, hF2, -, e2, hE⟩ :=
    decide_exact (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F2 := Option.some.inj (hF.symm.trans hF2)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : s'.lookHeard? = some x.1 := by
    rw [e]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn
  have hf1 : s'.fork? = some x.2 := by
    rw [e]
    exact seatCalls_keeps claim _ _ _ hsome hn
  have hg2 : s'.lookHeard? = some y.1 := by
    rw [e2]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn
  have hf2 : s'.fork? = some y.2 := by
    rw [e2]
    exact seatCalls_keeps claim _ _ _ hsome hn
  have ey1 : y.1 = x.1 := Option.some.inj (hg2.symm.trans hg1)
  have ey2 : y.2 = x.2 := Option.some.inj (hf2.symm.trans hf1)
  obtain ⟨F0, F', g, rs', -, h0, hL, hg, hf'⟩ :=
    k3_calls_left_anyWords claim piece laid before p guests s s' rs cols hs hd hF hQ.1
      (fun _ => True) trivial
  have eg : g = x.1 := Option.some.inj (hg.symm.trans hg1)
  have eF : F' = x.2 := Option.some.inj (hf'.symm.trans hf1)
  subst eg
  subst eF
  obtain ⟨E, hLat⟩ := hE hQ.1
  rw [ey1, ey2, hL.shape] at E
  rw [ey2] at hLat
  have hnext : F.next = p.first :=
    decide_first (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols F hF1 hd
  have hroom : F.next + Forest.elems h ≤ F.ns := by
    have r := left_room hL
    rw [h0, hLat.ns] at r
    rw [hnext]
    exact r
  exact ⟨x.1, x.2, hg1, hf1,
    leftAt_of (hN hQ.1) E hL.heardIs.lvFlags.1 hL.heardIs.lvFlags.2.2 hL.heardIs.lvSize hQ.1
      hLat.ns hQ.2.2 hroom⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.leftAt_of_left
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leftAt
