-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
k3_calls_lookLeft: no state is shown at which its premises hold together.
(The test lookLeftB itself has run at the small stored set: true.)
Johnson/Desc/First/Look/K3CallsLookLeft.lean: the lookup on a layers' link's CALLS: THE MAKER's
LEMMA OF THE PUBLIC ITEM (some m, "K4.lookLeft") (Johnson/Desc/First/FillBare.lean): where the
kind's decide accepts, from a ledger that is sized, has the public parameters' number of slots and
is free from its next slot on, at a place with room for the lookup's scalars, THE TEST lookLeftB IS
TRUE at the verifier's state behind. Statements and proofs. A tie of texts: no error term. NO
SOUNDNESS IS CLAIMED.

Why. The table of joints' promise in front of the calling kind's sub-protocol asks that test; by its
rows the lookup's sub-protocol makes it: so the lookup's kind owes: its accepting makes it.

OBJECT: Desc.K3.block's decide at Desc.K3.seatCalls claim; the Bool FillBare.lookLeftB.
USER: K3CallsLookLeftSeated.lean (k3_calls_lookLeft), K3CallsLeftAt.lean (leftAt_of). Meant: the
  clause of the promise behind the lookup on the calls at a layers' link.
LETTERS: claim, piece, laid, before, p, guests, h, s, s', rs, cols, F free.
Compiled with the whole library.



Main names:
  `named_of`: Named (Johnson/Top/H/Keep/PadNamed.lean) gives the test namedB.
  `vars_of_len`: a sumcheck whose window has a slot has a variable.
  `leftAt_of`: THE SEVEN PARTS of leftAtB g F', from: PadNames g F' (four) · the leaves' sumcheck's
    marks (begun, no row made, as many points as variables) · PadExact h F F' g · the ledger in
    front is sized and free from its next slot on · room.
  `k3_calls_lookLeft`: THE END, at decide.

WHAT IS LEFT, AND WHOSE IT IS. hs, hroom: conjuncts of the kind's test on the public parameters
(P.planOk). hw, hd: the seated piece accepts. hF, hQ: the promise in front (the ledger's items).
hlay: the promise's stand at a layers' link.

Limits. The premises are those of k3_calls_leftItem (Johnson/Desc/First/Look/K3LeftItem.lean), whose
conclusion's body has run true at honest states, with hroom and hlay more. At the kind's own decide:
the step without a round behind it at a layers' link leaves the state (another file's).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.FillBare
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Top.H.Keep.PadExact
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.FillBare (namedB readyB winFreeB leftAtB lookLeftB)

/-- Inside an array the default is not read. -/
theorem lookLeft_getD {α : Type} (a : Array α) (j : ℕ) (h : j < a.size) (d d' : α) :
    a.getD j d = a.getD j d' := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- Named gives the test. -/
theorem named_of {F : Fork} {f : Aff} (h : _root_.Fo.Tp.Named F f) : namedB F f = true := by
  unfold namedB
  rw [Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.2 fun x hx => ?_⟩
  · rw [_root_.Fo.Tp.bare_ents h.1]
    rfl
  · obtain ⟨a, b⟩ := h.filledA x hx
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true a, b⟩

/-- A sumcheck whose window has a slot has a variable. -/
theorem vars_of_len {p : Psc} (h : 0 < p.walk.1.length) : p.vars.isEmpty = false := by
  cases e : p.vars.isEmpty with
  | false => rfl
  | true =>
    have hv : p.vars.toList = [] := by
      have := Array.isEmpty_iff.1 e
      rw [this]
    have h0 : p.walk.1.length = 0 := by
      unfold Psc.walk
      rw [OnBytes.zipT_eq, hv, List.zip_nil_left]
      rfl
    omega

/-- **THE SEVEN PARTS.** -/
theorem leftAt_of {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (N : _root_.Fo.Tp.PadNames g F') (E : _root_.Fo.Tp.PadExact h F F' g)
    (hst : g.leaves.started = true) (hrow : g.leaves.rowMade = false)
    (hsz : g.leaves.r.size = g.leaves.vars.size) (hz : Sized F) (hns : F'.ns = F.ns)
    (hfree : ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false)
    (hroom : F.next + Forest.elems h ≤ F.ns) : leftAtB g F' = true := by
  have hlen := E.len
  have hw1 := E.within
  have hf1 := E.first
  have hnx := E.next
  unfold leftAtB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, named_of N.cEnd⟩, named_of N.sBit⟩, named_of N.start⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.2 fun f hf => named_of (N.rows f hf)
  · unfold readyB
    rw [hrow, hst, vars_of_len (by omega), hsz]
    simp
  · omega
  · unfold winFreeB
    refine List.all_eq_true.2 fun i hi => ?_
    have hi' : i < 1 + 2 * h.d + 5 := by
      rw [← hlen]
      exact List.mem_range.1 hi
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (by omega), ?_⟩
    have hnF : ¬ Filled F (g.leaves.first + i) := by
      intro hc
      have h1 := hfree (g.leaves.first + i) (by omega) (by omega)
      have h2 : F.gotF.getD (g.leaves.first + i) false = F.gotF.getD (g.leaves.first + i) true :=
        lookLeft_getD _ _ (by rw [hz.2.2]; omega) _ _
      unfold Filled at hc
      rw [h2, h1] at hc
      cases hc
    have hnF' : ¬ Filled F' (g.leaves.first + i) := by
      intro hc
      rcases (E.marks _).1 hc with h1 | ⟨-, -, h3⟩
      · exact hnF h1
      · exact h3 ⟨by omega, by omega⟩
    unfold Filled at hnF'
    cases hv : F'.gotF.getD (g.leaves.first + i) false with
    | false => rfl
    | true => exact absurd hv hnF'

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **WHERE THE LOOKUP ON A LAYERS' LINK's CALLS ACCEPTS, "K4.lookLeft" IS MADE.** -/
theorem k3_calls_lookLeft (hs : p.shape = some h) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F)
    (hroom : p.first + Forest.elems h ≤ p.ns) (hlay : ∃ a, s.here = .lay a) :
    lookLeftB s' = true := by
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
  obtain ⟨F0, F', g, rs', -, -, hL, hg, -⟩ :=
    k3_calls_left_any claim piece laid before p guests s s' rs cols hs hw hd hF hQ.1
      (fun _ => True) trivial
  have eg : g = x.1 := Option.some.inj (hg.symm.trans hg1)
  subst eg
  obtain ⟨E, hLat⟩ := hE hQ.1
  rw [ey1, ey2, hL.shape] at E
  rw [ey2] at hLat
  have hnext : F.next = p.first :=
    decide_first (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols F hF1 hd
  have key : leftAtB x.1 x.2 = true :=
    leftAt_of (hN hQ.1) E hL.heardIs.lvFlags.1 hL.heardIs.lvFlags.2.2 hL.heardIs.lvSize hQ.1
      hLat.ns hQ.2.2 (by rw [hnext, hQ.2.1]; exact hroom)
  obtain ⟨a, ha⟩ := hlay
  rcases (k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).sort with
    ⟨-, a', -, ha'⟩ | ⟨b, -, hb, -⟩ | ⟨b, -, hb, -⟩
  · have k1 : a'.lookHeard = some x.1 := by
      have := hg1
      unfold Desc.First.S.lookHeard? at this
      rw [ha'] at this
      exact this
    have k2 : a'.F = x.2 := by
      have := hf1
      unfold Desc.First.S.fork? at this
      rw [ha'] at this
      exact Option.some.inj this
    unfold lookLeftB
    rw [ha']
    show a'.lookHeard.any (fun g => leftAtB g a'.F) = true
    rw [k1, k2]
    exact key
  · rw [ha] at hb
    cases hb
  · rw [ha] at hb
    cases hb

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.leftAt_of
#print axioms VerifiableInference.OnPublicFiles.k3_calls_lookLeft
