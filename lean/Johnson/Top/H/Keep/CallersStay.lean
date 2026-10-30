-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/CallersStay.lean: The kind "lookup" (K3): WHAT THE RUNS OF THE LOOKUP ON THE
CALLS ASK AT THE STATE IN FRONT OF THE LOOKUP ON THE DIGITS, AND ACROSS IT: (1) the output head's
relation SamePlanes (Johnson/Desc/Kinds/Law/PlanesStay.lean)
holds across an accept of the digits' decision and across the lookup's runs "objects" and
"guests"; (2) so the output head's readers of the planes' matrix answer the same at both states;
(3) the window of the sumcheck over the leaves is free, in the room and below the next slot, from
the two items on the lookup on the calls that are open there. Statements and proofs: joinings.

OBJECT: K3.block's decide at K3.seatDigits; objectsRun, guestsRun; Kinds.Head.planesAt,
  Kinds.Head.callerReaders; K3.k3OnOut; k3LeftOnItem.
USER: Johnson/Top/H/Keep/HeadHoleFwd.lean (k3_digits_samePlanes, headReaders_same, hwin_of_onOut);
  Johnson/Desc/First/Look/K3DigitsCallersStay.lean (k3_digits_samePlanes, headReaders_same);
  Johnson/Desc/Sound/MgAt/K3DigitsFormsPlanes.lean (hwin_of_onOut); 4 more files.
  Meant: the premises hread (at the head's link) and hwin of planes_formsIn_pass'
  (Johnson/Top/H/Keep/FormsPassOurs.lean); four of the items that PlanesStay.lean's head books as
  owed by each kind's own files.
LETTERS: claim, piece, laid, before, p, guests, s, s', rs, cols, seat, iU3, pc, F, G free.
Compiled with the whole library.

Main names:
  k3_digits_samePlanes, objects_samePlanes, guests_samePlanes: (1).
  planesAt_same, headReaders_same: (2): in the head's link, from SamePlanes and the ledgers' arrays.
  k3_digits_headReaders: (2) across an accept of the digits' decision.
  hwin_of_onOut: (3).

Limits. (1), (2): OVER THE DECISION's OWN ACCEPT: the step without a round behind the digits'
rounds is not crossed here (SamePlanes.trans and planesAt_same carry it, once that step is shown to
keep SamePlanes and the arrays). (3) reads lookOut's test (k3OnOut) for the window and the sentence
"what the lookup on the calls left", in the form that stands at every later state, for the walk's
length alone.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3PassOf
import Johnson.Top.H.Keep.K3LeftWindow
import Johnson.Top.H.Keep.K3Block
import Johnson.Desc.Kinds.Law.PlanesStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K3 (Seat seatDigits freeB k3OnOut)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law (SamePlanes same_putFork same_putTl)

/-! ## (1) SamePlanes -/

/-- **An accept of the digits' decision keeps what the law on "planes" reads.** -/
theorem k3_digits_samePlanes {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : SamePlanes s s' := by
  obtain ⟨F, G, g, tl, _, htl, e, _⟩ :=
    k3_digits_footprint claim piece laid before p guests s s' rs cols hd
  rw [e]
  have h1 : SamePlanes s (s.putTl { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some g }) :=
    same_putTl s htl rfl rfl rfl rfl
  exact h1.trans (same_putFork _ G)

/-- So does the run "objects". -/
theorem objects_samePlanes (seat : Seat S Claim) (hA : AtS2 seat) {n : ℕ} {s t : S}
    {cl : List Claim} (h : objectsRun seat n s = .ok (cl, t)) : SamePlanes s t := by
  obtain ⟨F, g, _, _, rfl⟩ := objects_cut seat h
  rw [hA.mark]
  exact same_putFork s _

/-- And the run "guests". -/
theorem guests_samePlanes (guests : List (Desc.First.Look.Guest S Claim)) {n : ℕ} {s t : S}
    {cl : List Claim} (h : guestsRun guests n s = .ok (cl, t)) : SamePlanes s t := by
  obtain rfl : t = s := guests_same guests s t ⟨n, cl, h⟩
  exact SamePlanes.refl t

/-! ## (2) The output head's readers -/

theorem planesAt_same {s s' : S} (a : SamePlanes s s') {o : HeadOwn} (ho : s.here = .head o)
    {F G : Fork} (hF : s.fork? = some F) (hG : s'.fork? = some G) (ht : G.trees = F.trees)
    (iU3 : ℕ) : planesAt iU3 s' = planesAt iU3 s := by
  obtain ⟨o', ho', _, _, e3, _⟩ := a.head o ho
  unfold planesAt
  rw [ho, ho', hF, hG]
  simp only [e3, ht]

theorem headReaders_same {s s' : S} (a : SamePlanes s s') {o : HeadOwn} (ho : s.here = .head o)
    {F G : Fork} (hF : s.fork? = some F) (hG : s'.fork? = some G) (ht : G.trees = F.trees)
    (iU3 : ℕ) : callerReaders (planesAt iU3) s' = callerReaders (planesAt iU3) s := by
  unfold callerReaders
  rw [planesAt_same a ho hF hG ht iU3]

/-- **The head's readers across an accept of the digits' decision.** -/
theorem k3_digits_headReaders {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {o : HeadOwn} (ho : s.here = .head o) {F : Fork} (hF : s.fork? = some F) (hS : Sized F)
    (iU3 : ℕ) : callerReaders (planesAt iU3) s' = callerReaders (planesAt iU3) s := by
  obtain ⟨G, P⟩ := k3_digits_pass claim piece laid before p guests s s' rs cols hd hF hS
  exact headReaders_same (k3_digits_samePlanes claim piece laid before p guests s s' rs cols hd)
    ho hF P.behind P.trees iU3

/-! ## (3) The window -/

/-- **The window of the sumcheck over the leaves, at a state at which the two items on the lookup on
the calls are open.** -/
theorem hwin_of_onOut {pc : Desc.First.Look.P} (hdc : pc.digits = false) {s : S} {F : Fork}
    (hF : s.fork? = some F) (hO : k3OnOut pc s = true) (hL : k3LeftOnItem pc s) :
    ∀ g, s.lookHeard? = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j := by
  intro g hg
  obtain ⟨⟨h, hs, F0, F', G, g0, rs, _, _, K, hg0, _, _, _⟩, _⟩ := hL
  obtain rfl : g0 = g := Option.some.inj (hg0.symm.trans hg)
  have hlen : lvLen g0 = 1 + 2 * h.d + 5 := left_len K
  have hH : Desc.K3.heardAt pc.digits s = some g0 := by
    rw [hdc]
    exact hg
  unfold k3OnOut at hO
  rw [hs, hH, hF] at hO
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hO
  obtain ⟨⟨⟨⟨⟨⟨⟨_, c7⟩, _⟩, c9⟩, _⟩, c11⟩, _⟩, _⟩ := hO
  obtain ⟨f1, f2⟩ := (freeB_iff F g0.leaves.first (1 + 2 * h.d + 5)).1 c9
  rw [hlen]
  refine ⟨Nat.le_trans c11 c7, f1, fun j h1 h2 hc => ?_⟩
  have q := getD_in _ _ (f2 (j - g0.leaves.first) (by omega))
  rw [show g0.leaves.first + (j - g0.leaves.first) = j by omega] at q
  unfold Filled at hc
  rw [q] at hc
  cases hc

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_samePlanes
#print axioms VerifiableInference.OnPublicFiles.objects_samePlanes
#print axioms VerifiableInference.OnPublicFiles.guests_samePlanes
#print axioms VerifiableInference.OnPublicFiles.k3_digits_headReaders
#print axioms VerifiableInference.OnPublicFiles.hwin_of_onOut
