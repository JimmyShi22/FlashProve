-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/AttCallersStay.lean: The kind "lookup" (K3): IN AN ATTENTION LINK, WHAT THE
CALLING KIND HANDS THE RUNS "planes" AND "join" OF THE LOOKUP ON THE CALLS (its readers of the
planes' matrix, readersOfO; its key forms, keysOfO: Johnson/Desc/First/Att/SeatO.lean) IT HANDS
THEM BEHIND AN ACCEPT OF THE DIGITS' DECISION TOO: what they answered in front they answer behind.
Statements and proofs: JOININGS OVER THE ATTENTION KIND's OWN LEMMAS
(Johnson/Desc/First/Att/Claims/LeftLater.lean: inOf_mono, keysOfK_mono, shownLe_of_later;
Johnson/Desc/First/Att/SeatOAgrees.lean: seatCO_eq): nothing of that kind's text is unfolded here
but readersOfK's one line.

OBJECT: Att.P.readersOfO, Att.P.keysOfO; K3.block's decide at K3.seatDigits.
USER: Johnson/Desc/First/Look/K3DigitsCallersStay.lean (attReaders_fwd, attKeys_fwd);
  Johnson/Top/H/Keep/AttOwnSame.lean (k3_digits_attSame).
  Meant: the premises hread and hkeys of planes_formsIn_pass' and join_formsIn_pass'
  (Johnson/Top/H/Keep/FormsPassOurs.lean) at an attention link.
LETTERS: A, s, s', a, a' free; claim, piece, laid, before, p, guests, rs, cols: the digits'.
Compiled with the whole library.

Main names:
  attReaders_fwd, attKeys_fwd: between two states in an attention link with the same g and heard5,
    whose ledgers show alike (ShownLe) and have the same widths.
  att_put: the state behind the digits' put, in an attention link.
  k3_digits_attReaders, k3_digits_attKeys: ACROSS AN ACCEPT OF THE DIGITS' DECISION.

Limits. ONE-SIDED: from an answer in front: a reader that refuses at a free slot may speak behind.
OVER THE DECISION's OWN ACCEPT: the step without a round behind the digits' rounds is crossed by
attReaders_fwd | attKeys_fwd once more, at that step's two states.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3PassOf
import Johnson.Desc.First.Att.Claims.LeftLater
import Johnson.Desc.First.Att.SeatOAgrees
import Johnson.Desc.First.Att.Guest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.First (S AttOwn)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO readersOfK seatCO seatCH seatCO_eq
  parCOf)
open VerifiableInference.Desc.K3 (seatDigits)
open K5Law (ShownLe shownLe_of_later inOf_mono keysOfK_mono widths)

section
variable (A : Attention.Plan) {s s' : S} {a a' : AttOwn} (hs : s.here = .att a)
  (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5)
  (H : ShownLe a.F a'.F) (hw : widths a'.F = widths a.F)
include hs hs' hg h5 H hw

/-- **The readers of the planes' matrix answer at s' what they answered at s.** -/
theorem attReaders_fwd (r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff))
    (e : readersOfO A s = some r) : readersOfO A s' = some r := by
  unfold readersOfO readersOfK at e ⊢
  rw [seatCO_eq] at e ⊢
  obtain ⟨x, hx, hr⟩ := Option.map_eq_some_iff.1 e
  rw [inOf_mono (parCOf A) hs hs' hg h5 H hw hx]
  exact congrArg some hr

/-- **So do the key forms.** -/
theorem attKeys_fwd (KF : Array Aff) (e : keysOfO A s = some KF) : keysOfO A s' = some KF := by
  unfold keysOfO at e ⊢
  rw [seatCO_eq] at e ⊢
  exact keysOfK_mono (parCOf A) hs hs' hg h5 H hw e

end

/-- The state behind the digits' put, in an attention link. -/
theorem att_put {s : S} {a : AttOwn} (hs : s.here = .att a) (tl : HTailF2) (G : Fork) :
    ((s.putTl tl).putFork G).here = .att { a with tl := tl, F := G } := by
  simp [S.putTl, S.putFork, hs]

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
  (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
  (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s')
  {a : AttOwn} (hs : s.here = .att a) (hS : Sized a.F)
include hd hs hS

/-- What the two lemmas above ask, across an accept of the digits' decision. -/
theorem k3_digits_attSame :
    ∃ a', s'.here = .att a' ∧ a'.g = a.g ∧ a'.heard5 = a.heard5 ∧ ShownLe a.F a'.F ∧
      widths a'.F = widths a.F := by
  obtain ⟨F, G, g, tl, hF, _, e, hL⟩ :=
    k3_digits_footprint claim piece laid before p guests s s' rs cols hd
  have hFa : F = a.F := by
    have h0 : s.fork? = some a.F := by simp [S.fork?, hs]
    exact Option.some.inj (hF.symm.trans h0)
  subst hFa
  have Q := hL hS
  refine ⟨{ a with
    tl := { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := a.F.next, slotB := G.next, heard := some g }
    F := G }, by rw [e]; exact att_put hs _ G, rfl, rfl, ?_, ?_⟩
  · exact shownLe_of_later ⟨Q.later.next, Q.later.ns, fun _ => Q.sized, Q.later.keep⟩
  · show widths G = widths a.F
    unfold widths
    rw [Q.trees]

/-- **The attention kind's readers across an accept of the digits' decision.** -/
theorem k3_digits_attReaders (A : Attention.Plan) :
    ∀ r, readersOfO A s = some r → readersOfO A s' = some r := by
  obtain ⟨a', h1, h2, h3, h4, h5⟩ :=
    k3_digits_attSame claim piece laid before p guests s s' rs cols hd hs hS
  exact attReaders_fwd A hs h1 h2 h3 h4 h5

/-- **Its key forms across an accept of the digits' decision.** -/
theorem k3_digits_attKeys (A : Attention.Plan) :
    ∀ KF, keysOfO A s = some KF → keysOfO A s' = some KF := by
  obtain ⟨a', h1, h2, h3, h4, h5⟩ :=
    k3_digits_attSame claim piece laid before p guests s s' rs cols hd hs hS
  exact attKeys_fwd A hs h1 h2 h3 h4 h5

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attReaders_fwd
#print axioms VerifiableInference.OnPublicFiles.attKeys_fwd
#print axioms VerifiableInference.OnPublicFiles.k3_digits_attReaders
#print axioms VerifiableInference.OnPublicFiles.k3_digits_attKeys
