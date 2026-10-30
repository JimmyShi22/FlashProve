--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS AT ANY REAL PLACE.
Johnson/Top/H/Keep/DigitsHeardFacts.lean: The kind "lookup" (K3), at the lookup on the approximate
range proof's digits: WHAT STANDS OF WHAT ITS VERIFIER HAS HEARD (g) BEHIND AN ACCEPT OF ITS
DECISION, FROM THE TESTS ON THE PUBLIC PARAMETERS (DigOK) AND THE ACCEPT ALONE: g has the
parameters' shape; 5 ≤ kT + cK; each of the two calls' points has as many coordinates as the call
has variables; the sumcheck over the leaves starts from a form that names no entry; the form left
for the join names no entry, and every slot that it names is filled in the ledger left. Statements
and proofs: joinings.

OBJECT: K3.block's decide at K3.seatDigits, at the place's own parameters P.ofPlace set true x.
USER: nobody yet. Meant: the fields shape, five, points of another house's structure DigitsRest
  (Johnson/Desc/First/Link/Law/WorthAtFront.lean).
LETTERS: claim, piece, laid, before, guests, set, x, tl, D, rad, pp, s, s', rs, cols, F free; tlS:
  the approximate range proof's parameters at a later state.

Main names:
  digits_heard_facts: the seven, at tl.
  zOf_same: SameDig keeps the two calls.
  digits_rest_heard: shape, five, points IN THAT STRUCTURE's OWN TEXT, at any tlS with SameDig tl
    tlS.
  dig_c0: each piece's first column is its call's (the premise hc0 of rest_pays,
    Johnson/Top/H/Keep/DigitsRestPays.lean): from DigOK.

Limits. AT THE STATE BEHIND THE DECISION's OWN ACCEPT: that what was heard is still g at a later
state is whoever calls's. Sized F is a premise.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.Top.H.Keep.K3Named
import Johnson.Desc.First.Look.K3DigRows
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (DigOK dig_foOk Sent)
open VerifiableInference.Desc.K3 (seatDigits seatDigits_reads)

section
variable {set : Params.Setting} {x : Desc.First.Look.Place} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → ℕ} {pp : ℕ}

/-- Each piece's first column is its call's. -/
theorem dig_c0 (HD : DigOK set x tl D rad pp) :
    ∀ q < 2, ∀ p ∈ piecesL tl q, p.c0 = q * tl.mz := by
  obtain ⟨_, TO, PO⟩ := shape2_parts HD.tail
  intro q hq p hp
  exact (PO.held q (by rw [TO.nc]; exact hq) p hp).2.2

/-- **WHAT STANDS OF WHAT WAS HEARD.** -/
theorem digits_heard_facts {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest S Cl))
    (HD : DigOK set x tl D rad pp) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) :
    ∃ g G, (seatDigits claim).heard s' = some g ∧ s'.fork? = some G ∧ tl.f9 = g.shape ∧
      5 ≤ g.shape.kT + g.shape.cK ∧
      (∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n) ∧
      g.leaves.start.ents = #[] ∧ g.cEnd.ents = #[] ∧ _root_.Fo.FilledA G g.cEnd := by
  obtain ⟨F0, y, hF0, hn, e, hL⟩ := decide_left_some (seatDigits claim) piece laid before
    (Desc.First.Look.P.ofPlace set true x) guests (seatDigits_reads claim) tl.f9 HD.shape
    Reading.gl 5 s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
  obtain ⟨rs', K⟩ := hL hS
  obtain ⟨F1, y', hF1, _, e', hN⟩ := decide_named (seatDigits claim) piece laid before
    (Desc.First.Look.P.ofPlace set true x) guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((seatDigits claim).fork s).isSome = true := by
    rw [hF0]
    rfl
  have hg : (seatDigits claim).heard s' = some y.1 := by
    rw [e]
    exact seatDigits_reads claim s y.1 y.2 hsome hn
  have hg' : (seatDigits claim).heard s' = some y'.1 := by
    rw [e']
    exact seatDigits_reads claim s y'.1 y'.2 hsome hn
  have hy : y'.1 = y.1 := Option.some.inj (hg'.symm.trans hg)
  have hG : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim s y.1 y.2 hsome hn
  obtain ⟨_, TO, PO⟩ := shape2_parts HD.tail
  refine ⟨y.1, y.2, hg, hG, K.shape.symm, ?_, ?_, ?_, K.cEndEnts, K.cEndFilled⟩
  · rw [K.shape]
    exact _root_.Fo.port_five PO (dig_foOk HD)
  · intro q hq
    have hq' : q < tl.f9.NC := by
      rw [TO.nc]
      exact hq
    exact (K.zkLen q hq').trans (PO.call q hq').1
  · rw [← hy]
    exact _root_.Fo.Tp.bare_ents (hN hS).start.1

end

/-- SameDig keeps the two calls. -/
theorem zOf_same {tl tlS : HTailF2} (h : SameDig tl tlS) (q : ℕ) : tlS.zOf q = tl.zOf q := by
  unfold HTailF2.zOf
  rw [h.z1, h.z2]

/-- **shape, five, points**, at the parameters of a later state. -/
theorem digits_rest_heard {tl tlS : HTailF2} {g : Forest.Heard} (h : SameDig tl tlS)
    (h1 : tl.f9 = g.shape) (h2 : 5 ≤ g.shape.kT + g.shape.cK)
    (h3 : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n) :
    tlS.f9 = g.shape ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
      ∀ q < 2, (g.zk.getD q #[]).size = (tlS.zOf q).call.n :=
  ⟨h.f9.trans h1, h2, fun q hq => by rw [zOf_same h q]; exact h3 q hq⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.dig_c0
#print axioms VerifiableInference.OnPublicFiles.digits_heard_facts
#print axioms VerifiableInference.OnPublicFiles.digits_rest_heard
