-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttInst.lean: THE CALLS' END THEOREM AT AN ATTENTION LINK OF A PUBLIC
RECORD: the place, the sub-proof's shape and the plan's record of the smallness test are no letters:
they are functions of the public record X and the link's number i. After the pattern of
k3_digits_goodIn_at (Johnson/Desc/First/Look/K3DigitsRounds.lean). And the theorem at an empty list
of guests. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names:
  `attAt X i`: link i's place on the calls, the lookup's record laid anew as the one that the kind's
    own parameters make; the verifier's record of the sub-proof's shape; the plan's record tl. None
    where link i is no attention link.
  `attAt_shape`: there AttOK's first field holds. `attOK_at`: with the four others: AttOK.
  `attRiderAt_of`: the caller's own attRiderAt is there at the same link, shape and tl, at the place
    of which attAt's is the copy with the lookup's record laid anew.
  `k3_att_goodIn_at`: THE INSTANCE.
  `k3_att_noGuests`: the end theorem at guests := []: the text's guests are not what brings the
    rider in.

Limits. Those of K3AttRounds.lean. attAt IS NOT attRiderAt's READING TO THE LETTER
(Johnson/Desc/First/Look/K3CallerAtt.lean): that one takes the PLAN's own record x.fs; attAt lays
the record that the kind's parameters make in its place, as the digits' digAt does; that the two
have the same numbers is a test that is run (sameNums); at a record that publicOf returns the two
records are one (att_shape, Johnson/Desc/First/Look/K3CallerAtPlan.lean). D and rad stay letters.
THAT THE PLANES' CELLS LIE IN THE LIST's MATRIX (planesAtB,
Johnson/Desc/First/Look/K3CallerCellsIn.lean) IS ASKED BY NO PREMISE HERE: it stands beside the four
tests; at a record that publicOf returns it is had by planesAtB_att
(Johnson/Desc/First/Look/K3CallerCellsLaw.lean), spent in Johnson/Desc/First/Look/K3AttPublic.lean.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- Link i's place on the calls, the sub-proof's shape, the plan's record of its smallness test. -/
def attAt (X : Verify.Public) (i : Nat) : Option (Place × Attention.Shape × HTailF2) :=
  if X.p4 = true ∧ i % 2 = 1 then
    (lookAt X i false).bind fun x => (X.A[i / 2]?).bind fun a =>
      (P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h =>
        ({ x with fs := h }, a.S, a.seam.tl)
  else none

/-- There the kind's own parameters make the place's record. -/
theorem attAt_shape {X : Verify.Public} {i : ℕ} {x : Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X i = some (x, A, tl)) :
    (P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs := by
  unfold attAt at hx
  split at hx
  · obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, -⟩ := Prod.mk.inj hx
    exact hh
  · cases hx

/-- **The caller's own attRiderAt is there too, at the same link, shape and tl**, at the place x' of
which x is the copy with the lookup's record laid anew. -/
theorem attRiderAt_of {X : Verify.Public} {i : ℕ} {x : Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X i = some (x, A, tl)) (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec)
    (Wp : Type) :
    ∃ x', lookAt X i false = some x' ∧ x = { x' with fs := x.fs } ∧
      attRiderAt X D rad i Ex Wp = some (attRider x' A tl D rad Ex Wp) := by
  unfold attAt at hx
  split at hx
  · rename_i hc
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, h2, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, e0⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨e1, e2⟩ := Prod.mk.inj e0
    obtain ⟨e3, e4⟩ := Prod.mk.inj e2
    subst e1 e3 e4
    refine ⟨x', h1, rfl, ?_⟩
    unfold attRiderAt
    rw [if_pos hc, h1, Option.bind_some, h2, Option.map_some]
  · cases hx

/-- **At a link of the public record four tests are all that AttOK asks**; the planes' cells
(planesAtB) are a fifth, beside it. -/
theorem attOK_at {X : Verify.Public} {i : ℕ} {x : Place} {A : Attention.Shape} {tl : HTailF2}
    (D : Sent) (rad : OracleShape → Nat) (hx : attAt X i = some (x, A, tl)) (h4 : x.fs.NC = 4)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true) (hf : attFitsB A x.fs = true)
    (hm : x.F.next + FoNums.nMasks x.fs ≤ x.ns) :
    AttOK (Params.settingOf X.P.frame) x A tl D rad := ⟨attAt_shape hx, h4, hp, hf, hm⟩

end VerifiableInference.Desc.First.Look

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)

/-- **THE INSTANCE: at attention link i of a public record X.** -/
theorem k3_att_goodIn_at {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place}
    {A : Attention.Shape} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
    (hx : attAt X i = some (x, A, tl)) (h4 : x.fs.NC = 4)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true) (hf : attFitsB A x.fs = true)
    (hm : x.F.next + FoNums.nMasks x.fs ≤ x.ns)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hr : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [attRider x A tl D rad extNone Unit]).ε
      (attRider x A tl D rad extNone Unit)) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) guests).decide s rs cols =
        .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_att_goodIn_same G seatT arr smp claim piece laid before guests p hb hback hext
    (attOK_at D rad hx h4 hp hf hm) hr hR hε hsmp hseat σ₀

variable {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

/-- **The end theorem at an empty list of guests**: the same four relations, the fourth item of the
row out and at3 in front among them: the text's guests are not what brings the rider in. -/
theorem k3_att_noGuests (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) []))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [attRider x A tl D rad extNone Unit]).ε
      (attRider x A tl D rad extNone Unit)) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) []).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_att_goodIn_same G seatT arr smp claim piece laid before [] p hb hback hext H hr hR hε hsmp
    hseat σ₀

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.First.Look.attRiderAt_of
#print axioms VerifiableInference.Desc.First.Look.attOK_at
#print axioms VerifiableInference.OnPublicFiles.k3_att_goodIn_at
#print axioms VerifiableInference.OnPublicFiles.k3_att_noGuests
