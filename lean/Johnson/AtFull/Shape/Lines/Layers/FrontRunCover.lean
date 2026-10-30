-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/FrontRunCover.lean: in the layers' own rounds, the run "front" on
shapes, handing on two entries in the place of each claim's entries (rowZeroCover,
BackRunCover.lean); and the one-way tie: where this light run returns, the library's run returns,
the light claims standing under its claims (ClaimStandsUnder, ClaimCovers.lean), with the same
shape after, at a shape whose own record comes of a hearing at the run's own public record and
group. Two definitions and general laws; nothing is evaluated.

Why. As in BackRunCover.lean: the library's front_row0 (Johnson/Road/K4/Reads/RowZero.lean) says
where every entry of a form of "front" lies, of a record that the hearing of the layers' own rounds
has returned.

  ComesOfHearingAt P hp g ow   ow is the shape of a record that the hearing has returned at the
                          public record P with some list of tokens in the place of its own, the plan
                          hp and the group g. ComesOfHearingAt.some: it gives ComesOfHearing.
  frontRunCovered P g n   two tests on the shape (n is at most the array's number of columns; the
                          lookup's leaves' start form names no entry); then the forms of frontG
                          (Johnson/Desc/First/K4/Returns/RunShape.lean) with rowZeroCover for their
                          entries.
  frontRun_entriesInRowZero   under ComesOfHearingAt and these two tests: where frontG returns,
                          every entry of its forms is (ow.iU3, 0, i) with i below hp.nU[2].
  **frontRunCovered_standsUnder**   under ComesOfHearingAt: where k4RunG (frontRunCovered P g
                          hp.nU[2]) returns y', k4RunG (frontG P g) returns some z with y'.1 under
                          z.1, member by member, and y'.2 = z.2.

Limits. One way. frontRunCovered still calls frontG: it costs less only where a reader of its result
does not evaluate what it leaves unread. ComesOfHearingAt is a premise here. The cover's entries
need be no entries of a claim: see the Limits of BackRunCover.lean. What any of this costs Lean's
kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.BackRunCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (ledBlank)
open VerifiableInference.Desc.K9.Shape (EntriesCover ClaimStandsUnder ClaimsStandUnder
    claimStandsUnder_ofCover claimsStandUnder_cons)

/-- ow is the shape of a record that the hearing has returned at P with some tokens, hp and g. -/
def ComesOfHearingAt (P : Pub) (hp : HPlan2) (g : Nat) (ow : OwnSh) : Prop :=
  ∃ (tk : Array Nat) (fo : Forest.Heard) (F G : Fork) (t u : Tape) (o : Own),
    hearFl { P with tokv := tk } hp g fo F t = some (o, G, u) ∧ ownSh o = ow

/-- A shape that comes of a hearing at P, hp and g comes of a hearing at hp. -/
theorem ComesOfHearingAt.some {P : Pub} {hp : HPlan2} {g : Nat} {ow : OwnSh}
    (h : ComesOfHearingAt P hp g ow) : ComesOfHearing hp ow := by
  obtain ⟨tk, fo, F, G, t, u, o, hh, e⟩ := h
  exact ⟨_, g, fo, F, G, t, u, o, hh, e⟩

/-- **"front" with the cover.** n: the plan's length of the reads. -/
def frontRunCovered (P : Pub) (g n : Nat) (ow : OwnSh) (L : LedSh) : Option (List AffSh × LedSh) :=
  if decide (n ≤ ow.K3) && ow.H.fo.leaves.start.ents.isEmpty then
    (frontG P g ow L).map fun z => (z.1.map fun f => AffSh.mk (rowZeroCover ow.iU3 n) f.slots, z.2)
  else none

/-- Where frontG returns at a shape that comes of a hearing, under the two tests: its forms' entries
lie in row 0 of the array ow.iU3, below the plan's length of the reads. -/
theorem frontRun_entriesInRowZero {P : Pub} {hp : HPlan2} {g : Nat} {ow : OwnSh} {L : LedSh}
    {z : List AffSh × LedSh} (hF : ComesOfHearingAt P hp g ow) (hK : hp.nU.getD 2 0 ≤ ow.K3)
    (he : ow.H.fo.leaves.start.ents = []) (h : frontG P g ow L = some z) :
    ∀ f ∈ z.1, ∀ x ∈ f.ents, x.1 = ow.iU3 ∧ x.2.1 = 0 ∧ x.2.2 < hp.nU.getD 2 0 := by
  obtain ⟨tk, fo, F, G, t, u, o, hh, rfl⟩ := hF
  obtain ⟨-, ey, es, -⟩ := hear_parts hh
  have hb : frontG P g (ownSh o) (ledSh (ledBlank L)) = some z := by
    rw [ledSh_blank]
    exact h
  obtain ⟨fs, G', hf, rfl⟩ := formsFront_sh (P := P) ey es hb
  have hf' : formsFrontWith false { P with tokv := tk } g o (ledBlank L) = some (fs, G') := hf
  have hlv : Reads.InTab o.v o.H.fo.leaves.start := by
    intro y hy
    have e : o.H.fo.leaves.start.ents.toList.map entSh = [] := he
    rw [List.map_eq_nil_iff.1 e] at hy
    cases hy
  have hr := Reads.front_row0 hh hK hf' (fun c => by cases c) hlv
  intro f hf'' x hx
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf''
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (show x ∈ f0.ents.toList.map entSh from hx)
  exact hr f0 hf0 y hy

/-- Forms with the cover, as claims, stand under the same forms where their entries lie in row 0
below n. -/
theorem rowZeroCover_standUnder (t n : Nat) : ∀ l : List AffSh,
    (∀ f ∈ l, ∀ x ∈ f.ents, x.1 = t ∧ x.2.1 = 0 ∧ x.2.2 < n) →
    ClaimsStandUnder ((l.map fun f => AffSh.mk (rowZeroCover t n) f.slots).map claimOfSh) (l.map
        claimOfSh)
  | [], _ => trivial
  | f :: l, hl =>
    claimsStandUnder_cons.2 ⟨claimStandsUnder_ofCover none none f.slots [] (rowZeroCover_covers (hl
        f List.mem_cons_self)),
      rowZeroCover_standUnder t n l fun f' hf' => hl f' (List.mem_cons_of_mem _ hf')⟩

/-- **Where the light run returns, the library's returns**, the light claims under its claims, with
the same shape after: at a shape whose own record comes of a hearing at P, hp and g. -/
theorem frontRunCovered_standsUnder {P : Pub} {hp : HPlan2} {g : Nat} {a : ChainSh}
    (hI : ∀ ow, a.own = some ow → ComesOfHearingAt P hp g ow) {y' : List ClaimSh × ChainSh}
    (h : k4RunG (frontRunCovered P g (hp.nU.getD 2 0)) a = .ok y') :
    ∃ z, k4RunG (frontG P g) a = .ok z ∧ ClaimsStandUnder y'.1 z.1 ∧ y'.2 = z.2 := by
  unfold k4RunG at h ⊢
  by_cases h1 : (a.here != 1) = true
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h ⊢
  cases ho : a.own with
  | none =>
    rw [ho] at h
    cases h
  | some ow =>
    cases hl : a.led with
    | none =>
      rw [ho, hl] at h
      cases h
    | some L =>
      rw [ho, hl] at h
      dsimp only at h ⊢
      unfold frontRunCovered at h
      by_cases hb : (decide (hp.nU.getD 2 0 ≤ ow.K3) && ow.H.fo.leaves.start.ents.isEmpty) = true
      · rw [if_pos hb] at h
        rw [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hb
        cases hz : frontG P g ow L with
        | none =>
          rw [hz] at h
          cases h
        | some z =>
          rw [hz] at h
          obtain rfl := Except.ok.inj h
          exact ⟨_, rfl, rowZeroCover_standUnder _ _ z.1 (frontRun_entriesInRowZero (hI ow ho) hb.1
              hb.2 hz), rfl⟩
      · rw [if_neg hb] at h
        cases h

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.ComesOfHearingAt
#print axioms OnBytes.Desc.First.K4.Rt.ComesOfHearingAt.some
#print axioms OnBytes.Desc.First.K4.Rt.frontRunCovered
#print axioms OnBytes.Desc.First.K4.Rt.frontRun_entriesInRowZero
#print axioms OnBytes.Desc.First.K4.Rt.rowZeroCover_standUnder
#print axioms OnBytes.Desc.First.K4.Rt.frontRunCovered_standsUnder
