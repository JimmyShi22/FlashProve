-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/BackRunCover.lean: in the layers' own rounds, the run "back" on
shapes with two entries in the place of each claim's entries, the first and the n-th entry of row 0
of the array of reads; and the one-way tie: where this light run returns, the library's run returns,
the light claims standing under its claims (ClaimStandsUnder, ClaimCovers.lean), with the same
shape after, at a shape whose own record comes of a hearing. Three definitions and general laws;
nothing is evaluated.

Why. The library has it as a law that every entry which a form of "back" names is (iU3, 0, i) with i
below the plan's length of the reads (back_row0, Johnson/Road/K4/Reads/RowZero.lean). That law
speaks of a record that the hearing of the layers' own rounds has returned. So the light run need
not look at an entry.

  ComesOfHearing hp ow    ow is the shape of a record that the hearing has returned at the plan hp,
                          at some public record, group, lookup's record, ledger and tape.
  rowZeroCover t n        the two entries (t, 0, 0) and (t, 0, n - 1).
  rowZeroCover_covers     they cover every list of entries (t, 0, i) with i below n.
  backRunCovered n        two tests on the shape (n is at most the array's number of columns; the
                          form in which the lookup's key side ends names no entry); then the forms
                          of backRunLight (BackRunLight.lean) with rowZeroCover for their entries.
  backRun_entriesInRowZero   under ComesOfHearing and these two tests: where backRunLight returns,
                          every entry of its forms is (ow.iU3, 0, i) with i below hp.nU[2].
  **backRunCovered_standsUnder**   under ComesOfHearing: where k4RunG (backRunCovered hp.nU[2])
                          returns y', k4RunG (backG y sc) returns some z with y'.1 under z.1,
                          member by member, and y'.2 = z.2.

Limits. One way. ComesOfHearing is a premise here: the step of the layers' own rounds sets such a
shape by its text (ownOf, Johnson/Desc/First/K4/Returns/AtShape.lean); that the members between keep
it is not shown here. The cover's entries need be no entries of a claim: where row 0 of that array
is shorter than n, or begins after 0, the light run's claims fail at the adding and these laws say
nothing. A claim without an entry gets the cover too. What any of this costs Lean's kernel is not
measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.ClaimCovers
import Johnson.AtFull.Shape.Lines.Layers.BackRunLight
import Johnson.Desc.First.K4.Returns.AtShape
import Johnson.Road.K4.Reads.RowZero

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

/-- ow is the shape of a record that the hearing has returned at the plan hp. -/
def ComesOfHearing (hp : HPlan2) (ow : OwnSh) : Prop :=
  ∃ (P : Pub) (g : Nat) (fo : Forest.Heard) (F G : Fork) (t u : Tape) (o : Own),
    hearFl P hp g fo F t = some (o, G, u) ∧ ownSh o = ow

/-- The first and the n-th entry of row 0 of the array t. -/
def rowZeroCover (t n : Nat) : List EntSh := [(t, 0, 0), (t, 0, n - 1)]

/-- The two entries cover every list of entries of row 0 of the array t with index below n. -/
theorem rowZeroCover_covers {t n : Nat} {ents : List EntSh}
    (h : ∀ x ∈ ents, x.1 = t ∧ x.2.1 = 0 ∧ x.2.2 < n) : EntriesCover (rowZeroCover t n) ents := by
  intro x hx
  obtain ⟨a, b, c⟩ := h x hx
  refine ⟨0, n - 1, ?_, ?_, Nat.zero_le _, by omega⟩
  · rw [a, b]
    exact List.mem_cons_self
  · rw [a, b]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **"back" with the cover.** n: the plan's length of the reads. -/
def backRunCovered (n : Nat) (ow : OwnSh) (L : LedSh) : Option (List AffSh × LedSh) :=
  if decide (n ≤ ow.K3) && ow.H.fo.cEnd.ents.isEmpty then
    (backRunLight ow L).map fun z => (z.1.map fun f => AffSh.mk (rowZeroCover ow.iU3 n) f.slots,
        z.2)
  else none

/-- Where backRunLight returns at a shape that comes of a hearing, under the two tests: its forms'
entries lie in row 0 of the array ow.iU3, below the plan's length of the reads. -/
theorem backRun_entriesInRowZero {hp : HPlan2} {ow : OwnSh} {L : LedSh} {z : List AffSh × LedSh}
    (hF : ComesOfHearing hp ow) (hK : hp.nU.getD 2 0 ≤ ow.K3) (he : ow.H.fo.cEnd.ents = [])
    (h : backRunLight ow L = some z) :
    ∀ f ∈ z.1, ∀ x ∈ f.ents, x.1 = ow.iU3 ∧ x.2.1 = 0 ∧ x.2.2 < hp.nU.getD 2 0 := by
  obtain ⟨P, g, fo, F, G, t, u, o, hh, rfl⟩ := hF
  have hb : backG o.v.y o.v.sc (ownSh o) (ledSh (ledBlank L)) = some z := by
    rw [backOnShapes_eqLight, ledSh_blank]
    exact h
  obtain ⟨fs, G', hf, rfl⟩ := formsBack_sh hb
  have he' : o.H.fo.cEnd.ents = #[] := by
    have e : o.H.fo.cEnd.ents.toList.map entSh = [] := he
    have e2 : o.H.fo.cEnd.ents.toList = [] := List.map_eq_nil_iff.1 e
    exact Array.toList_eq_nil_iff.1 e2
  have hr := Reads.back_row0 hh hK hf he'
  intro f hf' x hx
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (show x ∈ f0.ents.toList.map entSh from hx)
  exact hr f0 hf0 y hy

/-- **Where the light run returns, the library's returns**, the light claims under its claims, with
the same shape after: at a shape whose own record comes of a hearing. -/
theorem backRunCovered_standsUnder {hp : HPlan2} (y : Layer.Lay) (sc : Layer.Scales) {a : ChainSh}
    (hI : ∀ ow, a.own = some ow → ComesOfHearing hp ow) {y' : List ClaimSh × ChainSh}
    (h : k4RunG (backRunCovered (hp.nU.getD 2 0)) a = .ok y') :
    ∃ z, k4RunG (backG y sc) a = .ok z ∧ ClaimsStandUnder y'.1 z.1 ∧ y'.2 = z.2 := by
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
      rw [backOnShapes_eqLight]
      unfold backRunCovered at h
      by_cases hb : (decide (hp.nU.getD 2 0 ≤ ow.K3) && ow.H.fo.cEnd.ents.isEmpty) = true
      · rw [if_pos hb] at h
        rw [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hb
        cases hz : backRunLight ow L with
        | none =>
          rw [hz] at h
          cases h
        | some z =>
          rw [hz] at h
          obtain rfl := Except.ok.inj h
          have hE := backRun_entriesInRowZero (hI ow ho) hb.1 hb.2 hz
          refine ⟨_, rfl, ?_, rfl⟩
          show ClaimsStandUnder ((z.1.map fun f => AffSh.mk (rowZeroCover ow.iU3 (hp.nU.getD 2 0))
              f.slots).map
            claimOfSh) (z.1.map claimOfSh)
          have key : ∀ l : List AffSh, (∀ f ∈ l, ∀ x ∈ f.ents,
              x.1 = ow.iU3 ∧ x.2.1 = 0 ∧ x.2.2 < hp.nU.getD 2 0) →
              ClaimsStandUnder ((l.map fun f => AffSh.mk (rowZeroCover ow.iU3 (hp.nU.getD 2 0))
                  f.slots).map
                claimOfSh) (l.map claimOfSh) := by
            intro l
            induction l with
            | nil => intro _; trivial
            | cons f l ih =>
              intro hl
              exact claimsStandUnder_cons.2 ⟨claimStandsUnder_ofCover none none f.slots []
                (rowZeroCover_covers (hl f List.mem_cons_self)),
                ih fun f' hf' => hl f' (List.mem_cons_of_mem _ hf')⟩
          exact key z.1 hE
      · rw [if_neg hb] at h
        cases h

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.ComesOfHearing
#print axioms OnBytes.Desc.First.K4.Rt.rowZeroCover
#print axioms OnBytes.Desc.First.K4.Rt.rowZeroCover_covers
#print axioms OnBytes.Desc.First.K4.Rt.backRunCovered
#print axioms OnBytes.Desc.First.K4.Rt.backRun_entriesInRowZero
#print axioms OnBytes.Desc.First.K4.Rt.backRunCovered_standsUnder
