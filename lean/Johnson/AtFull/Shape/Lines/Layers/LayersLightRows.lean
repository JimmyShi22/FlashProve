-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/LayersLightRows.lean: a layers' link's batching on shapes with
three light rows, and the one-way tie: at a shape whose component own comes of a hearing, where the
light step returns, the table's step returns the same. General in the public record W, the group g
and the plan hp. Nothing is evaluated.

Why. An entry's test is a test on an interval (ClaimCovers.lean), so three rows may hand on covers
in the place of their claims' entries (BackRunCover.lean, FrontRunCover.lean,
ReadsEquationsCover.lean).

  OwnRecordHeard P hp g a   the invariant: what stands at a.own, if anything, is the shape of a
                          record that the hearing of the layers' own rounds has returned at P (with
                          some tokens), hp and g (ComesOfHearingAt, FrontRunCover.lean).
                          OwnRecordHeard.of_own: it depends on that component alone.
  **ownRoundsStep_laysOwnHeard**   the step on shapes sets it: where k4G p a returns b,
                          OwnRecordHeard p.P p.hp p.g b.
  layersLightRows W g n   the seven rows' runs with equationsRunCovered
                          (ReadsEquationsCover.lean) at "K8.equations", frontRunCovered
                          (FrontRunCover.lean) at "front" and backRunCovered (BackRunCover.lean) at
                          "back"; the four others, and whatever is no row, are the table's.
  listLookup_member, layersRows_keepOwn   every run of the table's seven rows leaves own as it was
                          (OwnRecordKept.lean).
  **layersLightRows_standUnder**   the light rows stand for the table's (RowsStandUnder,
                          ClaimCovers.lean), at the invariant, with n the plan's length of
                          the reads.
  **layersMemberStep_standsUnder**   so the member's whole step: where batchGS over layersLightRows
                          returns u at a shape with the invariant, batchGS over the table's rows
                          returns u.

Limits. One way. The invariant is a premise of layersMemberStep_standsUnder:
ownRoundsStep_laysOwnHeard sets it after the step, the laws of OwnRecordKept.lean carry it over
four members' steps; LayersLinkCells.lean joins these to the table's cells by number. What either
step costs is not said. That either returns is not said. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.OwnRecordKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Rt
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (equationsRunCovered equationsRunCovered_standsUnder)
open VerifiableInference.Desc.K9 (SegSort)
open VerifiableInference.Desc.K9.Shape

/-- **The invariant**: what stands at a.own comes of a hearing at P, hp and g. -/
def OwnRecordHeard (P : Pub) (hp : HPlan2) (g : Nat) (a : ChainSh) : Prop :=
  ∀ ow, a.own = some ow → ComesOfHearingAt P hp g ow

/-- The invariant depends on the component own alone. -/
theorem OwnRecordHeard.of_own {P : Pub} {hp : HPlan2} {g : Nat} {a b : ChainSh}
    (h : OwnRecordHeard P hp g a) (e : b.own = a.own) : OwnRecordHeard P hp g b := by
  intro ow ho
  rw [e] at ho
  exact h ow ho

/-- **The step of the layers' own rounds on shapes sets it.** -/
theorem ownRoundsStep_laysOwnHeard (p : Par) {a b : ChainSh} (h : k4G p a = some b) :
    OwnRecordHeard p.P p.hp p.g b := by
  rw [k4G_eq] at h
  unfold k4GL at h
  split at h
  · cases h
  · split at h
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      unfold ownOf at hz
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hz
      intro ow ho
      have ho' : some (ownSh x.1) = some ow := ho
      obtain rfl := Option.some.inj ho'
      exact ⟨_, _, _, x.2.1, _, x.2.2, x.1, hx, rfl⟩
    · cases h

/-- **The seven rows' runs, three of them light.** n: the plan's length of the reads. -/
def layersLightRows (W : Verify.Public) (g n : Nat) (o : Nat × String) :
    Nat → ChainSh → Except String (List ClaimSh × ChainSh) :=
  if o == (4, "K8.equations") then equationsRunCovered
  else if o == (2, "front") then fun _ a => k4RunG (frontRunCovered W.layers g n) a
  else if o == (2, "back") then fun _ a => k4RunG (backRunCovered n) a
  else (tabOf (rowsLay W g) o).g

/-- What a lookup in a list returns is a value of the list. -/
theorem listLookup_member {α β : Type} [BEq α] (o : α) : ∀ (l : List (α × β)) (r : β),
    l.lookup o = some r → r ∈ l.map (·.2)
  | [], _, h => by cases h
  | (k, v) :: l, r, h => by
    rw [List.lookup_cons] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (listLookup_member o l r h)

/-- Every run of the table's rows leaves own as it was; what is no row returns an error. -/
theorem layersRows_keepOwn (W : Verify.Public) (g : Nat) (o : Nat × String) :
    RowRunKeepsOwn (tabOf (rowsLay W g) o).g := by
  unfold tabOf
  cases hl : (rowsLay W g).lookup o with
  | none =>
    intro n a y h
    cases h
  | some r =>
    have hm := listLookup_member o _ r hl
    simp only [rowsLay, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact objectsG_keepsOwn false
    · exact guestsG_keepsOwn
    · exact k4RunG_keepsOwn _
    · exact objectsG_keepsOwn true
    · exact guestsG_keepsOwn
    · intro n a y h
      have h' : VerifiableInference.Desc.First.K8.Honest.eqRunG n a = .ok y := h
      rw [VerifiableInference.Desc.First.K8.Honest.eqRunG_eqO] at h'
      unfold VerifiableInference.Desc.First.K8.Honest.eqRunGO at h'
      cases ht : VerifiableInference.Desc.First.K8.Honest.eqGO n a with
      | error e =>
        rw [ht] at h'
        cases h'
      | ok t =>
        rw [ht] at h'
        have h2 : (match VerifiableInference.Desc.First.K8.Honest.eqClaimsG a t with
          | some cs => (.ok (cs, t) : Except String (List ClaimSh × ChainSh))
          | none => .error "K8.equations: the claims' shapes cannot be said") = .ok y := h'
        split at h2
        · obtain rfl := Except.ok.inj h2
          exact eqGO_keepsOwn n a t ht
        · cases h2
    · exact k4RunG_keepsOwn _

/-- **The light rows stand for the table's**, at the invariant. -/
theorem layersLightRows_standUnder (W : Verify.Public) (g : Nat) (hp : HPlan2) :
    RowsStandUnder (OwnRecordHeard W.layers hp g) (layersLightRows W g (hp.nU.getD 2 0))
      (fun o => (tabOf (rowsLay W g) o).g) := by
  intro o n a y' hI h
  unfold layersLightRows at h
  by_cases e1 : o = (4, "K8.equations")
  · subst e1
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e2⟩ := equationsRunCovered_standsUnder h
    exact ⟨y, ey, u, e2, hI.of_own (by rw [← e2]; exact equationsRunCovered_keepsOwn n a y' h)⟩
  rw [if_neg (by simpa using e1)] at h
  by_cases e2 : o = (2, "front")
  · subst e2
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e3⟩ := frontRunCovered_standsUnder hI h
    exact ⟨y, ey, u, e3, hI.of_own (by rw [← e3]; exact k4RunG_keepsOwn _ n a y' h)⟩
  rw [if_neg (by simpa using e2)] at h
  by_cases e3 : o = (2, "back")
  · subst e3
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e4⟩ := backRunCovered_standsUnder W.layers.y W.layers.sc (fun ow ho =>
        (hI ow ho).some) h
    exact ⟨y, ey, u, e4, hI.of_own (by rw [← e4]; exact k4RunG_keepsOwn _ n a y' h)⟩
  rw [if_neg (by simpa using e3)] at h
  exact ⟨y', h, ClaimsStandUnder.refl _, rfl, hI.of_own (layersRows_keepOwn W g o n a y' h)⟩

/-- **The member's whole step**: where the light step returns u at the invariant, the table's does.
-/
theorem layersMemberStep_standsUnder (W : Verify.Public) (g : Nat) (hp : HPlan2) (rows : Nat) (k :
    SegSort)
    (order : List (Nat × String)) {a u : ChainSh} (hI : OwnRecordHeard W.layers hp g a)
    (h : batchGS rows k (layersLightRows W g (hp.nU.getD 2 0)) order a = .ok u) :
    batchGS rows k (fun o => (tabOf (rowsLay W g) o).g) order a = .ok u :=
  batchingOnShapes_standsUnder (layersLightRows_standUnder W g hp) rows order
    (fun a b hI hd => hI.of_own (drawG_keepsOwn rows a b hd)) hI h

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.OwnRecordHeard
#print axioms Johnson.AtFull.Shape.OwnRecordHeard.of_own
#print axioms Johnson.AtFull.Shape.ownRoundsStep_laysOwnHeard
#print axioms Johnson.AtFull.Shape.layersLightRows
#print axioms Johnson.AtFull.Shape.listLookup_member
#print axioms Johnson.AtFull.Shape.layersRows_keepOwn
#print axioms Johnson.AtFull.Shape.layersLightRows_standUnder
#print axioms Johnson.AtFull.Shape.layersMemberStep_standsUnder
