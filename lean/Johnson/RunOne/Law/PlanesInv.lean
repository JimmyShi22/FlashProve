-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/PlanesInv.lean: WHAT THE
RUN "planes" AND THE LAYER DO TO THE LEDGER, at a key file's lookup link.

Main names:
  hideRun_same: a run of values put under slots keeps the ledger's next, ns and owed, and the
    sizes of its three arrays. No premise.
  planes_inv: planesG's yes on an empty tape: the ledger behind is the one in front with zeros laid
    under the slots of the leaves' sumcheck's hiding polynomial (factor -1); the tape stays empty;
    the three claims written out.
  layerD_done: the layer's yes (layerD_law, Johnson/RunOne/Law/AtKeyD.lean) WITH the layer's own
    last test: doneG says yes at the ledger behind.
  doneG_parts: doneG's yes, in its three parts.

Object: planesG, doneG (Johnson/Desc/First/Look/K3LookupGeneral.lean); the layer
(Johnson/Desc/Key/Link.lean). User: Johnson/RunOne/Law/LayerBehind.lean.
Limits. Nothing on the claims' truth. Nothing on soundness.

-/
import Johnson.RunOne.Law.AtKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.PlanesInv
open OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params
open OnBytes.Model (Fork Aff Reading ofNat)
open VerifiableInference.Desc (Block named need claimsIn claimsInBy viewWordsBelowPrime)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Lookup lookupSeat layer lookupPlace rowsInOrder
  layerOrder)

theorem hide_same {F G : Fork} {j : ℕ} {y f : E} (h : F.hide j y f = some G) :
    G.next = F.next ∧ G.ns = F.ns ∧ G.owed = F.owed ∧ G.vp.size = F.vp.size ∧
      G.mf.size = F.mf.size ∧ G.gotF.size = F.gotF.size := by
  unfold Fork.hide at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl, rfl, by simp, by simp, by simp⟩

theorem hideSteps_same (f : E) : ∀ (l : List E) (first : ℕ) (F : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep f) (first, F) = some x →
      x.2.next = F.next ∧ x.2.ns = F.ns ∧ x.2.owed = F.owed ∧ x.2.vp.size = F.vp.size ∧
        x.2.mf.size = F.mf.size ∧ x.2.gotF.size = F.gotF.size
  | [], first, F, x, h => by
    obtain rfl : (first, F) = x := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hh : F.hide first y f with
    | none =>
      have : Fork.hideStep f (first, F) y = none := by
        show (F.hide first y f).map _ = none
        rw [hh]
        rfl
      rw [this] at h
      cases h
    | some H =>
      have : Fork.hideStep f (first, F) y = some (first + 1, H) := by
        show (F.hide first y f).map _ = _
        rw [hh]
        rfl
      rw [this] at h
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hide_same hh
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hideSteps_same f l (first + 1) H x h
      exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

/-- **A run of values put under slots keeps next, ns, owed and the three arrays' sizes.** -/
theorem hideRun_same {F G : Fork} {first : ℕ} {v : Array E} {f : E}
    (h : F.hideRun first v f = some G) :
    G.next = F.next ∧ G.ns = F.ns ∧ G.owed = F.owed ∧ G.vp.size = F.vp.size ∧
      G.mf.size = F.mf.size ∧ G.gotF.size = F.gotF.size := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hx : v.toList.foldlM (Fork.hideStep f) (first, F) with
  | none =>
    rw [hx] at h
    exact absurd h (by simp)
  | some x =>
    rw [hx] at h
    obtain rfl := Option.some.inj h
    exact hideSteps_same f _ _ _ _ hx

/-- **The run "planes", inverted.** -/
theorem planes_inv {f : Face} {g : HeardG} {H H' : Fork} {pl : List PlaneClaim} {u : Tape}
    (h : planesG f g H [] = some (pl, H', u)) :
    H.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE) (subE zeroE oneE) =
        some H' ∧ u = [] ∧
      pl = [⟨g.leaves.rowForm oneE {}, mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0),
          eqPairs (f.mu + f.d) g.zb0⟩,
        ⟨Aff.slot g.sBit, subE zeroE oneE, eqPairs (f.mu + f.d) g.zb1⟩,
        ⟨Aff.ofConst (subE zeroE (ofNat f.count)), oneE,
          ((List.range f.mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) ++
            List.replicate f.d (oneE, oneE)⟩] := by
  unfold planesG at h
  replace h := bind_some h
  obtain ⟨⟨row, p'⟩, G1, u1, h1, h⟩ := h
  obtain ⟨e1, rfl, rfl⟩ := row_fl h1
  cases pure_some h
  exact ⟨e1, rfl, rfl⟩

/-- **The layer's yes, with its own last test.** -/
theorem layerD_done {one : OneTime} {set : Setting} {i : ℕ} {x : Lookup}
    {claims : FirstState → Except String (List Claim × FirstState)} {s s'' : FirstState}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (layer one set i x claims).decide s rs gs = .ok s'') :
    ∃ cls s' F g rows keys, claims s = .ok (cls, s') ∧ s'.base.fork = some F ∧
      s'.base.heard = some g ∧
      rowsInOrder (Wf.planesAt one.ranges one.codes i)
        (layerOrder (cls.filter fun c => c.isLeft).length) F s'.base.home cls = some rows ∧
      keyClaims x F s'.base.home g = some keys ∧
      doneG (lookupPlace set i x) g (F.paid g.owedJoin) = true ∧
      s'' = { s' with base := { s'.base with
        fork := some (F.paid g.owedJoin)
        rows := s'.base.rows ++ [rows]
        keys := s'.base.keys ++ [keys] } } := by
  have h' : (do
      let y ← claims s
      let F ← named "the layer: no ledger is open" y.2.base.fork
      let g ← named "the layer: nothing was heard" y.2.base.heard
      let rows ← named "the layer: a claim has no row"
        (rowsInOrder (Wf.planesAt one.ranges one.codes i)
          (layerOrder (y.1.filter fun c => c.isLeft).length) F y.2.base.home y.1)
      let keys ← named "the layer: a part's form has no claim on its keys"
        (keyClaims x F y.2.base.home g)
      need "the layer: something of the lookup is left open in the ledger (doneG)"
        (doneG (lookupPlace set i x) g (F.paid g.owedJoin))
      pure ({ y.2 with base := { y.2.base with
        fork := some (F.paid g.owedJoin)
        rows := y.2.base.rows ++ [rows]
        keys := y.2.base.keys ++ [keys] } } : FirstState) : Except String FirstState) = .ok s'' := h
  obtain ⟨y, h1, h'⟩ := bindX h'
  obtain ⟨F, h2, h'⟩ := bindX h'
  obtain ⟨g, h3, h'⟩ := bindX h'
  obtain ⟨rows, h4, h'⟩ := bindX h'
  obtain ⟨keys, h5, h'⟩ := bindX h'
  obtain ⟨_, h6, h'⟩ := bindX h'
  cases h'
  exact ⟨y.1, y.2, F, g, rows, keys, h1, namedX h2, namedX h3, namedX h4, namedX h5, needX h6, rfl⟩

/-- doneG's yes, in its three parts. -/
theorem doneG_parts {p : PG} {g : HeardG} {F : Fork} (h : doneG p g F = true) :
    p.first + p.face.slots ≤ F.next ∧
      (∀ j, j < p.face.slots → F.gotF.getD (p.first + j) false = true) ∧
      ∀ i ∈ [g.owedObjects, g.owedPlanes, g.owedJoin],
        ((F.owed[i]?).map (·.added)) = some true := by
  unfold doneG at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Johnson.RunOne.Law.PlanesInv

#print axioms Johnson.RunOne.Law.PlanesInv.hide_same
#print axioms Johnson.RunOne.Law.PlanesInv.hideSteps_same
#print axioms Johnson.RunOne.Law.PlanesInv.hideRun_same
#print axioms Johnson.RunOne.Law.PlanesInv.planes_inv
#print axioms Johnson.RunOne.Law.PlanesInv.layerD_done
#print axioms Johnson.RunOne.Law.PlanesInv.doneG_parts
