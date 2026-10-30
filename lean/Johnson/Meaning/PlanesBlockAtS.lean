-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesBlockAtS.lean: the planes' three clauses from a yes of the layers' block at
the first chain's carried record.

Johnson/Meaning/PlanesBlock.lean has the three clauses that the layers owe the lookup on the planes
of its counts from a yes of `(block L p).decide`, at any seat L. The block that is seated in the
first chain is `blockAtS p` (Johnson/Desc/First/K4/AtS.lean): the block at the seat of the layers'
part, lifted to the carried record S. Johnson/Desc/First/K4/AtSHears.lean gets a run of the plain
hearing from its yes (`blockAtS_hears`). Here the run "front" is lifted likewise, and the two are
joined with Johnson/Meaning/ReadsTokens.lean.

Main theorems (namespace `Meaning.Planes`).
  `frontAtS`: which function the name "front" holds in `blockAtS p`.
  `frontAtS_parts`: a return of that run at a record s: s stands in a layers' link, holds something
      as heard, and `planesParts` is there at it.
  `blockAtS_planes`: **the three clauses from the block at the carried record**: a yes of
      `(blockAtS p).decide` at s; a return of its run "front" at s₂; s₂ holds as heard what the yes
      has laid (hkeep); then as `block_planes`.
  `seatOwn_setFork_own`, `seatOwn_setOwed_own`: of the seat's setters, those of the ledger and of
      the debt of rows leave what is held as heard.

Premises. hkeep: whatever runs between the yes and "front" is not treated here; the two lemmas on
the setters say it of K4's own two other setters alone. On the place: hT, hG, hgp, as in
Johnson/Meaning/PlanesBlock.lean. THE RELATION IN FRONT OF THE DRAW, and the premises on the
letters, the world and the cells, stand behind "for all".
Limits. Nothing on soundness.
-/
import Johnson.Meaning.PlanesBlock
import Johnson.Desc.First.K4.AtSHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf plansG)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (Par block blockAtS seatOwn part? setPart planesParts runOf frontOf)
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)
open Meaning.Reads

/-- The setter of the ledger leaves what is held as heard. -/
theorem seatOwn_setFork_own (x : Desc.First.K4.Part) (F : Fork) :
    seatOwn.own (seatOwn.setFork x F) = seatOwn.own x := rfl

/-- The setter of the debt of rows leaves what is held as heard. -/
theorem seatOwn_setOwed_own (x : Desc.First.K4.Part) (d : Option ℕ) :
    seatOwn.own (seatOwn.setOwed x d) = seatOwn.own x := rfl

/-- Which function the name "front" holds in the block at the carried record. -/
theorem frontAtS (p : Par) : (blockAtS p).claims.lookup "front" =
    some fun _ t => (named "the part is not there" (part? t)).bind fun q =>
      (runOf seatOwn "K4.claims-front" (frontOf p) q).map fun y => (y.1, setPart t y.2) := by
  simp [blockAtS, VerifiableInference.Desc.Block.liftPart, block, frontOf]

/-- A return of the run "front" at the carried record. -/
theorem frontAtS_parts {p : Par} {run : ℕ → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : ℕ} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (pp : Aff × List Aff),
      s.here = .lay a ∧ a.own = some o ∧ planesParts o.v o.H.fo = some pp := by
  rw [frontAtS] at hr
  obtain rfl := Option.some.inj hr
  have h' : ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn "K4.claims-front" (frontOf p) q).map fun y => (y.1, setPart s y.2)) =
        .ok (cl, s') := h
  cases hq : part? s with
  | none =>
    rw [hq] at h'
    cases h'
  | some q =>
    rw [hq] at h'
    have h2 : ((runOf seatOwn "K4.claims-front" (frontOf p) q).map
      fun y => (y.1, setPart s y.2)) = .ok (cl, s') := h'
    cases hd : runOf seatOwn "K4.claims-front" (frontOf p) q with
    | error e =>
      rw [hd] at h2
      cases h2
    | ok y =>
      obtain ⟨o, pp, ho, hpp⟩ := front_parts seatOwn (Desc.First.K4.block_front seatOwn p)
        (n := n) (s := q) (s' := y.2) (cl := y.1) hd
      unfold part? at hq
      split at hq
      · rename_i a ha
        obtain rfl := Option.some.inj hq
        exact ⟨a, o, pp, ha, ho, hpp⟩
      · cases hq

/-- **The planes' three clauses from the layers' block at the carried record.** s: the record at
which decide says yes; s': the record behind; s₂: the record at which "front" returns. -/
theorem blockAtS_planes (ρ : Reading Cb.Gl.E) {p : Par} {s s' s₂ s₃ : S} {rs : List Fmt.RoundView}
    {cols : List (List (ℕ × List UInt64))} (hyes : (blockAtS p).decide s rs cols = .ok s')
    {run : ℕ → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : ℕ} {cl : List Aff}
    (hfront : run n s₂ = .ok (cl, s₃))
    (hkeep : ∀ a a₂ : LayOwn, s'.here = .lay a → s₂.here = .lay a₂ → a₂.own = a.own)
    (hT : p.P.tails = tailsOf p.P.y) {G : Array HPlan2} (hG : plansG p.P = .ok G)
    (hgp : G[p.g]? = some p.hp) :
    ∃ (a : LayOwn) (o : Own), s'.here = .lay a ∧ a.own = some o ∧
      ∀ (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf
          (Closed.closedAt p.hp.tl (Closed.layShapes { p.P with tokv := s.tokv } p.g))))
        {x : Θ.X} {msg : Θ.M}, relIn Θ.letters x msg →
        (∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
          Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE)) →
        ∀ W : World Cb.Gl.E,
        (∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (p.hp.tl.mats.getD f.mat {}).k,
          ∀ sg < (p.hp.tl.mats.getD f.mat {}).m / f.len,
            Θ.u3 msg (f.start + c * ((p.hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
              u3Val W.entry o.v.iU3 o.v.K3
                (f.start + c * ((p.hp.tl.mats.getD f.mat {}).m / f.len) + sg)) →
        ∀ ν : _root_.Fo.Pl → Cb.Gl.E,
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          cellN (Closed.closedAt p.hp.tl (Closed.layShapes { p.P with tokv := s.tokv } p.g)) Θ
            msg (matIx o.v.y).iB r c = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
            (fun f => f.value ρ W) (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨a, fo, o, F, _, _, _, _, _, hh, e⟩ := Desc.First.K4.blockAtS_hears hyes
  obtain ⟨a₂, o', pp, ha₂, ho', hq⟩ := frontAtS_parts hr hfront
  have hs' : s'.here = .lay { a with F := F, own := some o } := by rw [e]
  have ho : a₂.own = some o := hkeep _ a₂ hs' ha₂
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  refine ⟨_, o', hs', rfl, fun Θ x msg h hphi W hu ν h4 => ?_⟩
  exact k4_host_planes_tokens ρ hh hq hT hG hgp _ _ rfl rfl Θ h hphi W hu ν h4

#print axioms frontAtS
#print axioms frontAtS_parts
#print axioms blockAtS_planes

end Meaning.Planes
