-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesBlock.lean: the planes' three clauses from a yes of the layers' own block.

Johnson/Meaning/ReadsTokens.lean has the three clauses that the layers owe the lookup on the planes
of its counts (`K3HostPlanes`, Johnson/Meaning/PlanesLaw.lean) from a run of the layers' plain
hearing and from `planesParts` being there. Johnson/Desc/First/K4/BlockLaws.lean gets such a run
from a yes of the block's `decide` (`decide_ok`), and a return of the plain function of the claims
from a return of the block's named run "front" (`front_ok`); OnBytes/Desc/First/K4/ClaimsLaws.lean
gets `planesParts` from that (`formsFrontWith_some`). Here the three are joined. Nothing is shown
anew of the block.

Main theorems (namespace `Meaning.Planes`).
  `front_parts`: a return of the block's run "front" has `planesParts` there at what the state holds
      as heard, whoever states the lookup's own claims.
  `block_planes`: **the three clauses from the block**: a yes of `(block L p).decide`; a return of
      its run "front" at a state that holds as heard what the state behind the yes holds; then: at
      any letters over the sizes of the place's plan's record closed with the public shapes, the
      relation in front of the draw, the letters' weights and reads, and the planes' cells give the
      three clauses at the forms of what was heard.
  `seatOwn_law`: hlaw holds at the seat of the layers' part of the carried record (`seatOwn`,
      Johnson/Desc/First/K4/AtS.lean), by unfolding.

Premises. On the seat L: what setOwn lays, own returns, also behind setOwed (hlaw). On the states:
hkeep. On the place: its record's lists of matrices are tailsOf's; its plan is member number p.g of
what plansG returns at its record (hT, hG, hgp). THE RELATION IN FRONT OF THE DRAW, and the premises
on the letters, the world and the cells, stand behind "for all".
Limits. That a file's place has the public record's own members, and what runs between the yes and
"front", are not treated. Nothing on soundness.
-/
import Johnson.Meaning.ReadsTokens
import Johnson.Desc.First.K4.BlockLaws
import Johnson.Desc.First.K4.AtS
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf plansG)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (Seat Par block planesParts)
open Meaning.Reads

variable {S : Type} (L : Seat S)

/-- A return of the block's run "front" has the planes' parts there. -/
theorem front_parts {p : Par} {run : ℕ → S → Except String (List Aff × S)}
    (hr : (block L p).claims.lookup "front" = some run) {n : ℕ} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ o pp, L.own s = some o ∧ planesParts o.v o.H.fo = some pp := by
  obtain ⟨o, fs, F, ho, hf, _, _⟩ := (Desc.First.K4.front_ok L p run hr n s s' cl).mp h
  refine ⟨o, ?_⟩
  unfold Desc.First.K4.frontOf at hf
  cases hk : p.k3Runs with
  | true =>
    rw [hk] at hf
    obtain ⟨_, pp, _, _, _, _, a2, _⟩ := Desc.First.K4.formsFrontWith_some (rows := false) hf
    exact ⟨pp, ho, a2⟩
  | false =>
    rw [hk] at hf
    obtain ⟨_, pp, _, _, _, _, a2, _⟩ := Desc.First.K4.formsFrontWith_some (rows := true) hf
    exact ⟨pp, ho, a2⟩

/-- **The planes' three clauses from the layers' own block.** s: the state at which decide says yes;
s': the state behind; s₂: the state at which "front" returns. -/
theorem block_planes (ρ : Reading Cb.Gl.E) {p : Par} {s s' s₂ s₃ : S} {rs : List Fmt.RoundView}
    {cols : List (List (ℕ × List UInt64))} (hyes : (block L p).decide s rs cols = .ok s')
    {run : ℕ → S → Except String (List Aff × S)}
    (hr : (block L p).claims.lookup "front" = some run) {n : ℕ} {cl : List Aff}
    (hfront : run n s₂ = .ok (cl, s₃))
    (hlaw : ∀ (x : S) (o : Own) (d : Option ℕ), L.own (L.setOwed (L.setOwn x o) d) = some o)
    (hkeep : L.own s₂ = L.own s')
    (hT : p.P.tails = tailsOf p.P.y) {G : Array HPlan2} (hG : plansG p.P = .ok G)
    (hgp : G[p.g]? = some p.hp) :
    ∃ o, L.own s' = some o ∧
      ∀ (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf
          (Closed.closedAt p.hp.tl (Closed.layShapes { p.P with tokv := L.tokv s } p.g))))
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
          cellN (Closed.closedAt p.hp.tl (Closed.layShapes { p.P with tokv := L.tokv s } p.g)) Θ
            msg (matIx o.v.y).iB r c = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
            (fun f => f.value ρ W) (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨_, _, _, fo, o, F, _, hh, e⟩ := Desc.First.K4.decide_ok L hyes
  obtain ⟨o', pp, ho', hq⟩ := front_parts L hr hfront
  have ho : L.own s' = some o := by rw [e]; exact hlaw _ o none
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans (hkeep.trans ho))
  refine ⟨o', ho, fun Θ x msg h hphi W hu ν h4 => ?_⟩
  exact k4_host_planes_tokens ρ hh hq hT hG hgp _ _ rfl rfl Θ h hphi W hu ν h4

/-- The seat of the layers' part of the carried record returns as heard what was laid as heard. -/
theorem seatOwn_law (x : Desc.First.K4.Part) (o : Own) (d : Option ℕ) :
    Desc.First.K4.seatOwn.own
      (Desc.First.K4.seatOwn.setOwed (Desc.First.K4.seatOwn.setOwn x o) d) = some o := rfl

#print axioms seatOwn_law
#print axioms front_parts
#print axioms block_planes

end Meaning.Planes
