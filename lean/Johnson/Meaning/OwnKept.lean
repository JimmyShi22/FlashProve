-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/OwnKept.lean: what the layers' own rounds have left stays in the carried record: the
row's definition, and the layers' own share.

Johnson/Meaning/PlanesBlockAtS.lean takes as a premise (hkeep) that the record at which the layers'
run of claims "front" returns still holds as heard what the yes of the layers' `decide` has laid.
Between the two stand other kinds' blocks and runs at the same record, each through its own seat.
That each of them leaves that field is an invariant of the chain: a share a kind. Here it is named,
and the layers' block's own share is shown.

Main names (namespace `Meaning.Planes`).
  `ownAt s`: what the record s holds as heard by the layers' own rounds; none outside a layers'
      link.
  `DecideKeepsOwn b`, `ClaimsKeepOwn b`, `AfterKeepsOwn b`: wherever b's decide, a named run of its
      claims, a named run of its behind the batching returns, `ownAt` is as it was.
  `blockAtS_lays`: the layers' decide is the one that lays it: behind its yes `ownAt` is there.
  `blockAtS_claimsKeep`, `blockAtS_afterKeeps`: **the layers' share**: its two runs of claims and
      its run behind the batching keep `ownAt`.
  `hkeep_of_ownAt`: `ownAt s₂ = ownAt s'` gives the premise hkeep.
  `blockAtS_planes_own`: `blockAtS_planes` with that equation in hkeep's place.

Limits. THE OTHER KINDS' SHARES ARE SHOWN BY NOBODY: that the lookup's, the smallness test's and
every other block and run of a layers' link keeps `ownAt`; nor that the driver runs nothing else
between. A block that refuses always keeps all this emptily. Nothing on soundness.
-/
import Johnson.Meaning.PlanesBlockAtS
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf plansG)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (Par block blockAtS seatOwn part? setPart runOf freeSlot)
open VerifiableInference.Desc (named Block)
open VerifiableInference.Desc.First (S LayOwn)
open Meaning.Reads

/-- What the record holds as heard by the layers' own rounds; none outside a layers' link. -/
def ownAt (s : S) : Option Own :=
  match s.here with
  | .lay a => a.own
  | _ => none

/-- Wherever the block's decide returns, what is held as heard is as it was. -/
def DecideKeepsOwn {Cl : Type} (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → ownAt s' = ownAt s

/-- The like of every named run of the block's claims. -/
def ClaimsKeepOwn {Cl : Type} (b : Block S Cl) : Prop :=
  ∀ c ∈ b.claims, ∀ n s cl s', c.2 n s = .ok (cl, s') → ownAt s' = ownAt s

/-- The like of every named run of the block's behind the batching. -/
def AfterKeepsOwn {Cl : Type} (b : Block S Cl) : Prop :=
  ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → ownAt s' = ownAt s

/-- The part of a record holds as heard what the record holds. -/
theorem part_own {s : S} {q : Desc.First.K4.Part} (h : part? s = some q) :
    ownAt s = q.1.own := by
  unfold part? at h
  unfold ownAt
  split at h
  · rename_i a ha
    obtain rfl := Option.some.inj h
    rw [ha]
  · cases h

/-- A record with a part laid back holds as heard what the part holds. -/
theorem setPart_own (s : S) (q : Desc.First.K4.Part) : ownAt (setPart s q) = q.1.own := rfl

/-- The layers' decide lays what is held as heard. -/
theorem blockAtS_lays {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (ℕ × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    ∃ o, ownAt s' = some o := by
  obtain ⟨a, fo, o, F, _, _, _, _, _, _, e⟩ := Desc.First.K4.blockAtS_hears h
  exact ⟨o, by rw [e]; rfl⟩

/-- A named run of claims of the layers' block, lifted to the carried record, keeps it. -/
theorem lifted_runOf_keeps (name : String) (f : Own → Fork → Option (Array Aff × Fork)) {s s' : S}
    {cl : List Aff}
    (h : ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn name f q).map fun y => (y.1, setPart s y.2)) = .ok (cl, s')) :
    ownAt s' = ownAt s := by
  cases hq : part? s with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    have h2 : ((runOf seatOwn name f q).map fun y => (y.1, setPart s y.2)) = .ok (cl, s') := h
    cases hd : runOf seatOwn name f q with
    | error e =>
      rw [hd] at h2
      cases h2
    | ok y =>
      rw [hd] at h2
      have e2 : (y.1, setPart s y.2) = (cl, s') := Except.ok.inj h2
      obtain ⟨o, fs, F, _, _, _, e⟩ :=
        (Desc.First.K4.runOf_ok seatOwn name f q y.2 y.1).mp hd
      rw [← (Prod.mk.inj e2).2, setPart_own, e, part_own hq]
      rfl

/-- **The layers' share: its runs of claims.** -/
theorem blockAtS_claimsKeep (p : Par) : ClaimsKeepOwn (blockAtS p) := by
  intro c hc n s cl s' h
  have hc' : c ∈ (block seatOwn p).claims.map fun c => (c.1, fun n t =>
      (named "the part is not there" (part? t)).bind fun q =>
        (c.2 n q).map fun y => (y.1, setPart t y.2)) := hc
  obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc'
  have h0' : c0 ∈ [("front", fun _ s => runOf seatOwn "K4.claims-front"
        ((if p.k3Runs then Desc.First.K4.formsFrontNoRows else Desc.First.K4.formsFront)
          p.P p.g) s),
      ("back", fun _ s => runOf seatOwn "K4.claims-back" Desc.First.K4.formsBack s)] := h0
  rcases List.mem_cons.mp h0' with rfl | h1
  · exact lifted_runOf_keeps _ _ h
  · obtain rfl := List.mem_singleton.mp h1
    exact lifted_runOf_keeps _ _ h

/-- **The layers' share: its run behind the batching.** -/
theorem blockAtS_afterKeeps (p : Par) : AfterKeepsOwn (blockAtS p) := by
  intro c hc s s' h
  have hc' : c ∈ (block seatOwn p).after.map fun c => (c.1, fun t =>
      (named "the part is not there" (part? t)).bind fun q => (c.2 q).map (setPart t)) := hc
  obtain ⟨c0, h0, rfl⟩ := List.mem_map.mp hc'
  have h0' : c0 ∈ [("free-slot", freeSlot seatOwn p.hp)] := h0
  obtain rfl := List.mem_singleton.mp h0'
  have h' : ((named "the part is not there" (part? s)).bind fun q =>
      (freeSlot seatOwn p.hp q).map (setPart s)) = .ok s' := h
  cases hq : part? s with
  | none =>
    rw [hq] at h'
    cases h'
  | some q =>
    rw [hq] at h'
    have h2 : ((freeSlot seatOwn p.hp q).map (setPart s)) = .ok s' := h'
    cases hd : freeSlot seatOwn p.hp q with
    | error e =>
      rw [hd] at h2
      cases h2
    | ok y =>
      rw [hd] at h2
      have e2 : setPart s y = s' := Except.ok.inj h2
      rw [← e2, setPart_own, Desc.First.K4.freeSlot_same seatOwn hd, part_own hq]

/-- The equation gives the premise hkeep of `blockAtS_planes`. -/
theorem hkeep_of_ownAt {s' s₂ : S} (h : ownAt s₂ = ownAt s') :
    ∀ a a₂ : LayOwn, s'.here = .lay a → s₂.here = .lay a₂ → a₂.own = a.own := by
  intro a a₂ ha ha₂
  unfold ownAt at h
  rw [ha, ha₂] at h
  exact h

/-- **The planes' three clauses from the layers' block at the carried record**, with the equation on
what is held as heard in hkeep's place. -/
theorem blockAtS_planes_own (ρ : Reading Cb.Gl.E) {p : Par} {s s' s₂ s₃ : S} {rs : List Fmt.RoundView}
    {cols : List (List (ℕ × List UInt64))} (hyes : (blockAtS p).decide s rs cols = .ok s')
    {run : ℕ → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : ℕ} {cl : List Aff}
    (hfront : run n s₂ = .ok (cl, s₃)) (hkeep : ownAt s₂ = ownAt s')
    (hT : p.P.tails = tailsOf p.P.y) {G : Array HPlan2} (hG : plansG p.P = .ok G)
    (hgp : G[p.g]? = some p.hp) :
    ∃ o, ownAt s' = some o ∧
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
  obtain ⟨a, o, ha, ho, H⟩ := blockAtS_planes ρ hyes hr hfront (hkeep_of_ownAt hkeep) hT hG hgp
  refine ⟨o, ?_, H⟩
  unfold ownAt
  rw [ha]
  exact ho

#print axioms blockAtS_planes_own
#print axioms blockAtS_lays
#print axioms blockAtS_claimsKeep
#print axioms blockAtS_afterKeeps
#print axioms hkeep_of_ownAt

end Meaning.Planes
