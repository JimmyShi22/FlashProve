-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RealPiece.lean: THEOREM: the piece that holds THE REAL BATCHING BLOCK K9.batch X p, at the
format's own written rounds, has the form that the rule of composition asks of a block
(Piece.GoodIn), from "all equations of the segment hold at the data to which the prover is bound"
to "the runs behind the batching return, and the ledger's value, read at the state that they return,
is 0 at these data".

It joins three things: Law/BatchAdds.lean (the law's premise "batch" at the real block), the law of
a segment's batching in the form of a piece (Johnson/Desc/LinkLaw3.lean: batch_goodIn) and the
carriage to raw challenges from the degree alone (Johnson/Desc/LinkLaw9.lean: reads_allErr).
  premises_real    the law's eight premises at a segment whose batching is K9.batch X p: "batch" is
                   paid; the other seven are hypotheses, on the other kinds' letters and runs.
  batch_goodIn_real   the piece.
WHAT IS LEFT, ALL BY NAME: Fits (the lens; the others' letters at the draw and at the adding) · plan
· square · later · exps · runs · after · full (the other kinds') · the pin (huniq), hcarry, hready,
hhands, hext (whoever lays the chain's relations) · positions of at most 64 bits · no drawn element
in the rounds put behind · the reading one to one on typed elements · the piece's errors at least
allErr at the degree d.

-/
import Johnson.Desc.LinkLaw9
import Johnson.Desc.First.Batch.Law.BatchAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where batch)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {T P K W : Type} [Field K] [Fintype K] [DecidableEq K] {F : Frame}

omit [Fintype K] [DecidableEq K] in
/-- **The law's premises at a segment whose batching is the real block.** -/
theorem premises_real (ρ : Reading K) (X : Lens T) (O : Others T P K) (p : Where)
    (L : Link T Claim) (ft d : ℕ) (hb : L.batch = batch X p) (HF : Fits X O p)
    (plan : L.laidB.planOk = true) (square : (semOf ρ X O).Square)
    (later : (semOf ρ X O).LaterOk)
    (exps : ∀ s, (semOf ρ X O).ready s → (semOf ρ X O).ExpsOk L.order ((semOf ρ X O).fixed s) d)
    (runs : (semOf ρ X O).RunsFixed L.hear) (after : (semOf ρ X O).AfterKeeps L.hear)
    (full : (semOf ρ X O).AfterFull L) : (semOf ρ X O).Premises L ft d where
  plan := plan
  square := square
  later := later
  exps := exps
  runs := runs
  batch := by
    rw [Link.batchB, hb]
    exact batchAdds ρ X O p _ ft HF
  after := after
  full := full

/-- **The real batching block's piece is good.** -/
theorem batch_goodIn_real (ρ : Reading K) (X : Lens T) (O : Others T P K)
    (L : Link T Claim) (d : ℕ) (H : (semOf ρ X O).Premises L F.ft d)
    (q : Piece (ckP .two) F T Claim W) (hq : q.b = below L.batchB)
    (hext : ∀ a τ w, q.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (Bnd : T × F.E.Str → W → Bound K → Prop)
    (hready : ∀ a, on a → (semOf ρ X O).ready a.1)
    (hhands : ∀ a τ b, on a → q.ior.red.out a τ = some b → on' b)
    (huniq : ∀ a w w' y y', on a → Bnd a w y → Bnd a w' y' → y = y')
    (hcarry : ∀ a τ b w y, on a → q.ior.red.out a τ = some b → Bnd b w y → Bnd a w y)
    (hlog : ∀ r ∈ q.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ q.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => ρ.val (E.ofTriple (toU3 a)))
    (herr : Err.le (allErr (fun _ _ => d) 0 q.ds) q.err) :
    q.GoodIn on on'
      (fun a w => ∃ y, Bnd a w y ∧ (semOf ρ X O).AllEq L.hear ((semOf ρ X O).fixed a.1) y)
      (fun b w => ∃ y, Bnd b w y ∧
        ∃ t, afterIn L.hear L.orderAfter b.1 = .ok t ∧ (semOf ρ X O).one t b.1 y = 0) :=
  batch_goodIn (semOf ρ X O) L d H q hq hext on on' Bnd hready hhands huniq hcarry
    (reads_allErr q (semOf ρ X O).rd d hlog hback hinj herr)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.premises_real
#print axioms VerifiableInference.Desc.K9L.batch_goodIn_real
