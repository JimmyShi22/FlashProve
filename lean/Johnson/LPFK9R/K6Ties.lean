-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/K6Ties.lean: THE OUTPUT HEAD's TWO TIES OF THE LINK's LAW, WHOLE, AT THE
SEAT: at a link of the description's first chain whose hearing block number 3 is of the kind K6: the
runs at the entries (3, «norm»), (3, «policy»), (3, «logits») stand under the runs of the output
head's kind's block, and the run at (3, «join») under its join: the fields tK6 and tJoin of
`HeadTies` (Johnson/Desc/First/Link/Law/PayHead.lean) to the letter, WITH EVERY PARAMETER NAMED off
the letters G₀ at which the lots' tables are made: h := G₀.W.hS; l := G₀.built.size − 1; piece := 4;
p := parOf G₀.W.hS (workAtW G₀.W); iU3: the value of G₀.W.H.tl.ix.U.getD 2 none. A theorem, after
the pattern of Johnson/LPFK9R/MergeTie.lean.

What is said. `k6_ties`: **the two ties.** Through `ties_at_seat`, `lot_of_kind` and the output
head's files' law on every block of its lot (Johnson/P4R/LotRuns.lean: `k6_lot_run`, `k6_lot_join`).

Limits. Two of 21 ties. The kind's block is named at the link's number G₀.built.size − 1: that this
is the l of the link at hand is not said here: `HeadTies`' own letter l stands for the number in the
block's place, and no law spends it. Under the seat's three yeses. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat
import Johnson.P4R.LotRuns

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At Under)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open ProofFile (Cl)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **THE OUTPUT HEAD's TWO TIES, WHOLE, AT THE SEAT.** -/
theorem k6_ties {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub)
    (hk : (kindsBeforeBatching sub (l == 0))[3]? = some KindName.K6)
    (iU3 : ℕ) (hU : B.G₀.W.H.tl.ix.U.getD 2 none = some iU3) :
    ∃ Lk, c.links[l]? = some Lk ∧
      (∀ name ∈ ["norm", "policy", "logits"], ∀ run, At Lk (3, name) run →
        ∃ r, (kind asClaim (seatAt B.G₀.W.hS iU3) (B.G₀.built.size - 1) 4
          (parOf B.G₀.W.hS (workAtW B.G₀.W))).claims.lookup name = some r ∧ Under run r) ∧
      ∀ run, At Lk (3, "join") run →
        Under run (VerifiableInference.Desc.K3.joinRun
          (VerifiableInference.Desc.K3.seatCalls asClaim)
          (callerKeys (parOf B.G₀.W.hS (workAtW B.G₀.W)) (seatAt B.G₀.W.hS iU3))) := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, _⟩ :=
    ties_at_seat hB hb hc l sub hl 3 .K6 hk (by decide) (by decide) (by decide)
  obtain rfl : L = P4.k6Lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  refine ⟨Lk, e1, fun name hn run h => ?_, fun run h => ?_⟩
  · obtain ⟨r', h1, hu⟩ := t1 name run h
    have hj : name ≠ "join" := by
      rintro rfl
      simp at hn
    obtain ⟨i', hi', h2⟩ := P4.k6_lot_run hb' h1 hj
    obtain rfl : i' = iU3 := Option.some.inj (hi'.symm.trans hU)
    exact ⟨r', h2, hu⟩
  · obtain ⟨r', h1, hu⟩ := t1 "join" run h
    obtain ⟨i', hi', h2⟩ := P4.k6_lot_join hb' h1
    obtain rfl : i' = iU3 := Option.some.inj (hi'.symm.trans hU)
    exact h2 ▸ hu

end LPFK9

#print axioms LPFK9.k6_ties
