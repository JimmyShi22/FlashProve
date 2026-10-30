-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeftIs.lean: the two records that the statements on the kind K5 take of
the lookup are projections of the record and the promise of the lookup's kind (`K3Left`, `K3LeftAt`,
Johnson/Top/H/K3LeftStatement.lean).

Statements and proofs.
Main names:
  `left_is`: `K3Left` Reading.gl h lm F F' g rs gives `K3LeftIs` h lm F F' g rs
    (Johnson/Desc/First/Att/K05Left.lean): six of its eleven fields, and of zkRaw the equation.
  `leftAtIs_of_leftAt`: `K3LeftAt` gives `K3LeftAtIs` (Johnson/Desc/First/Att/K05EntryAt.lean).
  `entry_of_leftAt`: `K3LeftAt` at the two readers of `K3.seatCalls`, at Q := `Room` · ns nx
    (Forest.elems x.fs + (slotsOf (script own) + k)), gives `K5Entry` at `seatSO` for some F, F', g
    and rs (Johnson/Desc/First/Att/K05Entry.lean).
Limits: that a yes of the lookup's block leaves `K3LeftAt` is a statement on that kind; it is not
imported here. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement
import Johnson.Desc.First.Att.K05EntryAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.OnPublicFiles (K3Left K3LeftAt)

/-- **Our record is a projection of the lookup's kind's.** -/
theorem left_is {h : Forest.Shape} {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds Cb.Gl.E}
    (L : K3Left Reading.gl h lm F F' g rs) : K3LeftIs h lm F F' g rs :=
  ⟨L.heardIs, L.padLeft, L.shape, L.zx, L.zy, fun c hc => (L.zkRaw c hc).2⟩

/-- **So is our promise.** -/
theorem leftAtIs_of_leftAt {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Q : Fork → Prop} {s : S} (A : K3LeftAt fork heard h lm first Q s) :
    K3LeftAtIs fork heard h lm first Q s := by
  obtain ⟨F, F', g, rs, q, hn, L, hh, hf⟩ := A
  exact ⟨F, F', g, rs, q, hn, left_is L, hh, hf⟩

/-- **The lookup's sharp promise gives the record at the entry of the kind K5**, at the two seats. -/
theorem entry_of_leftAt {Cl : Type} (claim : Aff → Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (own : Params.AttentionRounds) (s : First.S) (ns nx k : ℕ)
    (A : K3LeftAt (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
      x.fs x.lm x.F.next (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script own) + k))) s) :
    ∃ F F' g rs, K5Entry seatSO (VerifiableInference.Desc.K3.seatCalls claim).fork
      (VerifiableInference.Desc.K3.seatCalls claim).heard x own s ns nx k F F' g rs :=
  entry_at_seats claim x own s ns nx k (leftAtIs_of_leftAt A)

end VerifiableInference.Desc.First.Att.P
