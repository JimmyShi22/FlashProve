-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LeftProof.lean: the kind "lookup" (K3): WHAT STANDS BEHIND A YES, PROVED BUT FOR ONE
NAMED PREMISE: K3LeavesAtCalls (Johnson/Top/H/K3LeftStatement.lean) from the laws that lie on
K3.block's decide. Theorems with their proofs.

Where each field of K3Left comes from. heardIs, padLeft: k3DecideHears_calls
(Johnson/Top/H/K3DecideHearsAt.lean). shape: its ShapeOf, which fixes the shape (shapeOf_unique,
shape_some). zx, zy, zkSize, zkRaw: block_point_calls (Johnson/Desc/First/Look/K3PointAtSeats.lean).
zkLen: decide_zk_size (Johnson/Top/H/K3KeySizes.lean). eRaw: `lkPad_e`, here: the record that lkPad
returns holds the weights so, by its own text. cEndEnts, cEndFilled: THE NAMED PREMISE `LkPadCEnd`:
a yes of lkPad from a ledger with its sizes leaves a form for the join that names no entry of a
virtual row and whose slots are filled and below the number of slots. NOT PROVED HERE.

Main names: `LkPadCEnd` · `lkPad_e` · `k3LeavesAtCalls_of` · `k3DecideLeaves_mono` (a decide that
says yes only where another does leaves what that one leaves).

Limits. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement
import Johnson.Top.H.K3KeySizes
import Johnson.Top.H.K3KeyPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- The record that lkPad returns holds the calls' weights as the library's callWeight at zy. -/
theorem lkPad_e (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) :
    g.e = (Array.range g.shape.NC).map (Forest.callWeight g.shape g.zy) := by
  obtain ⟨M, hc⟩ := pad_cut calls pub lid F F' t u g h
  rw [hc.heard]
  rfl

/-- **What is still owed on the form left for the join.** NOT PROVED HERE. -/
def LkPadCEnd : Prop :=
  ∀ (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard), lkPad calls pub lid F t = some (g, F', u) → OnBytes.PscRun.Sized F →
    g.cEnd.ents = #[] ∧ FilledA F' g.cEnd

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- A decide that says yes only where another does leaves what that one leaves. -/
theorem k3DecideLeaves_mono {S : Type} {fork : S → Option Fork}
    {heard : S → Option Forest.Heard} {h : Forest.Shape}
    {d d' : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S}
    (hyes : ∀ s rs cols s', d' s rs cols = .ok s' → d s rs cols = .ok s')
    (H : K3DecideLeaves fork heard h d) : K3DecideLeaves fork heard h d' :=
  fun K _ ρ lm s s' rs cols hw hd => H K ρ lm s s' rs cols hw (hyes s rs cols s' hd)

/-- **K3.block's decide at the calls' seat leaves the record**, under the one named premise. -/
theorem k3LeavesAtCalls_of (hC : Fo.Tp.LkPadCEnd) : K3LeavesAtCalls := by
  intro Cl claim piece laid before p guests h hsh K _ ρ lm s s' rs cols hw hdec
  obtain ⟨F, F', g, hF, hF', hg, -, hS⟩ :=
    k3DecideHears_calls claim piece laid before p guests K ρ lm s s' rs cols hw hdec
  refine ⟨F, F', g, hF, hF', hg, fun hSz => ?_⟩
  obtain ⟨hShape, hPad, hI⟩ := hS hSz
  obtain rfl : g.shape = h := shapeOf_unique hShape (shape_some p h hsh)
  -- the points, as machine words
  obtain ⟨g1, hg1, -, hx, hy, hk, hz⟩ :=
    Desc.K3.block_point_calls claim piece laid before p guests hdec
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans hg1)
  obtain ⟨g2, hg2, hn⟩ := decide_zk_size (Desc.K3.seatCalls claim) piece laid before p guests
    (Desc.K3.seatCalls_reads claim) s s' rs cols hdec
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans hg2)
  -- lkPad's own yes
  obtain ⟨F3, F3', g3, t, hF3, hn3, hl, e3⟩ :=
    decide_lkPad (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hdec
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF3]
    rfl
  obtain rfl : F = F3 := Option.some.inj (hF.symm.trans hF3)
  have hg3 : (Desc.K3.seatCalls claim).heard s' = some g3 := by
    rw [e3]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn3
  have hF3' : (Desc.K3.seatCalls claim).fork s' = some F3' := by
    rw [e3]
    exact seatCalls_keeps claim _ _ _ hsome hn3
  obtain rfl : g = g3 := Option.some.inj (hg.symm.trans hg3)
  obtain rfl : F' = F3' := Option.some.inj (hF'.symm.trans hF3')
  obtain ⟨c1, c2⟩ := hC _ _ _ _ _ _ _ _ hl hSz
  exact
    { heardIs := hI, padLeft := hPad, shape := rfl, zx := hx, zy := hy, zkSize := hk, zkRaw := hz,
      zkLen := hn, eRaw := Fo.Tp.lkPad_e _ _ _ _ _ _ _ _ hl, cEndEnts := c1, cEndFilled := c2 }

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.lkPad_e
#print axioms VerifiableInference.OnPublicFiles.k3DecideLeaves_mono
#print axioms VerifiableInference.OnPublicFiles.k3LeavesAtCalls_of
