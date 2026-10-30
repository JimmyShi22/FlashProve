-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsTail.lean.
The smallness test's lookup on the digits: which claims the byte-level routines add for it, and in
which order.

In the smallness test the lookup's claims on the planes and on the keys are written out by hand
(HTailF2.linJoin9, HTailF2.linBits9, OnBytes/Model/Tail.lean), as claims with runs on long stretches
of entries, behind Forest.objects.

States:
  added_t2Lin: t2Lin adds the one claim of its form and its runs.
  join9_added: HTailF2.linJoin9 adds one claim: the join's constant less the hidden value at the key
    side's end, with the pieces' runs.
  bits9_added: HTailF2.linBits9 adds three claims, in this order: the row of the leaves' sumcheck
    with the run at the first virtual row of the planes' matrix; the slot of the bits' shown value
    with the run at the second; the counts' constant with the run at the third.
  tailLook_added: Forest.objects, linJoin9, linBits9, each run from what the one before leaves, add:
    the record's rows; the join; these three. So here the join stands BEFORE the planes' three.
  Each asks that the runs return, the first from a state with one coefficient for each slot;
  tailLook_added also that the record is the smallness test's (tl.heard = some g). "Adds" is
  Fo.Added (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean): an identity of values at the state's theta.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, what the runs' virtual rows hold, or that HTailF2.objectsF
runs the three routines in turn: that is read off its definition.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsLook
import OnBytes.Tie.Pv.Lookup.Ends.FoTailBits
import OnBytes.Tie.Pv.Lookup.Ends.FoTailJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Forest

/-- t2Lin adds one claim. -/
theorem added_t2Lin {a : Aff} {runs : Array Run2} {F G : Fork} {c c' : Ctx}
    (h : t2Lin a runs F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) : Added F G [(a, runs)] where
  total := fun K _ ρ W => by
    rw [(t2Lin_total ρ W a runs F G c c' hs h).2.1]
    simp [clsValue, sumFrom, Cl.value]
  nClaim := (t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs h).2.2.1
  theta := (t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs h).2.2.2.1
  ns := (t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs h).2.2.2.2.1
  sized := (t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs h).2.2.2.2.2.1

/-- The join, written out by hand. -/
theorem join9_added {tl tl' : HTailF2} {F G : Fork} {c c' : Ctx}
    (h : tl.linJoin9 F c = .ok ((tl', G), c')) (hs : F.LS.size = F.ns) :
    ∃ (g : Heard) (runs : Array Run2), tl.heard = some g ∧ runs.toList = joinRuns tl g ∧
      tl' = { tl with joinObj9 := some F.nClaim } ∧
      Added F G [(Aff.ofConst (joinConst tl g) - g.cEnd, runs)] := by
  obtain ⟨g, runs, F1, c1, h1, _, h3, h4, h5, h6⟩ := linJoin9_cut tl tl' F G c c' h
  have a1 := added_t2Lin h4 hs
  obtain ⟨_, l2, e2, a2⟩ := (Quiet.paid g.owedJoin) _ _ _ _ _ h5 a1.sized
  obtain rfl := List.length_eq_zero_iff.mp e2
  have := a1.trans a2
  rw [List.append_nil] at this
  exact ⟨g, runs, h1, h3, h6, this⟩

/-- The planes' three, written out by hand. -/
theorem bits9_added {tl tl' : HTailF2} {F G : Fork} {c c' : Ctx}
    (h : tl.linBits9 F c = .ok ((tl', G), c')) (hs : F.LS.size = F.ns) :
    ∃ (g : Heard), tl.heard = some g ∧
      Added F G [(g.leaves.rowForm oneE {}, #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
          (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))]),
        (Aff.slot g.sBit, #[bzRun tl 1 (subE zeroE oneE)
          (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))]),
        (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
          #[bzRun tl 2 oneE (pinW tl)])] := by
  obtain ⟨g, row, p', F1, F2, F3, F4, c1, c2, c3, c4, h1, h2, h3, h4, h5, h6, _⟩ :=
    linBits9_cut tl tl' F G c c' h
  obtain ⟨_, _, _, _, _, _, rfl, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h2
  obtain ⟨_, l0, e0, a0⟩ := quiet_pscRow _ _ _ _ _ _ _ _ h2 hs
  obtain rfl := List.length_eq_zero_iff.mp e0
  have a1 := added_t2Lin h3 a0.sized
  have a2 := added_t2Lin h4 a1.sized
  have a3 := added_t2Lin h5 a2.sized
  obtain ⟨_, l4, e4, a4⟩ := quiet_planesAdded g _ _ _ _ _ h6 a3.sized
  obtain rfl := List.length_eq_zero_iff.mp e4
  have := (((a0.trans a1).trans a2).trans a3).trans a4
  exact ⟨g, h1, by simpa using this⟩

/-- The lookup's claims in the smallness test, in the order of the three routines. -/
theorem tailLook_added {tl tl1 tl2 : HTailF2} {g : Heard} {F F1 G1 G2 : Fork} {c c0 c1 c2 : Ctx}
    (hg : tl.heard = some g) (hO : Forest.objects g F c = .ok (((), F1), c0))
    (hJ : tl.linJoin9 F1 c0 = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (hs : F.LS.size = F.ns) :
    ∃ runs : Array Run2, runs.toList = joinRuns tl g ∧
      Added F G2 ((g.rows.toList.map fun f => (f, #[])) ++
        [(Aff.ofConst (joinConst tl g) - g.cEnd, runs),
          (g.leaves.rowForm oneE {}, #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
            (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))]),
          (Aff.slot g.sBit, #[bzRun tl 1 (subE zeroE oneE)
            (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))]),
          (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
            #[bzRun tl 2 oneE (pinW tl)])]) := by
  have a0 := objects_added hO hs
  obtain ⟨g1, runs, e1, e2, e3, a1⟩ := join9_added hJ a0.sized
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e1)
  obtain ⟨g2, e4, a2⟩ := bits9_added hB a1.sized
  have hh : tl1.heard = tl.heard := by rw [e3]
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans (hh.symm.trans e4))
  rw [e3] at a2
  have := (a0.trans a1).trans a2
  exact ⟨runs, e2, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using this⟩

end Fo
