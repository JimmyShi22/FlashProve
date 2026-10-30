-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6KeysInScope.lean.
WHAT IT IS NOT. Facts on public parameters alone: nothing on a state of the verifier, nothing on
what is sent. UNDER THE LIBRARY's publicOf ALONE, at public files in the goals' scope: the full
size. Nothing on soundness, on completeness or on hiding.
WHAT IT IS. AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TEST keysFitB (Law/K6GivenOfLeft.lean)
ACCEPTS: six calls at least (in scope: six); the lookup's first point has ls + lt coordinates at
least; each call's key point has as many coordinates as the head's text asks. So the premise on
public numbers under which the head's letters are read in front of the output head's own rounds is
met there.
  layout_n              in every layout of the head that the program's text makes: call q's number
                        of key coordinates, by the lookup's shape, is the layout's number of column
                        coordinates of that call and lt more.
  headKeysFit_in_scope  MAIN. CONDITIONAL on the scope's three premises.
  headKeysFit_at_place  the same at whatever shape the place of the lookup on the calls makes.
CALLED: layout_fs, lookups_is, lookOne_n, fs_in_scope (Law/HeadFsWritten.lean), numbers_in_scope
(Goal/Meaning/HeadCondScope.lean), cols_in_scope (Goal/Meaning/HeadColsScope.lean), calls_place
(Law/K6PubInScope.lean), publicSteps_of (Desc/Ok/PlanWritten/PublicAtSteps.lean).
OF THE FOLDER Johnson/Goal/ it imports Goal/Meaning/HeadColsScope.lean, for the two lemmas of that
folder named above; nothing else of it is called.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6GivenOfLeft
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Goal.Meaning.HeadColsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Head (Shape HL)
open VerifiableInference.Desc.First.Look (placeAt)

/-- In every layout of the head that the program's text makes: call q's key point, by the shape of
the lookup on the calls, has as many coordinates as the layout's columns of that call and the
positions ask. -/
theorem layout_n {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) (q : Nat) (hq : q < L.calls.size) :
    ((L.fs.calls[q]?).map (·.n)).getD 0 = (L.calls.getD q default).lJ + h.lt := by
  obtain ⟨L0, calls, fs0, pub, _, _, hc, _, _, hcl, hfs⟩ := layout_fs hy
  have hq' : q < calls.length := by
    rw [hc] at hq
    simpa using hq
  rw [hfs]
  show ((L.cl[q]?).map (·.n)).getD 0 = _
  rw [hcl, lookups_is, hc]
  simp only [Array.getElem?_mapIdx, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hq', Option.map_some, Option.getD_some,
    Array.getD_eq_getD_getElem?]
  exact lookOne_n _ _ _ _

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TEST keysFitB ACCEPTS**, at the shape of the
lookup on the head's calls. -/
theorem headKeysFit_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    @keysFitB (parOf X.hS (workOf X)).sizes (parOf X.hS (workOf X)).floor X.HLy.fs = true := by
  have F := fs_in_scope hZ hR h
  have N := numbers_in_scope hZ hR h
  have hy := (VerifiableInference.PlanWritten.publicSteps_of h).head
  have hsz : X.HLy.calls.size = 6 := by
    obtain ⟨L0, calls, fs0, pub, _, _, hc, _, _, hcl, hfs⟩ := layout_fs hy
    have e : X.HLy.fs.calls.size = calls.length := by
      rw [hfs]
      show X.HLy.cl.size = _
      rw [hcl, Array.size_mapIdx, lookups_is]
      simp
    rw [hc, List.size_toArray, ← e]
    exact F.calls
  unfold keysFitB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨by rw [F.NC], ?_⟩, fun c hc => ?_⟩
  · show X.hS.la - X.hS.lt + X.hS.lt ≤ X.HLy.fs.dT
    rw [F.dT, N.la, N.lt]
    decide
  · rw [layout_n hy c (by rw [hsz]; exact hc), cols_in_scope hZ hR h c hc]
    rfl

/-- The same in the letters in which k6Front_of_items asks it. In scope there is just one such place
and shape: calls_place. -/
theorem headKeysFit_at_place (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    ∀ p3 h3, placeAt X 24 false = some p3 → p3.shape = some h3 →
      @keysFitB (parOf X.hS (workOf X)).sizes (parOf X.hS (workOf X)).floor h3 = true := by
  intro p3 h3 e3 s3
  obtain ⟨p, e, s, _, _⟩ := calls_place hZ h
  obtain rfl : p = p3 := Option.some.inj (e.symm.trans e3)
  obtain rfl : X.HLy.fs = h3 := Option.some.inj (s.symm.trans s3)
  exact headKeysFit_in_scope hZ hR h

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.layout_n
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.headKeysFit_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.headKeysFit_at_place
