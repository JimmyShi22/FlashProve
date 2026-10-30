-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FourRunsScope.lean: Law/FourRunsTie.lean's armCellIn_K6_at_table AT ALL
PUBLIC FILES IN THE GOALS' SCOPE: its eight premises on public numbers (the verifier's own maker
returns the public parameters; the full size; the layers' three structures of numerals; the
geometry of the head's cells; the four ranges lie inside the sizes; the tests on the numbers of the
list of rounds) are paid from the scope's three. One theorem.

WHAT IT IS NOT. An implication. Nothing on soundness. What stays a premise is what
armCellIn_K6_at_table's docstring and Law/FourRunsTie.lean's head name: on the verifier's two
states, the readers, the tie, the run's letters, the arrays' names and the riding of the symbol
arrays' cells. No values are shown at which these hold together.
LETTERS. No letter stands under "there is" in the conclusion.

-/
import Johnson.Desc.Kinds.Law.FourRunsTie
import Johnson.Desc.Kinds.Law.HeadRangesOfNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Verify (borderOf publicOf)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab)

/-- **THE HEAD's HALF OF THE EXCHANGE AT THE HEAD's FOUR RUNS, FROM THE TIE, AT ALL PUBLIC FILES
IN THE GOALS' SCOPE.** The letters are armCellIn_K6_at_table's. -/
theorem armCellIn_K6_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (hX : publicOf Z.pol Z.KL lay = .ok X)
    (l piece blk : Nat) (states : Nat → List (RunOf S))
    (KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk)
    (Rd : Readers) (own : List (Nat × Nat)) (s s' : S) (a b : K9.Part)
    {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (ms : List Mem)
    (N : Numbers) (m : Nat) (z : P) (w : Wit Cells Tok MsgT)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s)
    (hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K)
    (hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩))
    (hCome : TablesCome X s s') (hb : K9.segAt? s' = some b)
    (htie : First.K8.TieAt (cellsAt cs arr ms N m (z, s')) s' w)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf X]? = some cU)
    (hlab : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))))
    (hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ (N.group m) b (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c)
    (name : String) (hn : K6Name name) :
    Sound.ArmCellIn Rd own (N.group m) blk name s a b (seatTab cs arr ms w) (uHeadK6 X 24) := by
  have B := OnBytes.Road.Hd.public_of_core hX (OnBytes.Road.Hd.core_of_scope hZ hR hX)
  exact armCellIn_K6_at_table hX B.full B.switches B.sized B.sized2
    (Came.inRanges_in_scope hZ hR hX (workOf X)) (Came.inSizes_in_scope hZ hR hX) l piece blk
    states KS Rd own s s' a b cs arr ms N m z w hRd (InScope.ok_in_scope hZ hR hX (workOf X)) hT
    hbare harr hwide hRun hCome hb htie cU hArr hlab hride name hn

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_K6_in_scope
