-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/AllFrontAtBatch.lean: THE SMALLNESS TEST: `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean: the seventeen sentences on the data and the ledger in front
of the batching, from which three readings and seven tests of the verifier's test behind it follow)
AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, IN THE
GOALS' SCOPE: ELEVEN OF THE SEVENTEEN ARE SHOWN THERE WHOLE, TWO IN PART (five of pub's eight
fields, three of digits' four), FOUR NOT; WHAT IS LEFT IS ONE SMALLER NAMED PREMISE
(`FrontLeftOver`: eight sentences). An assembly: nothing is shown here that the called lemmas do not
show. None of the library's goals.

  `FrontLeftOver tl F g`   WHAT IS LEFT: a third of each matrix's rows of cells, rounded up, is at
                   most 2^64 · two forms that the digits' lookup has heard name no entry · BitsPub ·
                   the digits' array has the name "ZZ" · the verifier's three tests at the data in
                   front (forestHeld · both callHeld · pointsHeld)
  `colsFacts_sizes`   DgP.colsTest tl · sizesB tl ⊢ ColsFacts tl
  `wantPlan_of`   PiecePlanned tl w (Johnson/P1K8R/WantAtBatch.lean) ⊢ WantPlan tl w
  **`allFront_at_batch`**   the scope · the files read · an opening of the description · the
                   description's test on its plan · l < 25 · the built segment number l · (z, s)
                   reached at 14 l + 9, or 347 at the head's segment · s shows tl and G ·
                   FrontLeftOver tl G g ⊢ there are nbW, Wn with AllFront tl G g nbW Wn
  `forms_at_batch`   at the 24 segments in front of the head's: the digits' lookup has heard
                   something, and the two forms name no entry: two of the eight
SHOWN THERE, AND BY WHAT: zR · zB · laid, and of pub: ties · pieces · apart: `five_at_batch`
(Johnson/P1K8R/SecondFrontAtBatch.lean) · of pub: tau; tau: `drawn_at_batch` (DrawAtBatch.lean: 128
combinations) · of pub: cols: `apart_at_batch` (ApartAtBatch.lean), `sizes_at_batch`
(TiesAtBatch.lean), `colsFacts_of` (Johnson/Desc/K8/Honest/TiesLaidOf.lean) · bits · syms, and of
digits: rows, columns, virtual rows: `fronts_at_batch` (Johnson/Desc/K8/Honest/ArraysAtBatch.lean) ·
rest: `tiesRest_at_batch` (Johnson/Desc/K8/Honest/TiesRestAtBatch.lean) · coef · blocks:
`static_at_built`, `static_at_batch`, `three_of_static` (StaticAtBuilt.lean, StaticAtBatch.lean) ·
wants: `wants_128`; plan: `want_at_batch` (WantAtBatch.lean) · the two forms at the 24:
`digitsLeft_at_batch` (Johnson/P1K8R/NamedAtBatch.lean).
Limits. AN IMPLICATION STILL: OF `FrontLeftOver`'s EIGHT SIX ARE PAID BY NOBODY HERE, the two forms
at the head's segment neither; three of the eight are the verifier's own tests. PAYERS IN SIGHT, NOT
CALLED: the two forms at the head's segment: `digitsHeard_head`
(Johnson/P1K8R/HeadDigitsAtBatch.lean), where a ledger is open with its sizes, which `head_at_rch`
(BehindAtRch.lean) shows at another family of states. IN SCOPE ALONE: the full size's 25
segments; the first chain; the family of states from the description's own first state. Nothing says
that any state is reached, nor that a stand of the batching has such a state in front. That the
link's list has a member for each array, which `allHeld_at_link` asks beside AllFront, is not
shown of a state (at addTreesF's return: `addTreesF_syms`, Johnson/Desc/K8/Honest/SymbolsMade.lean).
No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ArraysAtBatch
import Johnson.Desc.K8.Honest.TiesRestAtBatch
import Johnson.P1K8R.NamedAtBatch
import Johnson.P1K8R.SecondFrontAtBatch
import Johnson.P1K8R.WantAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What is left of `AllFront` at a state reached in front of a batching. -/
structure FrontLeftOver (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Prop where
  rows : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64
  cEnd : g.cEnd.ents.isEmpty = true
  start : g.leaves.start.ents.isEmpty = true
  bitsPub : BitsPub tl g
  name : (F.trees.getD tl.ix.ZZ {}).name = "ZZ"
  forest : tl.forestHeld g = true
  calls : [0, 1].all (tl.callHeld g tl.zzBlocks) = true
  points : tl.pointsHeld g = true

/-- The facts on the columns, from two tests with code. -/
theorem colsFacts_sizes {tl : HTailF2} (hC : DgP.colsTest tl = true)
    (hS : _root_.P1K8.sizesB tl = true) : ColsFacts tl := by
  unfold _root_.P1K8.sizesB at hS
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hS
  obtain ⟨h1, h2⟩ := hS
  refine colsFacts_of tl hC (fun mu hmu => (h1 mu hmu).2) fun h0 => ?_
  rcases h2 with h2 | h2
  · exact absurd h0 h2
  · exact h2

/-- The plan's piece is the expected one. -/
theorem wantPlan_of {tl : HTailF2} {w : Want} (k : _root_.P1K8.PiecePlanned tl w) :
    WantPlan tl w :=
  ⟨k.mem, k.tree, k.row.symm, k.r0.symm, k.Rp.symm, k.c0.symm, k.Cp.symm⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING.** -/
theorem allFront_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    {g : Forest.Heard} (L : FrontLeftOver tl G g) :
    ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn := by
  obtain ⟨t1, a1, f1, f2, f3, f4, f5⟩ := _root_.P1K8.five_at_batch hS hR O hl h
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans a1)
  obtain ⟨t2, a2, -, htau⟩ := _root_.P1K8.drawn_at_batch hS hR O hl h
  obtain rfl : tl = t2 := Option.some.inj (ht.symm.trans a2)
  obtain ⟨t3, a3, -, hC⟩ := _root_.P1K8.apart_at_batch hS hR O hl h
  obtain rfl : tl = t3 := Option.some.inj (ht.symm.trans a3)
  obtain ⟨t4, a4, hZ⟩ := _root_.P1K8.sizes_at_batch hS hR O hl h
  obtain rfl : tl = t4 := Option.some.inj (ht.symm.trans a4)
  obtain ⟨hB, hY, d1, d2, d3⟩ := fronts_at_batch hS hR O hl e3 h ht hG
  obtain ⟨s1, s2, -⟩ := _root_.P1K8.three_of_static
    (_root_.P1K8.static_at_batch hS hR O hl e3 h ht hG (_root_.P1K8.static_at_built hS O hl e3))
  have hw := _root_.P1K8.wants_128 htau
  have hb := s1 _ _ hw
  refine ⟨_, _, ⟨f1, by rw [htau]; norm_num, L.rows, colsFacts_sizes hC hZ, f4, f3, L.cEnd,
    L.start⟩, f5 G hG _ _, fun e _ => f5 G hG _ e, hB, L.bitsPub, ⟨L.name, d1, d2, d3⟩, hY, f2,
    tiesRest_at_batch hS hR O hl e3 h ht, s2, hw, hb, by rw [htau]; norm_num,
    fun w hw' => wantPlan_of (_root_.P1K8.want_at_batch hS hR O hOk hl e3 h ht _ _ hw w hw'),
    L.forest, by have k := L.calls; rw [← hb] at k; exact k, L.points⟩

/-- At the 24 segments in front of the head's: what the digits' lookup has heard is there, and the
two forms name no entry. -/
theorem forms_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    (ht : s.tl? = some tl) :
    ∃ g, tl.heard = some g ∧ g.cEnd.ents.isEmpty = true ∧
      g.leaves.start.ents.isEmpty = true := by
  obtain ⟨g, h1, h2, h3⟩ := _root_.P1K8.digitsLeft_at_batch hS hR O hOk hl h
  rw [ht] at h1
  exact ⟨g, h1, by rw [h2]; rfl, by rw [h3]; rfl⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.colsFacts_sizes
#print axioms VerifiableInference.Desc.First.K8.Honest.wantPlan_of
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.forms_at_batch
