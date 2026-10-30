-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Added8.lean: WHAT A YES OF THE BATCHING BLOCK OPENS, AS ONE STRUCTURE ON
LEDGERS AND LISTS OF CLAIMS; AND, BEHIND THE ADDING, THE VALUE OF THE WEIGHT OF A DIGIT IN THE TIES'
ROW OF THE DIGITS' ARRAY AND OF A COLUMN OF A MATRIX's ARRAY OF SYMBOLS, WHERE NO PLAIN CLAIM BEARS
ON THE ENTRY. Definitions and lemmas; none of the library's goals. No prover stands in them; nothing
on completeness, soundness or hiding.

  `Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀`   Y: the ledger in front of the adding: it bears
      nothing, and its weights are words below the prime; G: Y with the claims added: plain claims
      fr, the list "K8.equations" k8, plain claims bk
  `PlainOff fr k8 bk t r i`   no claim of fr, none of the first four of k8 and none of bk bears on
      entry i of virtual row r of array t (`coefOn`, Johnson/Desc/K8/Honest/FallCount.lean)
  `Added8.core`, `termsSum_none`   the adding leaves the batching element, the plan's number and the
      frame; the weights behind it are words below the prime
  **`Added8.weight`**   under `PlainOff`, at a virtual row that begins at column 0: the weight's
      value is what the list's ties and reads part by in the two worlds
  **`Added8.weight_tie`**, **`Added8.weight_sym`**   so at a digit in the ties' row: one monomial in
      the batching element; at a column of a matrix's array of symbols: minus the tie's power times
      the column's sum
  **`behind_open`**   behind a yes of the batching block at the challenge x, under `Gathers`: the
      state holds data and a ledger that stand in `Added8`; Y's batching element reads as x; its
      plan's number and shape are those of the ledger in front; the plain claims' coefficients are
      the letters of `Gathers`. ITS PROOF IS THE FIRST STEPS OF `behind_total`
      (Johnson/Desc/K8/Honest/BehindTotal.lean), WRITTEN ONCE MORE, so that later lemmas call this
      one
By: `total_cut` (Johnson/Desc/K8/Honest/WeightAt.lean) · `tie_cut` (LinkedFew.lean) · `sym_cut`
(SymbolsFew.lean) · `termsSum_column`, `termsSum_fromOn` (FallTerms.lean) · `total_oneAt`
(FallAlg.lean) · `addList_ok`, `okW_iff`, `okW_of_sums`, `okTrees_empty` (OkWeights.lean) ·
K9L.addAll_total, total_of_sums, total_of_empty (Johnson/Desc/First/Batch/Law/Ledger.lean) ·
K9L.drawnClean_ok (AtBlock.lean).
Limits. BY VALUES. `PlainOff`, `Gathers`, `tiesLaid`, `SymAt` and "begins at column 0" are premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.OkWeights
import Johnson.Desc.K8.Honest.LinkedFew
import Johnson.Desc.K8.Honest.SymbolsFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **What a yes of the batching block opens**, on ledgers and lists alone: Y: the ledger in front
of the adding; it bears nothing; G: Y with the claims added: plain claims fr, the list
"K8.equations" k8 (made at the data tl, the tables funs and a ledger F₁ with Y's batching element,
plan's number and frame; it returns the data tl'), plain claims bk. -/
structure Added8 (tl tl' : HTailF2) (funs : Array HFun) (Y G F₁ F₂ : Fork)
    (fr k8 bk : List Claim) (n₀ : Nat) : Prop where
  add : K9.addList Y (fr ++ k8 ++ bk) = .ok G
  zero : ∀ W : World Cb.Gl.E, Y.total Reading.gl W = 0
  n0 : Y.nClaim = 0
  sz : Y.LS.size = Y.ns
  eq : equations n₀ tl funs F₁ = .ok (tl', F₂, k8)
  th : F₁.theta = Y.theta
  pl : F₁.planClaimsF = Y.planClaimsF
  frame : treesFrame F₁.trees = treesFrame Y.trees
  plainA : ∀ (j : Nat) (cl : Claim), (fr ++ k8.take 4)[j]? = some cl → cl.eqFirst = none
  plainB : ∀ (j : Nat) (cl : Claim), bk[j]? = some cl → cl.eqFirst = none
  ok : OkW Y

/-- No plain claim bears on the entry. -/
def PlainOff (fr k8 bk : List Claim) (t r i : Nat) : Prop :=
  (∀ (j : Nat) (cl : Claim), (fr ++ k8.take 4)[j]? = some cl → coefOn cl t r i = 0) ∧
    ∀ (j : Nat) (cl : Claim), bk[j]? = some cl → coefOn cl t r i = 0

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- What the adding leaves, and that the weights behind it are words below the prime. -/
theorem Added8.core (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) :
    G.theta = Y.theta ∧ G.planClaimsF = Y.planClaimsF ∧
      treesFrame G.trees = treesFrame Y.trees ∧ OkW G := by
  obtain ⟨-, eG, -, frG⟩ := K9L.addAll_total Reading.gl allZero _ Y G A.sz
    (K9L.addList_older _ Y G A.add)
  exact ⟨by rw [eG], by rw [eG], frG, (okW_iff _).2 (addList_ok A.add ((okW_iff _).1 A.ok))⟩

theorem termsSum_none (m c : Nat) (x : Cb.Gl.E) :
    K9L.termsSum (fromOn (fun _ => (0 : Cb.Gl.E)) m c) x = 0 := by
  rw [termsSum_fromOn]
  simp only [mul_zero]
  exact runSum_zero m c

/-- **The weight on an entry on which no plain claim bears: what the ties and reads part by.** -/
theorem Added8.weight (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (t r i : Nat)
    (h0 : ((Y.trees.getD t {}).rows.getD r {}).L0 = 0) (hoff : PlainOff fr k8 bk t r i) :
    ∃ tl1 : HTailF2, Powered tl1 F₁.theta ∧
      (∀ mu, mu < tl1.NM → tl1.gamV.getD mu #[] = gamAt tl1 mu) ∧
      tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
      Reading.gl.val ((weightsOf G t r).getD i zeroE) =
        (((List.range tl1.NM).map (tieTerm Reading.gl (oneAt t r i) tl1 F₁)).sum +
            sumFrom (readTerm Reading.gl (oneAt t r i) tl1 F₁) 0 (readsList tl1 funs)) -
          (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
            sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs)) := by
  obtain ⟨tl1, hP, hgam, etl, hcut⟩ := total_cut (fun _ => 0) tl tl' funs Y G F₁ F₂ fr k8 bk n₀
    t r i fr.length bk.length (K9L.addList_older _ Y G A.add) A.zero A.n0 A.sz A.eq A.th A.pl
    A.frame rfl rfl (fun j cl hj => ⟨A.plainA j cl hj, hoff.1 j cl hj⟩)
    (fun j cl hj => ⟨A.plainB j cl hj, hoff.2 j cl hj⟩)
  refine ⟨tl1, hP, hgam, etl, ?_⟩
  have h0G : ((G.trees.getD t {}).rows.getD r {}).L0 = 0 := by
    rw [L0_of_shape, shape_of_frame _ _ A.core.2.2.1, ← L0_of_shape]
    exact h0
  rw [← total_oneAt Reading.gl G t r i h0G, hcut, termsSum_none, termsSum_none, zero_add,
    zero_add]

/-- **The weight of a digit in the ties' row: one monomial.** -/
theorem Added8.weight_tie (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀)
    (hL : tiesLaid tl = true) (mu plane i : Nat) (hmu : mu < tl.NM) (hp : plane ≤ 1)
    (hi : i < (tl.mats.getD mu {}).m)
    (h0 : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowTies {}).L0 = 0)
    (hoff : PlainOff fr k8 bk tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) :
    Reading.gl.val ((weightsOf G tl.ix.ZZ tl.zzRowTies).getD
        (plane * tl.mz + tl.off.getD mu 0 + i) zeroE) =
      Reading.gl.val Y.theta ^ (Y.planClaimsF + firstOf tl mu + tl.stepF * (i / 3)) *
        (((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3)) := by
  obtain ⟨tl1, hP, -, etl, hw⟩ := A.weight _ _ _ h0 hoff
  rw [hw, tie_cut A.eq etl hP hL mu plane i hmu hp hi, A.th, A.pl]

/-- **The weight of a column of a matrix's array of symbols: minus the tie's power times the
column's sum.** -/
theorem Added8.weight_sym (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (mu c : Nat)
    (h : SymAt tl mu c)
    (h0 : ((Y.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L0 = 0)
    (hoff : PlainOff fr k8 bk (tl.gtTree.getD mu 0) 0 c) :
    Reading.gl.val ((weightsOf G (tl.gtTree.getD mu 0) 0).getD c zeroE) =
      -(Reading.gl.val Y.theta ^ (Y.planClaimsF + firstOf tl mu) *
        ∑ u ∈ Finset.range tl.tau,
          signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0) *
            Reading.gl.val Y.theta ^ u) := by
  obtain ⟨tl1, hP, -, etl, hw⟩ := A.weight _ _ _ h0 hoff
  rw [hw, sym_cut A.eq etl hP mu c h, termsSum_column, A.th, A.pl]

end

/-- **BEHIND A YES OF THE BATCHING BLOCK AT THE CHALLENGE x**: the parts, once for all. -/
theorem behind_open (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (Y G F₁ F₂ : Fork) (fr k8 bk : List Claim) (n₀ : Nat),
      tlForkP.get? t' = some (tl', G) ∧ Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀ ∧
      Reading.gl.val Y.theta = x ∧ Y.planClaimsF = F.planClaimsF ∧
      shapeOf Y.trees = shapeOf F.trees ∧ fr.length = nf ∧ bk.length = nb ∧
      (∀ c cl, (fr ++ k8.take 4)[c]? = some cl → ∀ t r i, coefOn cl t r i = a c t r i) ∧
      ∀ c cl, bk[c]? = some cl → ∀ t r i, coefOn cl t r i = a (nf + k8.length + c) t r i := by
  obtain ⟨t, e, cls, y', G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p g s t' (chiAt x) (hb _ _ hbt)
  obtain ⟨xx, yy, tl', fr, k8, bk, n₀, F₁, F₂, gx, gy, gcore, gfr, gtl, gcls, gnf,
    gnb, geq, gth, gpl, gfr1, gA, gB⟩ := hG.each (chiAt x) t e cls hdr hg
  obtain rfl : yy = y' := Option.some.inj (gy.symm.trans hy)
  obtain ⟨a0, x0, o, ha0, hel, hdc, htt⟩ := drawnAt_ok p s t (chiAt x) hdr
  have hx0 : x0 = Slice.ofE x := by
    have h1 : [Slice.ofE x] = [x0] := hel
    exact (List.cons.inj h1).1.symm
  obtain ⟨c1, c2, c3, c4, -, -, -, -, -, -, -, c12⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ hdc
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have hxx : xx.F = o.F := by
    rw [htt] at gx
    rw [Option.some.inj (gx.symm.trans ha')]
    exact hF'
  have hFa : a0.F = F :=
    Option.some.inj ((K9.get_fork s a0 ha0).symm.trans ((tlFork_iff s tl F).1 hs).2)
  have hsums : K9L.sums yy.F = K9L.sums xx.F := congrArg (·.1) gcore
  have hth : yy.F.theta = xx.F.theta := congrArg (·.2.1) gcore
  have hnc : yy.F.nClaim = xx.F.nClaim := congrArg (·.2.2.1) gcore
  have hpl : yy.F.planClaimsF = xx.F.planClaimsF := congrArg (·.2.2.2) gcore
  have hLS : yy.F.LS = xx.F.LS := congrArg (·.2.1) hsums
  have hns : yy.F.ns = xx.F.ns := congrArg (·.2.2.2) hsums
  have hbs := behind_set e yy G tl' gy gtl
  rw [← ht'] at hbs
  rw [gcls] at hadd
  refine ⟨tl', yy.F, G, F₁, F₂, fr, k8, bk, n₀, hbs,
    ⟨hadd, fun W => ?_, by rw [hnc, hxx]; exact c3, by rw [hLS, hns, hxx]; exact c12, geq,
      gth.trans hth.symm, gpl.trans hpl.symm, gfr1.trans gfr.symm,
      fun j cl hj => (gA j cl hj).1, fun j cl hj => (gB j cl hj).1,
      okW_of_sums hsums ((okW_iff _).2 (by rw [hxx]; exact okTrees_empty c1))⟩,
    ?_, by rw [hpl, hxx, c4, hFa], ?_, gnf, gnb, fun c cl hc => (gA c cl hc).2,
    fun c cl hc => (gB c cl hc).2⟩
  · rw [K9L.total_of_sums Reading.gl W xx.F yy.F hsums, hxx]
    exact K9L.total_of_empty Reading.gl W o.F c1
  · rw [hth, hxx, c2, hx0]
    exact Slice.toE_ofE x
  · refine (shape_of_frame _ _ gfr).trans ?_
    rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.core
#print axioms VerifiableInference.Desc.First.K8.Honest.termsSum_none
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_tie
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_sym
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_open
