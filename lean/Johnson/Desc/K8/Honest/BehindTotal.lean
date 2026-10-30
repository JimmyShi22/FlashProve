-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BehindTotal.lean: BEHIND A YES OF THE BATCHING BLOCK: THE SMALLNESS TEST's
DATA AND THE LEDGER THAT THE STATE HOLDS, AND WHAT THE LEDGER BEARS ON ANY ONE ENTRY OF ANY ARRAY,
AS TERMS IN THE CHALLENGE. Statements and proofs. No prover. Lemmas; none of the library's goals.

The first steps of `fall_root` (Johnson/Desc/K8/Honest/FallFew.lean), as a lemma of its own, at any
entry: for the counts of the tests on the ledger's weights.
  **`behind_total`**   batch: a decision each of whose yeses at s is a yes of the batching block
      K9.batch K9.atS p g with the same return; s holds the data tl and the ledger F; g meets
      `Gathers` at s; batch says yes at the challenge x and returns t'. THEN t' holds data tl' and a
      ledger G such that: tl' is what the list "K8.equations" has returned at tl, funs and a ledger
      F₁ whose batching element is x, with F's plan's number and arrays' shape; G has F's arrays'
      shape; the claims are at most the plan's number; tl has heard its lookup (g₀), and a's values
      at the numbers nf .. nf + 3 are the coefficients of the four claims K9L.four8 tl g₀; and at
      every entry (t, r, i) the cut of `total_cut` (Johnson/Desc/K8/Honest/WeightAt.lean) holds at x
  **`behind_plain`**   so at every virtual row on which the ties and reads lay nothing (`OffAt`):
      the ledger's value where the entry is 1 and all else 0, less its value where all is 0, is the
      sum of `plainTerms` at x
By: `batch_ok`, `drawnAt_ok`, `behind_set`, `drawn_trees`, `shape_fill`, `addList_count`
(FallDraw.lean) · K9L.take_four (Johnson/Desc/First/Batch/Law/K8Four.lean).
Limits: `Gathers` is a premise. The shape holds each array's number of columns and each virtual
row's first column, not the rows' numbers of weights: the draw lays these.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.WeightAt
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.First.Batch.Law.K8Four

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **Behind a yes of the batching block.** -/
theorem behind_total (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G F₁ F₂ : Fork) (k8 : List Claim) (n₀ : Nat) (g₀ : Forest.Heard),
      tlForkP.get? t' = some (tl', G) ∧ equations n₀ tl funs F₁ = .ok (tl', F₂, k8) ∧
      tl.heard = some g₀ ∧ Reading.gl.val F₁.theta = x ∧ F₁.planClaimsF = F.planClaimsF ∧
      shapeOf F₁.trees = shapeOf F.trees ∧ shapeOf G.trees = shapeOf F.trees ∧
      nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
      (∀ c cl, (K9L.four8 tl g₀)[c]? = some cl → ∀ t r i, a (nf + c) t r i = coefOn cl t r i) ∧
      ∀ t r i, ∃ tl1 : HTailF2, Powered tl1 F₁.theta ∧
        (∀ mu, mu < tl1.NM → tl1.gamV.getD mu #[] = gamAt tl1 mu) ∧
        tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
        G.total Reading.gl (oneAt t r i) - G.total Reading.gl allZero =
          K9L.termsSum (fromOn (fun j => a j t r i) (nf + 4) 0) x +
          K9L.termsSum (fromOn (fun j => a j t r i) nb
            (nf + (4 + (tl.NM + (readsList tl funs).length)))) x +
          ((((List.range tl1.NM).map (tieTerm Reading.gl (oneAt t r i) tl1 F₁)).sum +
              sumFrom (readTerm Reading.gl (oneAt t r i) tl1 F₁) 0 (readsList tl1 funs)) -
            (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
              sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs))) := by
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
  have hsz : yy.F.LS.size = yy.F.ns := by rw [hLS, hns, hxx]; exact c12
  have hn0 : yy.F.nClaim = 0 := by rw [hnc, hxx]; exact c3
  have hplF : yy.F.planClaimsF = F.planClaimsF := by rw [hpl, hxx, c4, hFa]
  have hz : ∀ W : World Cb.Gl.E, yy.F.total Reading.gl W = 0 := fun W => by
    rw [K9L.total_of_sums Reading.gl W xx.F yy.F hsums, hxx]
    exact K9L.total_of_empty Reading.gl W o.F c1
  have hchi : Reading.gl.val yy.F.theta = x := by
    rw [hth, hxx, c2, hx0]
    exact Slice.toE_ofE x
  have hall : addAll yy.F (fr ++ k8 ++ bk) = some G := by
    rw [← gcls]
    exact K9L.addList_older cls yy.F G hadd
  have sh0 : shapeOf xx.F.trees = shapeOf F.trees := by
    rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]
  have sh1 : shapeOf F₁.trees = shapeOf F.trees := (shape_of_frame _ _ gfr1).trans sh0
  have shG : shapeOf G.trees = shapeOf F.trees :=
    (shape_of_frame _ _ (K9L.addAll_total Reading.gl allZero _ yy.F G hsz hall).2.2.2).trans
      ((shape_of_frame _ _ gfr).trans sh0)
  obtain ⟨-, -, -, -, -, hk8, -⟩ := k8_cut geq
  obtain ⟨g₀, -, hg₀, h4, -, -⟩ := K9L.take_four geq
  have hbs := behind_set e yy G tl' gy gtl
  rw [← ht'] at hbs
  refine ⟨tl', G, F₁, F₂, k8, n₀, g₀, hbs, geq, hg₀, by rw [gth, ← hth]; exact hchi,
    by rw [gpl, ← hpl]; exact hplF, sh1, shG, ?_, ?_, ?_⟩
  · have h1 := addList_count cls yy.F G hsz hadd (by omega)
    rw [gcls, List.length_append, List.length_append, gnf, gnb, hk8, hn0, hplF] at h1
    omega
  · intro c cl hc t r i
    have h5 : (fr ++ k8.take 4)[nf + c]? = some cl := by
      rw [List.getElem?_append_right (by omega), gnf, Nat.add_sub_cancel_left, h4]
      exact hc
    exact ((gA _ cl h5).2 t r i).symm
  · intro t r i
    obtain ⟨tl1, hP, hgam, etl, hcut⟩ := total_cut (fun j => a j t r i) tl tl' funs yy.F G F₁ F₂ fr
      k8 bk n₀ t r i nf nb hall hz hn0 hsz geq (gth.trans hth.symm) (gpl.trans hpl.symm)
      (gfr1.trans gfr.symm) gnf gnb (fun j cl hj => ⟨(gA j cl hj).1, (gA j cl hj).2 t r i⟩)
      (fun j cl hj => ⟨(gB j cl hj).1, (gB j cl hj).2 t r i⟩)
    rw [hchi] at hcut
    exact ⟨tl1, hP, hgam, etl, hcut⟩

/-- **At a row that is none of the ties' and reads'.** -/
theorem behind_plain (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork) (g₀ : Forest.Heard),
      tlForkP.get? t' = some (tl', G) ∧
      (∃ (n₀ : Nat) (F₁ F₂ : Fork) (k8 : List Claim),
        equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) ∧ tl.heard = some g₀ ∧
      shapeOf G.trees = shapeOf F.trees ∧
      nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
      (∀ c cl, (K9L.four8 tl g₀)[c]? = some cl → ∀ t r i, a (nf + c) t r i = coefOn cl t r i) ∧
      ∀ t r i, OffAt tl t r → G.total Reading.gl (oneAt t r i) - G.total Reading.gl allZero =
        K9L.termsSum (plainTerms (fun j => a j t r i) nf nb
          (tl.NM + (readsList tl funs).length)) x := by
  obtain ⟨tl', G, F₁, F₂, k8, n₀, g₀, h1, geq, h3, -, -, -, h7, h8, h9, h10⟩ :=
    behind_total p g batch s t' tl F funs nf nb a hb hs hG x hbt
  refine ⟨tl', G, g₀, h1, ⟨n₀, F₁, F₂, k8, geq⟩, h3, h7, h8, h9, fun t r i hoff => ?_⟩
  obtain ⟨tl1, -, -, etl, hcut⟩ := h10 t r i
  have hcond : OffAt tl1 t r :=
    (same1 (fun u : HTailF2 => OffAt u t r) geq etl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr hoff
  rw [hcut, brackets_off tl1 F₁ funs t r i hcond, add_zero]
  unfold plainTerms
  rw [termsSum_append]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.behind_total
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_plain
