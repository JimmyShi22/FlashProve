-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OpenAtLink.lean: THE SMALLNESS TEST: FROM A PLAIN SEGMENT's WALK STRAIGHT TO
`Added8` (Johnson/Desc/K8/Honest/Added8.lean), AT THE CUT OF THE LIST OF CLAIMS BY THE RUNS
THEMSELVES, WITH THE NUMBER THAT "K8.equations" IS HANDED: THE NUMBER OF THE CLAIMS IN FRONT. A
lemma; none of the library's goals. No prover stands in it; nothing on completeness, soundness or
hiding.

  **`open_at_link`**   at a segment whose order is pre ++ [(i, "K8.equations")] ++ post, under
      `PreOk`, `PostOk` and the list's tie to its run: behind a yes of the batching block at the
      challenge x: the draw's yes; the runs' yes; its cut (`Walk`,
      Johnson/Desc/K8/Honest/GathersPlain.lean); the ledger behind the runs; the state behind holds
      data and a ledger that stand in `Added8` at that cut; the batching element reads as x; the
      plan's number and the shape are those of the ledger in front
ITS PROOF REPEATS THE STEPS OF TWO EARLIER PROOFS: the middle of `gathers_of_plain`
(GathersPlain.lean) and the end of `behind_open` (Added8.lean). The statements of both hide
behind an "exists" what is wanted here: the cut, and the number handed to the list.
`behind_open` does not follow from this lemma: it stands under `Gathers` at any function of
claims.
By: `batch_ok`, `drawnAt_ok`, `behind_set`, `shape_of_frame` (Johnson/Desc/K8/Honest/FallDraw.lean)
· `walk_one`, `pre_one`, `post_one`, `drawnAt_part` (GathersPlain.lean) · `four8_plain`
(FallLayersLaw.lean) · `okW_of_sums`, `okW_iff`, `okTrees_empty` (OkWeights.lean) · K9L.take_four
(Johnson/Desc/First/Batch/Law/K8Four.lean) · K9L.drawnClean_ok (AtBlock.lean) · K9L.total_of_sums,
total_of_empty (Ledger.lean).
Limits. Nothing on any weight. Which run stands under which is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.Added8
import Johnson.Desc.K8.Honest.GathersPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **FROM A PLAIN SEGMENT's WALK STRAIGHT TO `Added8`**: behind a yes of the batching block at the
challenge x: the draw's yes, the runs' yes, its cut by the runs (`Walk`), and `Added8` AT THAT VERY
CUT, with the number that "K8.equations" is handed: the number of the claims in front. -/
theorem open_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (t e e₁ e₂ : S) (cls fr k8 bk : List Claim) (tl' : HTailF2) (Y G F₁ F₂ : Fork),
      drawnAt p s (chiAt x) = .ok t ∧ claimsInBy L.each L.hear L.order t = .ok (cls, e) ∧
      Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs ∧
      e.fork? = some Y ∧ tlForkP.get? t' = some (tl', G) ∧
      Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length ∧
      Reading.gl.val Y.theta = x ∧ Y.planClaimsF = F.planClaimsF ∧
      shapeOf Y.trees = shapeOf F.trees := by
  obtain ⟨t, e, cls, y, G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p _ s t' (chiAt x) (hb _ _ hbt)
  obtain ⟨fr, k8, bk, e₁, e₂, F₁, F₂, tl₁, tl', funs₁, W⟩ :=
    walk_one L i pre post hord Hpost tEq t e cls hg
  obtain ⟨⟨xx, hx⟩, xt, xf⟩ := drawnAt_part p s t (chiAt x) hdr
  obtain ⟨c, c1, c2, c3, c4, c5⟩ := pre_one L pre Hpre _ _ W.a1
  obtain ⟨x₁, hx₁, s₁⟩ := c5 xx hx
  obtain rfl : x₁.F = F₁ := Option.some.inj ((K9.get_fork _ _ hx₁).symm.trans W.a2)
  obtain rfl : tl = tl₁ := by
    have h := W.a3
    rw [c3, xt, ht] at h
    exact Option.some.inj h
  obtain rfl : funs = funs₁ := by
    have h := W.a4
    rw [c4, xf, hf] at h
    exact Option.some.inj h
  obtain ⟨x₂, hx₂, hF₂, -, -, htl₂, -, -⟩ := K9L.get_put e₁ x₁ hx₁ tl' F₂
  obtain ⟨b, b1, b2, b3, b5⟩ := post_one L post Hpost _ _ W.a7
  rw [W.a6] at b3 b5
  obtain ⟨y', hy', s₃⟩ := b5 x₂ hx₂
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  have s₂ : SameSums x₁.F x₂.F := by
    rw [hF₂]
    exact SameSums.ofSide (eq_side W.a5)
  have sxy : SameSums xx.F y'.F := (s₁.trans s₂).trans s₃
  have hplainF : ∀ cl ∈ fr, cl.eqFirst = none := by
    have e0 : fr = c := by simpa using c1
    rw [e0]
    exact c2
  have hplainB : ∀ cl ∈ bk, cl.eqFirst = none := by
    have e0 : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
    rw [e0]
    exact b2
  obtain ⟨g8, -, -, h48, -, -⟩ := K9L.take_four W.a5
  obtain ⟨a0, x0, o, ha0, hel, hdc, htt⟩ := drawnAt_ok p s t (chiAt x) hdr
  have hx0 : x0 = Slice.ofE x := by
    have h1 : [Slice.ofE x] = [x0] := hel
    exact (List.cons.inj h1).1.symm
  obtain ⟨d1, d2, d3, d4, -, -, -, -, -, -, -, d12⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ hdc
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have hxx : xx.F = o.F := by
    rw [htt] at hx
    rw [Option.some.inj (hx.symm.trans ha')]
    exact hF'
  have hFa : a0.F = F := Option.some.inj ((K9.get_fork s a0 ha0).symm.trans hF)
  have gcore := sxy.core
  have hsums : K9L.sums y'.F = K9L.sums xx.F := congrArg (·.1) gcore
  have hth : y'.F.theta = xx.F.theta := congrArg (·.2.1) gcore
  have hnc : y'.F.nClaim = xx.F.nClaim := congrArg (·.2.2.1) gcore
  have hpl : y'.F.planClaimsF = xx.F.planClaimsF := congrArg (·.2.2.2) gcore
  have hLS : y'.F.LS = xx.F.LS := congrArg (·.2.1) hsums
  have hns : y'.F.ns = xx.F.ns := congrArg (·.2.2.2) hsums
  have hn1 : x₁.F.nClaim = 0 := by
    rw [s₁.nClaim, hxx]
    exact d3
  have hbs := behind_set e y' G tl' hy (b3.trans htl₂)
  rw [← ht'] at hbs
  have a5 := W.a5
  rw [hn1, Nat.zero_add] at a5
  rw [W.a8] at hadd
  refine ⟨t, e, e₁, e₂, cls, fr, k8, bk, tl', y'.F, G, x₁.F, F₂, hdr, hg, W, K9.get_fork e y' hy,
    hbs,
    ⟨hadd, fun Wd => ?_, by rw [hnc, hxx]; exact d3, by rw [hLS, hns, hxx]; exact d12, a5,
      s₁.theta.trans hth.symm, s₁.plan.trans hpl.symm, s₁.frame.trans sxy.frame.symm,
      fun j cl hj => ?_, fun j cl hj => hplainB cl (List.mem_of_getElem? hj),
      okW_of_sums hsums ((okW_iff _).2 (by rw [hxx]; exact okTrees_empty d1))⟩,
    ?_, by rw [hpl, hxx, d4, hFa], ?_⟩
  · rw [K9L.total_of_sums Reading.gl Wd xx.F y'.F hsums, hxx]
    exact K9L.total_of_empty Reading.gl Wd o.F d1
  · rcases List.mem_append.1 (List.mem_of_getElem? hj) with h1 | h1
    · exact hplainF cl h1
    · rw [h48] at h1
      exact four8_plain _ _ cl h1
  · rw [hth, hxx, d2, hx0]
    exact Slice.toE_ofE x
  · refine (shape_of_frame _ _ sxy.frame).trans ?_
    rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.open_at_link
