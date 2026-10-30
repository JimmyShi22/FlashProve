-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LeftAtDrawn.lean: THE SMALLNESS TEST: `allHeld_at_link`
(Johnson/Desc/K8/Honest/LeftAtLink.lean: at a plain segment, behind a yes of the batching block,
three readings and seven tests of the verifier's test on what the adding has left) AT WHATEVER THE
ROUND HAS DRAWN: at every d : Fmt.Drawn at which the block says yes, not only at a field element
written in reduced words (`chiAt x`, Johnson/Desc/K8/Honest/FallCount.lean). Why: a sentence on
every yes of the block speaks of an element as three words, of which nothing says that they are
reduced. None of the library's goals.

  **`open_at_drawn`**   `open_at_link` (Johnson/Desc/K8/Honest/OpenAtLink.lean) at d: the same
                   ends, but that in the stead of "the batching element reads as x" stands: d has
                   one element x0, and the batching element behind the runs is E.ofTriple x0
  `filled_at_drawn`   `filled_at_link` (Johnson/Desc/K8/Honest/BitsFilled.lean) at d
  **`allHeld_at_drawn`**   `allHeld_at_link` at d: the state behind shows data tl' and a ledger G
                   with AllHeld tl' G
WRITTEN A FURTHER TIME: THE PROOF OF `open_at_drawn` IS THAT OF `open_at_link`, LINE FOR LINE, with
d in the stead of chiAt x, less the three lines that read x0 off chiAt x and the last step's reading
of the element: that proof spends chiAt x as a drawn value alone. `open_at_link` is not turned for
it; by reading, not typed: it would follow from this lemma at d := chiAt x, so of the twins it is
the one that can fall at a later turn. The two others are their namesakes' proofs with the one call
exchanged.
Limits. ALL LIMITS OF LeftAtLink.lean STAND: IMPLICATIONS; NO MEMBER; AllFront's seventeen,
RunsKeep, PreOk, PostOk, the list's tie and the sentence on the link's list ARE PAID BY NOBODY HERE;
not the whole of the verifier's test. At one drawn value d. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.LeftAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **What a yes of the batching block opens at a plain segment, at whatever is drawn.** -/
theorem open_at_drawn (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (d : Fmt.Drawn) (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (x0 : Fmt.Ext3) (t e e₁ e₂ : S) (cls fr k8 bk : List Claim) (tl' : HTailF2)
      (Y G F₁ F₂ : Fork),
      d.elems = [x0] ∧ drawnAt p s d = .ok t ∧ claimsInBy L.each L.hear L.order t = .ok (cls, e) ∧
      Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs ∧
      e.fork? = some Y ∧ tlForkP.get? t' = some (tl', G) ∧
      Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length ∧
      Y.theta = E.ofTriple x0 ∧ Y.planClaimsF = F.planClaimsF ∧
      shapeOf Y.trees = shapeOf F.trees := by
  obtain ⟨t, e, cls, y, G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p _ s t' d (hb _ _ hbt)
  obtain ⟨fr, k8, bk, e₁, e₂, F₁, F₂, tl₁, tl', funs₁, W⟩ :=
    walk_one L i pre post hord Hpost tEq t e cls hg
  obtain ⟨⟨xx, hx⟩, xt, xf⟩ := drawnAt_part p s t d hdr
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
  obtain ⟨a0, x0, o, ha0, hel, hdc, htt⟩ := drawnAt_ok p s t d hdr
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
  refine ⟨x0, t, e, e₁, e₂, cls, fr, k8, bk, tl', y'.F, G, x₁.F, F₂, hel, hdr, hg, W,
    K9.get_fork e y' hy, hbs,
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
  · rw [hth, hxx, d2]
  · refine (shape_of_frame _ _ sxy.frame).trans ?_
    rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]

/-- The same with the filling beside it. -/
theorem filled_at_drawn (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (d : Fmt.Drawn) (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (a0 : K9.Part) (t e e₁ e₂ : S) (cls fr k8 bk : List Claim) (tl' : HTailF2)
      (Y G F₁ F₂ : Fork), K9.atS.get? s = some a0 ∧ drawnAt p s d = .ok t ∧
      Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs ∧
      tlForkP.get? t' = some (tl', G) ∧ Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length ∧
      Y.trees = (t2FillL F a0.L.list).trees := by
  obtain ⟨-, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, -, hdr, -, W, hY, hget, A, -, -,
    -⟩ := open_at_drawn L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf d hbt
  obtain ⟨a0, xx, ha0, hxx, hfill⟩ := drawn_fill p s t d hdr F hF
  exact ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, W, hget, A,
    (walk_trees Hpre Hpost W xx hxx Y hY).trans hfill⟩

/-- **AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK, AT WHATEVER IS DRAWN.** -/
theorem allHeld_at_drawn (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (d : Fmt.Drawn) (hInv : ∀ t, drawnAt p s d = .ok t → Inv t)
    (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, Wk, hget, A, hYt⟩ :=
    filled_at_drawn L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf d hbt
  exact ⟨tl', G, hget, all_of_walk Wk A a0.L.list hYt (hT a0 ha0) g hg nbW Wn D R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.open_at_drawn
#print axioms VerifiableInference.Desc.First.K8.Honest.filled_at_drawn
#print axioms VerifiableInference.Desc.First.K8.Honest.allHeld_at_drawn
