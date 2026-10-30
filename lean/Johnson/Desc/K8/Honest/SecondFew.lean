-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SecondFew.lean: THE SMALLNESS TEST: HOW MANY FIELD ELEMENTS ARE CHALLENGES OF
THE BATCHING BEHIND WHICH THE REST OF THE VERIFIER's TWO TESTS ON WEIGHTS BY A SECOND COMPUTATION
FAILS ("NOT 0", "ALL DIFFERENT": `SecondRest`, Johnson/Desc/K8/Honest/SecondParts.lean): AT MOST
`secondN`, UNDER THREE NAMED PREMISES: `SecondLaid` AND `PieceLive` IN FRONT OF THE BATCHING, AND
`SecondEqs` BEHIND IT AT EVERY CHALLENGE. Definitions and lemmas; none of the library's goals. No
prover stands in them; nothing on completeness, soundness or hiding.

  `rows_of_shape`, `hasRow_of_shape`   a virtual row that is there in one ledger is there in every
      ledger of its shape (`shapeOf`, Johnson/Desc/K8/Honest/FallDraw.lean)
  **`behind_powered`**   behind a yes of the batching block at the challenge x: the data hold the
      powers of the batching element of THE LEDGER BEHIND, which reads as x; that ledger has the
      shape of the one in front; eight planned fields of the data are those in front. ITS FIRST
      STEPS ARE THOSE OF `behind_total` (Johnson/Desc/K8/Honest/BehindTotal.lean), WRITTEN A SECOND
      TIME: that lemma speaks of the ledger at which the list "K8.equations" was made, not of the
      one behind the adding
  `wants_same`, `pieceLive_same`   what the wanted pieces and `PieceLive` read of the data
  `secondN tl`   1 for the element 0, and for each matrix what `differ_few` counts
      (Johnson/Desc/K8/Honest/DifferFew.lean)
  `SecondLaid tl F`   on the frame in front: every matrix has a shape; its array of symbols has a
      virtual row 0; the matrices' arrays differ
  **`second_few`**, **`second_at_link`**   the count; at a plain segment (`PlainLink`,
      Johnson/Desc/K8/Honest/CountFrom.lean), as `count_at_link` there
By: `second_speaks` (Johnson/Desc/K8/Honest/SecondNz.lean) · `powered_of_yes` (PoweredOfYes.lean) ·
K9L.addAll_total: the adding leaves the batching element (Johnson/Desc/First/Batch/Law/Ledger.lean)
· eq_same (Johnson/Desc/First/TailClaims/EquationsCover.lean) · Prob.cnt_or_le, cnt_le_one.
Limits. THE THREE PREMISES ARE SHOWN OF NO STATE. `SecondEqs` is asked behind the batching AT EVERY
FIELD ELEMENT at which it says yes. `PieceLive` is asked of what the lookup has heard in front of
the batching; where nothing has been heard the premise is empty, and so is the event. `Gathers` is a
premise of `second_few`. The element 0 is counted more than once: an upper bound.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.SecondNz
import Johnson.Desc.K8.Honest.DifferFew
import Johnson.Desc.K8.Honest.PoweredOfYes
import Johnson.Desc.K8.Honest.CountFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- An array's number of virtual rows, off the shape. -/
theorem rows_of_shape (A : Array HTree) (t : Nat) :
    (A.getD t {}).rows.size = (((shapeOf A).getD t (0, #[])).2).size := by
  simp only [shapeOf, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> simp

/-- A virtual row that is there in one ledger is there in every ledger of its shape. -/
theorem hasRow_of_shape {F G : Fork} (h : shapeOf G.trees = shapeOf F.trees) {t e : Nat}
    (hr : HasRow F t e) : HasRow G t e := by
  have hs : G.trees.size = F.trees.size := by
    have k := congrArg Array.size h
    simpa [shapeOf] using k
  exact ⟨hs ▸ hr.1, by rw [rows_of_shape, h, ← rows_of_shape]; exact hr.2⟩

/-- **Behind a yes of the batching block at the challenge x**: the data and the ledger that the
state holds: the data hold the powers of the ledger's batching element, which reads as x; the
ledger has the shape of the one in front; the planned fields that the two tests read are those in
front. -/
theorem behind_powered (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ Powered tl' G.theta ∧
      Reading.gl.val G.theta = x ∧ shapeOf G.trees = shapeOf F.trees ∧
      tl'.NM = tl.NM ∧ tl'.shp = tl.shp ∧ tl'.gtTree = tl.gtTree ∧ tl'.tau = tl.tau ∧
      tl'.heard = tl.heard ∧ tl'.mz = tl.mz ∧ tl'.z1 = tl.z1 ∧ tl'.z2 = tl.z2 := by
  obtain ⟨t, e, cls, y', G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p g s t' (chiAt x) (hb _ _ hbt)
  obtain ⟨xx, yy, tl', fr, k8, bk, n₀, F₁, F₂, gx, gy, gcore, gfr, gtl, gcls, -,
    -, geq, gth, -, -, -, -⟩ := hG.each (chiAt x) t e cls hdr hg
  obtain rfl : yy = y' := Option.some.inj (gy.symm.trans hy)
  obtain ⟨a0, x0, o, ha0, hel, hdc, htt⟩ := drawnAt_ok p s t (chiAt x) hdr
  have hx0 : x0 = Slice.ofE x := by
    have h1 : [Slice.ofE x] = [x0] := hel
    exact (List.cons.inj h1).1.symm
  obtain ⟨-, c2, -, -, -, -, -, -, -, -, -, c12⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ hdc
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
  have hLS : yy.F.LS = xx.F.LS := congrArg (·.2.1) hsums
  have hns : yy.F.ns = xx.F.ns := congrArg (·.2.2.2) hsums
  have hsz : yy.F.LS.size = yy.F.ns := by rw [hLS, hns, hxx]; exact c12
  have hchi : Reading.gl.val yy.F.theta = x := by
    rw [hth, hxx, c2, hx0]
    exact Slice.toE_ofE x
  have hall : addAll yy.F cls = some G := K9L.addList_older cls yy.F G hadd
  obtain ⟨-, eG, -, frG⟩ := K9L.addAll_total Reading.gl allZero _ yy.F G hsz hall
  have thG : G.theta = yy.F.theta := by rw [eG]
  have sh0 : shapeOf xx.F.trees = shapeOf F.trees := by
    rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]
  have hbs := behind_set e yy G tl' gy gtl
  rw [← ht'] at hbs
  have hP := powered_of_yes geq
  rw [gth, ← hth, ← thG] at hP
  exact ⟨tl', G, hbs, hP, by rw [thG]; exact hchi,
    (shape_of_frame _ _ frG).trans ((shape_of_frame _ _ gfr).trans sh0),
    eq_same (·.NM) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    eq_same (·.shp) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    eq_same (·.gtTree) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (·.tau) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    eq_same (·.heard) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (·.mz) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    eq_same (·.z1) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    eq_same (·.z2) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩

/-- The wanted pieces are read off two planned numbers. -/
theorem wants_same {tl tl' : HTailF2} (h1 : tl'.tau = tl.tau) (h2 : tl'.mz = tl.mz) :
    tl'.wants = tl.wants := by
  unfold HTailF2.wants
  rw [h1, h2]

/-- `PieceLive` reads the data through the two calls alone. -/
theorem pieceLive_same {tl tl' : HTailF2} (h1 : tl'.z1 = tl.z1) (h2 : tl'.z2 = tl.z2)
    {g : Forest.Heard} {W : List Want} (h : PieceLive tl g W) : PieceLive tl' g W := by
  have e : tl'.zOf = tl.zOf := by
    funext q
    unfold HTailF2.zOf
    rw [h1, h2]
  unfold PieceLive at h ⊢
  rw [e]
  exact h

/-- **The number**: 1 for the element 0, and for each matrix what `differ_few` counts. -/
def secondN (tl : HTailF2) : Nat :=
  1 + ∑ mu ∈ Finset.range tl.NM,
    (1 + ∑ k ∈ Finset.range (tl.shp.getD mu {}).mS, tl.stepF * k)

/-- **On the frame in front**: every matrix has a shape; its array of symbols has a virtual row 0;
the matrices' arrays differ. -/
def SecondLaid (tl : HTailF2) (F : Fork) : Prop :=
  tl.NM ≤ tl.shp.size ∧ (∀ mu < tl.NM, HasRow F (tl.gtTree.getD mu 0) 0) ∧
    ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b

/-- **THE COUNT.** no: a test on the state behind whose yes gives the three values and that not
both halves hold. -/
theorem second_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (no : S → Bool)
    (hno : ∀ t' tl' G, tlForkP.get? t' = some (tl', G) → no t' = true →
      ∃ g₀ jo nbW W, tl'.heard = some g₀ ∧ tl'.joinObj9 = some jo ∧
        tl'.wants = some (nbW, W) ∧ ¬ (SecondEqs tl' G ∧ SecondRest tl' G))
    (hLd : SecondLaid tl F)
    (hLv : ∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W)
    (hEq : ∀ x t' tl' G, batch s [⟨[], chiAt x⟩] = .ok t' → tlForkP.get? t' = some (tl', G) →
      SecondEqs tl' G) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ secondN tl := by
  have hN : 0 < tl.stepF := Nat.two_pow_pos _
  refine (Prob.cnt_mono fun x hx => ?_).trans ((Prob.cnt_or_le (fun x : Cb.Gl.E => x = 0)
    (fun x : Cb.Gl.E => ∃ mu, mu < tl.NM ∧ ∃ i j, i < j ∧ j < (tl.shp.getD mu {}).mS ∧
      (x ^ tl.stepF) ^ i = (x ^ tl.stepF) ^ j)).trans (Nat.add_le_add
      (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm)
      (differ_few Cb.Gl.E tl.NM tl.stepF (fun mu => (tl.shp.getD mu {}).mS) hN
        (fun x mu => ∃ i j, i < j ∧ j < (tl.shp.getD mu {}).mS ∧
          (x ^ tl.stepF) ^ i = (x ^ tl.stepF) ^ j) fun _ _ _ h => h)))
  unfold askBehind at hx
  simp only [List.map_cons, List.map_nil] at hx
  cases hbt : batch s [⟨[], chiAt x⟩] with
  | error e =>
    rw [hbt] at hx
    exact absurd hx (by simp)
  | ok t' =>
    rw [hbt] at hx
    obtain ⟨tl', G, h1, hP, hv, hsh, e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
      behind_powered p g batch s t' tl F funs nf nb a hb hs hG x hbt
    obtain ⟨g₀, jo, nbW, W, k1, k2, k3, k4⟩ := hno t' tl' G h1 hx
    obtain ⟨l1, l2, l3⟩ := hLd
    have est : tl'.stepF = tl.stepF := by
      unfold HTailF2.stepF
      rw [e4]
    have hE := hEq x t' tl' G hbt h1
    have key := second_speaks tl' G k1 k2 k3 hE
      (pieceLive_same e7 e8 (hLv g₀ nbW W (e5 ▸ k1) ((wants_same e4 e6) ▸ k3))) hP
      (by rw [e1, e2]; exact l1)
      (fun mu hmu => hasRow_of_shape hsh (by rw [e3]; exact l2 mu (e1 ▸ hmu)))
      (by rw [e1, e3]; exact l3) fun hR => k4 ⟨hE, hR⟩
    rw [hv, e1, e2, est] at key
    exact key

/-- **The count at a plain segment.** -/
theorem second_at_link (L : Link S Claim) (hL : PlainLink L) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (n : Nat) (no : S → Bool)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hno : ∀ t' tl' G, tlForkP.get? t' = some (tl', G) → no t' = true →
      ∃ g₀ jo nbW W, tl'.heard = some g₀ ∧ tl'.joinObj9 = some jo ∧
        tl'.wants = some (nbW, W) ∧ ¬ (SecondEqs tl' G ∧ SecondRest tl' G))
    (hOw : ∀ tl F, s.tl? = some tl → s.fork? = some F → SecondLaid tl F ∧
      (∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W) ∧
      secondN tl ≤ n)
    (hEq : ∀ x t' tl' G, batch s [⟨[], chiAt x⟩] = .ok t' → tlForkP.get? t' = some (tl', G) →
      SecondEqs tl' G) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ n := by
  obtain ⟨i, pre, post, hord, Hpre, Hpost, tEq⟩ := hL
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch no s [chiAt x] = true
  · obtain ⟨x, hx⟩ := hne
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      obtain ⟨t, e, cls, y, G, hdr, hg, -, -, -⟩ := batch_ok p _ s t' (chiAt x) (hb _ _ hbt)
      obtain ⟨a0, -, -, ha0, -, -, -⟩ := drawnAt_ok p s t (chiAt x) hdr
      have hF : s.fork? = some a0.F := K9.get_fork s a0 ha0
      obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1
        (funs_of_yes L p i pre post hord Hpre Hpost tEq s _ t e cls hdr hg)
      obtain ⟨tl, ht⟩ : ∃ tl, s.tl? = some tl := by
        cases h : s.tl? with
        | some tl => exact ⟨tl, rfl⟩
        | none =>
          exfalso
          simp [K9.atS, h] at ha0
      obtain ⟨nf, nb, a, hGa⟩ := gathers_of_plain L p i pre post hord Hpre Hpost tEq s tl funs ht hf
      obtain ⟨h1, h2, h3⟩ := hOw tl a0.F ht hF
      exact (second_few p _ batch s tl a0.F funs nf nb a hb ((tlFork_iff s tl a0.F).2 ⟨ht, hF⟩)
        hGa no hno h1 h2 hEq).trans h3
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.rows_of_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.hasRow_of_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_powered
#print axioms VerifiableInference.Desc.First.K8.Honest.wants_same
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceLive_same
#print axioms VerifiableInference.Desc.First.K8.Honest.second_few
#print axioms VerifiableInference.Desc.First.K8.Honest.second_at_link
