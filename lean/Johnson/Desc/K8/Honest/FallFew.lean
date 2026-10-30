-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallFew.lean: THE COUNT OF Johnson/Desc/K8/Honest/FallCount.lean, PROVED:
`fall_few : FallFew`. Statements and proofs. No prover.

  `rowStart`    the first place of the virtual row in which a place lies
  **`fall_root`**   at a challenge at which the batching block says yes and an entry of the vector of
      reads has the weight 0: the claims are at most the plan's number; every place of the vector is
      named by a read and a column, and that column of the drawn matrix has an entry other than 0;
      and at some place the terms of that place's weight (`unitTerms`) add up to 0 at the challenge
      (the place of the weight 0 itself, if its virtual row's weights begin at column 0; else the
      row's first place, on which the ledger then lays nothing)
  **`fall_few`**    so at most nU[2] * d challenges are such: each place's terms are a polynomial that
      is not 0, of a degree of at most d (the library's count of roots: `K9L.count_terms`)
Limits: those of the statement: `Gathers` is a premise, shown of no function of claims.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallTerms
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.K8.Honest.FallLive
import Johnson.Desc.K8.Honest.FallLaw
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The first place of the virtual row in which a place lies: it lies in that row, at column 0. -/
theorem rowStart (K pos : Nat) :
    pos / K * K ≤ pos ∧ pos / K * K / K = pos / K ∧ pos / K * K % K = 0 := by
  refine ⟨Nat.div_mul_le_self pos K, ?_, Nat.mul_mod_left _ _⟩
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h
    simp
  · exact Nat.mul_div_cancel _ h

/-- **A challenge at which an entry has the weight 0 is a root of that entry's terms.** -/
theorem fall_root (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (nU : Array Nat) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (tU nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hU : unitsLaid nU tl tU = true)
    (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hx : askBehind batch (zeroUnitAt nU) s [chiAt x] = true) :
    nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
    (∀ pos, pos < nU.getD 2 0 → ∃ (q : Nat) (y : HFun × Nat) (c : Nat),
      (readsList tl funs)[q]? = some y ∧ columnLive tl y.1.mat c = true ∧
      c < (tl.mats.getD y.1.mat {}).k ∧ posOf tl y.1 y.2 c = pos) ∧
    ∃ pos, pos < nU.getD 2 0 ∧ ∀ (q : Nat) (y : HFun × Nat) (c : Nat),
      (readsList tl funs)[q]? = some y →
      c < (tl.mats.getD y.1.mat {}).k → posOf tl y.1 y.2 c = pos →
      K9L.termsSum (unitTerms (fun j => a j tU) tl F.planClaimsF nf nb (readsList tl funs).length
        (F.trees.getD tU {}).K pos q y.1.mat c) x = 0 := by
  simp only [unitsLaid, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Option.isNone_iff_eq_none, List.all_eq_true, List.mem_range] at hU
  obtain ⟨⟨⟨⟨⟨⟨⟨u0, u1⟩, u2⟩, u3⟩, u4⟩, u5⟩, u6⟩, u7⟩ := hU
  unfold askBehind at hx
  simp only [List.map_cons, List.map_nil] at hx
  cases hbt : batch s [⟨[], chiAt x⟩] with
  | error e =>
    rw [hbt] at hx
    exact absurd hx (by simp)
  | ok t' =>
    rw [hbt] at hx
    change zeroUnitAt nU t' = true at hx
    obtain ⟨t, e, cls, y', G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p g s t' (chiAt x) (hb _ _ hbt)
    obtain ⟨xx, yy, tl', fr, k8, bk, n₀, F₁, F₂, gx, gy, gcore, gfr, gtl, gcls, gnf,
      gnb, geq, gth, gpl, gfr1, gA, gB⟩ := hG.each (chiAt x) t e cls hdr hg
    have gix : tl'.ix = tl.ix :=
      eq_same (fun t : HTailF2 => t.ix) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ => rfl)
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
    -- what the runs have left of the ledger
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
    -- the arrays' shape, from the state in front to the ledger behind the adding
    have sh0 : shapeOf xx.F.trees = shapeOf F.trees := by
      rw [hxx, drawn_trees _ _ _ _ _ _ _ hdc, shape_fill, hFa]
    have sh1 : shapeOf F₁.trees = shapeOf F.trees := (shape_of_frame _ _ gfr1).trans sh0
    have shG : shapeOf G.trees = shapeOf F.trees :=
      (shape_of_frame _ _ (K9L.addAll_total Reading.gl allZero _ yy.F G hsz hall).2.2.2).trans
        ((shape_of_frame _ _ gfr).trans sh0)
    have hK1 : colsU F₁ tU = (F.trees.getD tU {}).K := by
      rw [colsU_eq, K_of_shape, sh1, ← K_of_shape]
    have hKG : (G.trees.getD tU {}).K = (F.trees.getD tU {}).K := by
      rw [K_of_shape, shG, ← K_of_shape]
    obtain ⟨-, -, -, -, -, hk8, -⟩ := k8_cut geq
    refine ⟨?_, ?_, ?_⟩
    · have h1 := addList_count cls yy.F G hsz hadd (by omega)
      rw [gcls, List.length_append, List.length_append, gnf, gnb, hk8, hn0, hplF] at h1
      omega
    · have hcov := (eq_same (fun t : HTailF2 => t.tabFirst.getD 1 0 = 0 →
          t.tabLen.getD 1 0 = t.nUF.getD 2 0 → ∀ pos : Nat, pos < t.nUF.getD 2 0 →
          ∃ z ∈ readsList t funs, z.1.tree = 2 ∧ ∃ d, d < (t.mats.getD z.1.mat {}).k ∧
            posOf t z.1 z.2 d = pos) geq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ _ _ => rfl)).mp (eq_coverU3 n₀ tl tl' funs F₁ F₂ k8 geq)
      intro pos hpos
      obtain ⟨z, hz1, hz2, c, hc, hp⟩ := hcov u3 (by rw [u4, u5]) pos (by rw [u5]; exact hpos)
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hz1
      exact ⟨q, z, c, hq, eq_columnLive geq z hz1 c hc, hc, hp⟩
    · have hbs := behind_set e yy G tl' gy gtl
      rw [← ht'] at hbs
      unfold zeroUnitAt at hx
      rw [hbs] at hx
      change zeroUnit tl' nU G = true at hx
      obtain ⟨n, hn, t0, ht0, pos, hpos, hzero⟩ := (zeroUnit_iff tl' nU G).1 hx
      rw [gix] at ht0
      have hn2 : n = 2 := by
        rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
        · rw [u0] at ht0
          exact absurd ht0 (by simp)
        · rw [u1] at ht0
          exact absurd ht0 (by simp)
        · rfl
      subst hn2
      obtain rfl : tU = t0 := Option.some.inj (u2.symm.trans ht0)
      have wt : ∀ (pos q c : Nat) (y : HFun × Nat), (readsList tl funs)[q]? = some y →
          c < (tl.mats.getD y.1.mat {}).k → posOf tl y.1 y.2 c = pos →
          G.total Reading.gl (oneAt tU (pos / (F.trees.getD tU {}).K) (pos % (F.trees.getD tU {}).K)) -
              G.total Reading.gl allZero =
            K9L.termsSum (unitTerms (fun j => a j tU) tl F.planClaimsF nf nb
              (readsList tl funs).length (F.trees.getD tU {}).K pos q y.1.mat c) x := by
        intro pos q c y hq hc hp
        have w := weight_terms (fun j => a j tU) tl tl' funs yy.F G F₁ F₂ fr k8 bk n₀ tU nf nb pos q
          c y hall hz hn0 hsz geq (gth.trans hth.symm) (gpl.trans hpl.symm) (gfr1.trans gfr.symm) gnf
          gnb (fun j cl hj => ⟨(gA j cl hj).1, fun r i => (gA j cl hj).2 tU r i⟩)
          (fun j cl hj => ⟨(gB j cl hj).1, fun r i => (gB j cl hj).2 tU r i⟩) u6 u7 u0 u2 hq hc hp
        rw [hK1, hplF, hchi] at w
        exact w
      by_cases hL : ((G.trees.getD tU {}).rows.getD (pos / (F.trees.getD tU {}).K) {}).L0 = 0
      · -- the row's weights begin at column 0: the weight that the test reads is the entry's own
        refine ⟨pos, hpos, fun q y c hq hc hp => ?_⟩
        rw [← wt pos q c y hq hc hp, total_oneAt Reading.gl G tU _ _ hL]
        have hw : unitWeightAt G tU pos = zeroE := isZeroE_eq hzero
        unfold unitWeightAt at hw
        rw [hKG] at hw
        rw [hw]
        exact Reading.gl.zero
      · -- they begin behind it: then the ledger lays nothing on the row's first entry
        obtain ⟨r1, r2, r3⟩ := rowStart (F.trees.getD tU {}).K pos
        refine ⟨pos / (F.trees.getD tU {}).K * (F.trees.getD tU {}).K, by omega,
          fun q y c hq hc hp => ?_⟩
        rw [← wt _ q c y hq hc hp, r2, r3]
        exact total_below Reading.gl G tU _ 0 (Nat.pos_of_ne_zero hL)

/-- **The count.** -/
theorem fall_few : FallFew := by
  intro p g batch nU s tl F funs tU nf nb d a hb hs hU hG hd
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch (zeroUnitAt nU) s [chiAt x] = true
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨hcnt, hcov, -⟩ := fall_root p g batch nU s tl F funs tU nf nb a hb hs hU hG x₀ hx₀
    calc Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true)
        ≤ Prob.cnt (fun x : Cb.Gl.E => ∃ pos ∈ Finset.range (nU.getD 2 0),
            ∀ (q : Nat) (y : HFun × Nat) (c : Nat), (readsList tl funs)[q]? = some y →
              c < (tl.mats.getD y.1.mat {}).k → posOf tl y.1 y.2 c = pos →
              K9L.termsSum (unitTerms (fun j => a j tU) tl F.planClaimsF nf nb
                (readsList tl funs).length (F.trees.getD tU {}).K pos q y.1.mat c) x = 0) :=
          Prob.cnt_mono fun x hx => by
            obtain ⟨-, -, pos, hpos, hq⟩ :=
              fall_root p g batch nU s tl F funs tU nf nb a hb hs hU hG x hx
            exact ⟨pos, Finset.mem_range.2 hpos, hq⟩
      _ ≤ ∑ pos ∈ Finset.range (nU.getD 2 0), Prob.cnt (fun x : Cb.Gl.E =>
            ∀ (q : Nat) (y : HFun × Nat) (c : Nat), (readsList tl funs)[q]? = some y →
              c < (tl.mats.getD y.1.mat {}).k → posOf tl y.1 y.2 c = pos →
              K9L.termsSum (unitTerms (fun j => a j tU) tl F.planClaimsF nf nb
                (readsList tl funs).length (F.trees.getD tU {}).K pos q y.1.mat c) x = 0) :=
          Prob.cnt_exists_mem_le _ _
      _ ≤ ∑ _pos ∈ Finset.range (nU.getD 2 0), d := by
          refine Finset.sum_le_sum fun pos hpos => ?_
          obtain ⟨q, y, c, hq, hlive, hc, hp⟩ := hcov pos (Finset.mem_range.1 hpos)
          refine (Prob.cnt_mono fun x hQ => hQ q y c hq hc hp).trans
            (K9L.count_terms Cb.Gl.E _ d
              (unitTerms_ok (fun j => a j tU) tl F.planClaimsF nf nb (readsList tl funs).length _ pos
                q y.1.mat c d hcnt (List.getElem?_eq_some_iff.1 hq).1 hd)
              (unitTerms_live (fun j => a j tU) tl F.planClaimsF nf nb (readsList tl funs).length _
                pos q y.1.mat c hlive))
      _ = nU.getD 2 0 * d := by simp
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fall_root
#print axioms VerifiableInference.Desc.First.K8.Honest.fall_few
