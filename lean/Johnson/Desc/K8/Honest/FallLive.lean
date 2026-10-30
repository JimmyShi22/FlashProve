-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLive.lean: A YES OF THE LIST "K8.equations" SAYS THAT NO COLUMN OF THE DRAWN
MATRIX THAT A READ USES IS ALL 0. Statements and proofs, on the list's own text, for the count of
Johnson/Desc/K8/Honest/FallCount.lean. No block, no prover.

Why. A read's text asks that none of its columns' sums under the powers of the batching element is 0
("internal-f-table-read"). The sum of a column that is all 0 is the element 0 at every value of the
batching element. So where such a column stands the list is made at no value: the batching block
refuses there, and the count of the values at which it says yes and a weight is 0 needs no premise on
the drawn matrix.

  `readEnts_live`   a read's entries made with the mark "none is 0" still set: no sum is 0
  `eqRead_live`     so a yes of one read
  `stepLE`, `eqTail_live`, **`eq_live`**   so a yes of the list, for every read of its list of reads
  `foldColumn_dead`   the sum of a column that is all 0 is the element 0
  **`eq_columnLive`**   a yes of the list: each column of each read's matrix has an entry other than 0
The proof of `eqTail_live` walks the text's four loops as `eqTail_marks`
(Johnson/Desc/First/TailClaims/EquationsCover.lean) does.
Limits: from a yes alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

theorem readEnts_live (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (minus : E) (gc : Array E) :
    ∀ (count c : Nat) (ents : Array Ent) (nz : Bool) (out : Array Ent),
      tl.readEnts Fn sg tU cols minus gc count c ents nz = some (out, true) →
      nz = true ∧ ∀ j, c ≤ j → j < c + count → isZeroE (gc.getD j zeroE) = false := by
  intro count
  induction count with
  | zero =>
    intro c ents nz out h
    simp only [HTailF2.readEnts, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2, fun j h1 h2 => by omega⟩
  | succ n ih =>
    intro c ents nz out h
    unfold HTailF2.readEnts at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      obtain ⟨h1, h2⟩ := ih _ _ _ _ h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      refine ⟨h1.1, fun j hj1 hj2 => ?_⟩
      by_cases e : j = c
      · rw [e]
        exact h1.2
      · exact h2 j (by omega) (by omega)

/-- No sum of a column of the read's matrix is the element 0. -/
def LiveAt (tl : HTailF2) (x : HFun × Nat) : Prop :=
  ∀ c, c < (tl.mats.getD x.1.mat {}).k →
    isZeroE ((tl.gamV.getD x.1.mat #[]).getD c zeroE) = false

theorem eqRead_live (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) (front : Nat)
    (s s' : St) (u : Unit) (h : eqRead tl Fn sg laid sums front s = .ok (u, s')) :
    LiveAt tl (Fn, sg) := by
  unfold eqRead at h
  dsimp only at h
  obtain ⟨tU, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 h
  rw [(eq_get_ok h1).2] at k1
  obtain ⟨cols, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  rw [(eq_ask_ok h2).2] at k2
  obtain ⟨u3, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_must_ok h3).2] at k3
  obtain ⟨en, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨hen, e4⟩ := eq_get_ok h4
  rw [e4] at k4
  obtain ⟨ents, nz⟩ := en
  dsimp only at k4
  obtain ⟨u5, t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  obtain ⟨hnz, -⟩ := eq_test_ok h5
  rw [hnz] at hen
  intro c hc
  exact (readEnts_live tl Fn sg tU cols _ _ _ _ _ _ ents hen).2 c (Nat.zero_le c)
    (by rw [Nat.zero_add]; exact hc)

/-- One read of the text, as far as its columns' sums go. -/
def stepLE (tl : HTailF2) (x : HFun × Nat) (_ : MProd Nat (Array (Array Bool))) (_ : St)
    (_ : MProd Nat (Array (Array Bool))) (_ : St) : Prop :=
  LiveAt tl x ∧ True

/-- The text behind the four first claims, as far as the reads' columns' sums go. -/
theorem eqTail_live (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ tl1 : HTailF2, eqWeights tlb front s = .ok (tl1, s) ∧
      ∀ x ∈ readsList tl1 funs, LiveAt tl1 x := by
  unfold eqTail at h
  obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨en0, et0⟩ := eq_claims_ok h0
  rw [en0, et0] at k0
  obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 k0
  obtain ⟨b4, et1⟩ := eq_must_ok h1
  rw [et1] at k1
  obtain ⟨tl1, t2, hW, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  have eW : t2 = s := by
    unfold eqWeights at hW
    obtain ⟨x3, t3, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 hW
    rw [(eq_ask_ok g1).2] at g2
    exact (eq_get_ok g2).2
  rw [eW] at hW k2
  obtain ⟨sz, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_ask_ok h3).2] at k3
  obtain ⟨bT, sT, hT, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨bR, sR, hR, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  -- the reads: four loops, flattened
  have rR := forInE_inv front _
    (fun mu => RunFoldE (fun un => RunFoldE (fun (Fn : HFun) => RunFoldE (stepLE tl1)
      (segsOf tl1 mu un Fn)) funs.toList) [0, 2])
    (by
      intro mu b s r s1 hb
      obtain ⟨b2, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u', x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      rw [((eq_pure_ok _ _ _ _ _).1 c2).2] at d2
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d2
      rw [ex]
      refine ⟨_, er, ?_⟩
      refine forInE_inv front _ _ ?_ _ _ _ _ _ c1
      intro un b s r s1 hb
      obtain ⟨b3, y1, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u'', y2, c4, d4⟩ := (eq_bind_ok _ _ _ _ _).1 d3
      rw [((eq_pure_ok _ _ _ _ _).1 c4).2] at d4
      obtain ⟨er', ex'⟩ := (eq_pure_ok _ _ _ _ _).1 d4
      rw [ex']
      refine ⟨_, er', ?_⟩
      refine forInE_inv_array front _ _ ?_ _ _ _ _ _ c3
      intro Fn b s r s1 hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [(eq_must_ok e1).2] at f1
        obtain ⟨v2, z2, e2, f2⟩ := (eq_bind_ok _ _ _ _ _).1 f1
        rw [(eq_must_ok e2).2] at f2
        obtain ⟨b4', z3, e3, f3⟩ := (eq_bind_ok _ _ _ _ _).1 f2
        obtain ⟨v4, z4, e4, f4⟩ := (eq_bind_ok _ _ _ _ _).1 f3
        rw [((eq_pure_ok _ _ _ _ _).1 e4).2] at f4
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f4
        rw [ex2]
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_pos hc]
        apply runFoldE_map
        refine forInE_inv front _ _ ?_ _ _ _ _ _ e3
        intro sg b s r s1 hb
        obtain ⟨rd, w1, p1, q1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [(eq_get_ok p1).2] at q1
        obtain ⟨v5, w2, p2, q2⟩ := (eq_bind_ok _ _ _ _ _).1 q1
        obtain ⟨v6, w3, p3, q3⟩ := (eq_bind_ok _ _ _ _ _).1 q2
        rw [((eq_pure_ok _ _ _ _ _).1 p3).2] at q3
        obtain ⟨er3, ex3⟩ := (eq_pure_ok _ _ _ _ _).1 q3
        rw [ex3]
        exact ⟨_, er3, eqRead_live tl1 Fn sg _ _ front _ _ _ p2, trivial⟩
      · rw [if_neg hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [((eq_pure_ok _ _ _ _ _).1 e1).2] at f1
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f1
        rw [ex2]
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl⟩) _ _ _ _ _ hR
  have s1 := runFoldE_mono _
    (fun mu => RunFoldE (fun un => RunFoldE (stepLE tl1)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ h2 => runFoldE_mono _
      (fun un => RunFoldE (stepLE tl1) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ h3 => runFoldE_flat (stepLE tl1) (segsOf tl1 mu un) _ _ _ _ _ h3)
      _ _ _ _ _ h2) _ _ _ _ _ rR
  have s2 := runFoldE_mono _
    (fun mu => RunFoldE (stepLE tl1)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ h2 => runFoldE_flat (stepLE tl1)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ h2) _ _ _ _ _ s1
  have fP := runFoldE_flat (stepLE tl1)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ s2
  exact ⟨tl1, hW, (runFoldE_all (LiveAt tl1) (fun _ _ _ _ _ => True) _ _ _ _ _ fP).1⟩

/-- The sum of a column that is all 0 is the element 0, whatever the weights. -/
theorem foldColumn_dead (cf : Array Int) (base tau : Nat) (v : Array E)
    (h : ∀ u, u < tau → cf.getD (base + u) 0 = 0) : HTailF2.foldColumn cf base tau v = zeroE := by
  have key : ∀ (l : List E) (n : Nat), n + l.length ≤ tau →
      (l.foldl (fun (s : E × Nat) y =>
        let x := cf.getD (base + s.2) 0
        (if x == 0 then s.1 else if x < 0 then subE s.1 y else addE s.1 y, s.2 + 1))
        (zeroE, n)).1 = zeroE := by
    intro l
    induction l with
    | nil => intro n _; rfl
    | cons y l ih =>
      intro n hn
      simp only [List.length_cons] at hn
      rw [List.foldl_cons]
      have h0 : cf.getD (base + n) 0 = 0 := h n (by omega)
      simp only [h0, beq_self_eq_true, if_true]
      exact ih (n + 1) (by omega)
  unfold HTailF2.foldColumn
  rw [← Array.foldl_toList]
  refine key _ 0 ?_
  simp only [Array.length_toList, Array.size_extract]
  omega

/-- **A yes of the list: each column of each read's matrix has an entry other than 0.** -/
theorem eq_columnLive {n₀ : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork}
    {k8 : List Claim} (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) (y : HFun × Nat)
    (hy : y ∈ readsList tl funs) (c : Nat) (hc : c < (tl.mats.getD y.1.mat {}).k) :
    columnLive tl y.1.mat c = true := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  obtain ⟨tl1, hW, hlive⟩ := eqTail_live before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain ⟨tl2, hW2, -, -, etl, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain rfl : tl2 = tl1 := congrArg Prod.fst (Except.ok.inj (hW2.symm.trans hW))
  obtain ⟨-, -, hgam⟩ := eqWeights_spec tlb tl2 n₀ s2 s2 hW
  have hcond : y ∈ readsList tl2 funs ∧ c < (tl2.mats.getD y.1.mat {}).k :=
    (same1 (fun t : HTailF2 => (y ∈ readsList t funs ∧ c < (t.mats.getD y.1.mat {}).k)) h etl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr ⟨hy, hc⟩
  rw [← same1 (fun t : HTailF2 => columnLive t y.1.mat c) h etl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  have hmat : y.1.mat < tl2.NM := ((mem_readsList tl2 funs y.1 y.2).1 hcond.1).2.1
  have hz := hlive y hcond.1 c hcond.2
  rw [(hgam y.1.mat hmat).2, gamAt, getD_map_range _ _ _ _ hcond.2] at hz
  cases hl : columnLive tl2 y.1.mat c with
  | true => rfl
  | false =>
    exfalso
    have hdead : ∀ u, u < tl2.tau →
        tl2.cfF.getD ((tl2.cfFirst.getD y.1.mat 0 + c) * tl2.tau + u) 0 = 0 := by
      intro u hu
      simp only [columnLive, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq,
        Decidable.not_not] at hl
      exact hl u hu
    rw [foldColumn_dead _ _ _ _ hdead] at hz
    exact absurd hz (by decide)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_live
#print axioms VerifiableInference.Desc.First.K8.Honest.foldColumn_dead
#print axioms VerifiableInference.Desc.First.K8.Honest.eq_columnLive
