-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SymbolsFew.lean: THE SMALLNESS TEST: THE COUNT FOR ITS TEST `selfSymbols`
("no weight on a symbol array is 0": Johnson/Desc/First/TailClaims/SelfTests.lean). Definitions with
code, statements and proofs. No prover. Lemmas; none of the library's goals.

Each matrix has an array of symbols; its tie lays on entry c of that array's row 0 the negative of
column c's sum under the powers of the batching element, lifted above every plain claim's exponent.
  `sym_cut`   behind a yes of the list "K8.equations": what the ties and reads lay on such an entry,
      as terms at the element, in the letters of the data in front
  `symbolsLaid tl`   with code, on public numbers: no matrix's array of symbols is the digits'
      array, another matrix's, or what a read's vector's array reads as; the shape's number of
      columns is the matrix's
  `symbolsLive tl`   with code, on the drawn matrix: every column of every matrix has an entry other
      than 0 (`columnLive`, Johnson/Desc/K8/Honest/FallCount.lean)
  `symbolsNo s`   the state holds data and a ledger at which `selfSymbols` says no; `symCount tl`:
      how many entries the test asks
  **`symbols_few`**   IF tl passes both tests, g meets `Gathers` at s and d bounds the exponents:
      THEN at most symCount tl * d field elements are challenges at which batch says yes and, behind
      it, `selfSymbols` says no
  `symbols_from`   in the form `CountFrom` (Johnson/Desc/K8/Honest/CountFrom.lean)
By: `behind_total` (BehindTotal.lean) · `ties_at_symbol`, `symTerms_ok`, `symTerms_live`, `eq_gamX`
(TiesAt.lean) · `noneZero_no` (CoefCode.lean) · K9L.count_terms.
Limits. `symbolsLive` is a premise on a matrix drawn in front. `Gathers` and `symbolsLaid` are
premises. What other claims lay on a symbol array is not asked: they are plain, at exponents below
the plan's number. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.TiesAt
import Johnson.Desc.K8.Honest.CountFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- What is asked of a matrix's array of symbols. -/
def SymAt (u : HTailF2) (mu c : Nat) : Prop :=
  mu < u.NM ∧ c < (u.mats.getD mu {}).k ∧ (u.shp.getD mu {}).k = (u.mats.getD mu {}).k ∧
    u.ix.ZZ ≠ u.gtTree.getD mu 0 ∧
    (∀ nu, nu < u.NM → nu ≠ mu → u.gtTree.getD nu 0 ≠ u.gtTree.getD mu 0) ∧
    (u.ix.U.getD 0 none).getD 0 ≠ u.gtTree.getD mu 0 ∧
    (u.ix.U.getD 2 none).getD 0 ≠ u.gtTree.getD mu 0

/-- **What the ties and reads lay on a symbol's entry, in the letters of the data in front.** -/
theorem sym_cut {n₀ : Nat} {tl tl' tl1 : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork}
    {k8 : List Claim} (geq : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (hP : Powered tl1 F₁.theta) (mu c : Nat) (h : SymAt tl mu c) :
    (((List.range tl1.NM).map
          (tieTerm Reading.gl (oneAt (tl.gtTree.getD mu 0) 0 c) tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl (oneAt (tl.gtTree.getD mu 0) 0 c) tl1 F₁) 0
          (readsList tl1 funs)) -
      (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs)) =
      K9L.termsSum (fromOn (fun j => - signOf (K := Cb.Gl.E)
          (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau +
            (j - (F₁.planClaimsF + firstOf tl mu))) 0)) tl.tau (F₁.planClaimsF + firstOf tl mu))
        (Reading.gl.val F₁.theta) := by
  have h1 : SymAt tl1 mu c :=
    (same1 (fun u : HTailF2 => SymAt u mu c) geq etl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr h
  obtain ⟨hmu, hc, hk, hZ, hdist, hU0, hU2⟩ := h1
  have egt : tl1.gtTree.getD mu 0 = tl.gtTree.getD mu 0 :=
    same1 (fun u : HTailF2 => u.gtTree.getD mu 0) geq etl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have e1 : tl'.gamX = tl1.gamX := (congrArg (fun z : HTailF2 => z.gamX) etl).trans rfl
  have e2 : gamAt tl' mu = gamAt tl1 mu :=
    (congrArg (fun z : HTailF2 => gamAt z mu) etl).trans rfl
  have e3 : tl'.NM = tl1.NM := (congrArg (fun z : HTailF2 => z.NM) etl).trans rfl
  have hgX : tl1.gamX.getD mu #[] = gamAt tl1 mu := by
    rw [← e1, ← e2]
    exact eq_gamX geq mu (by rw [e3]; exact hmu)
  rw [← same1 (fun u : HTailF2 => K9L.termsSum (fromOn (fun j => - signOf (K := Cb.Gl.E)
      (u.cfF.getD ((u.cfFirst.getD mu 0 + c) * u.tau +
        (j - (F₁.planClaimsF + firstOf u mu))) 0)) u.tau (F₁.planClaimsF + firstOf u mu))
      (Reading.gl.val F₁.theta)) geq etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl), ← egt,
    ties_at_symbol tl1 F₁ hP funs mu c hmu hc hk hgX hZ hdist hU0 hU2,
    gamAt_val Reading.gl hP mu c hc, termsSum_column]
  have ef : tl1.eqFirst.getD mu 0 = firstOf tl1 mu :=
    hP.eqFirst_val mu (Nat.le_of_lt (hP.lt_shp mu hmu))
  rw [ef]

/-- On public numbers. -/
def symbolsLaid (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    tl.ix.ZZ != tl.gtTree.getD mu 0 && (tl.ix.U.getD 0 none).getD 0 != tl.gtTree.getD mu 0 &&
    (tl.ix.U.getD 2 none).getD 0 != tl.gtTree.getD mu 0 &&
    (tl.shp.getD mu {}).k == (tl.mats.getD mu {}).k &&
    (List.range tl.NM).all fun nu => nu == mu || tl.gtTree.getD nu 0 != tl.gtTree.getD mu 0

/-- On the drawn matrix. -/
def symbolsLive (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    (List.range (tl.mats.getD mu {}).k).all fun c => columnLive tl mu c

/-- `selfSymbols` says no at the state. -/
def symbolsNo (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => !selfSymbols q.1 q.2
  | none => false

/-- How many entries the test asks. -/
def symCount (tl : HTailF2) : ℕ :=
  ∑ mu ∈ Finset.range tl.NM, (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k

theorem symAt_of_laid (tl : HTailF2) (h : symbolsLaid tl = true) (mu c : Nat) (hmu : mu < tl.NM)
    (hc : c < (tl.mats.getD mu {}).k) : SymAt tl mu c := by
  simp only [symbolsLaid, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h mu hmu
  exact ⟨hmu, hc, a4, a1, fun nu hnu hne => (a5 nu hnu).resolve_left hne, a2, a3⟩

/-- **The count.** -/
theorem symbols_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hP : symbolsLaid tl = true)
    (hL : symbolsLive tl = true) (hG : Gathers p g s tl funs nf nb a)
    (hd : F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch symbolsNo s [chiAt x] = true) ≤
      symCount tl * d := by
  have root : ∀ x : Cb.Gl.E, askBehind batch symbolsNo s [chiAt x] = true →
      nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
      ∃ mu ∈ Finset.range tl.NM,
        ∃ c ∈ Finset.range ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k),
          c < (tl.mats.getD mu {}).k ∧
          K9L.termsSum (symTerms (fun j => a j (tl.gtTree.getD mu 0) 0 c) tl F.planClaimsF nf nb
            (readsList tl funs).length mu c) x = 0 := by
    intro x hx
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      rw [hbt] at hx
      change symbolsNo t' = true at hx
      obtain ⟨tl', G, F₁, F₂, k8, n₀, g₀, h1, geq, -, hθ, hpl, -, shG, hcnt, -, hcut⟩ :=
        behind_total p g batch s t' tl F funs nf nb a hb hs hG x hbt
      refine ⟨hcnt, ?_⟩
      have T : ∀ {α : Type} (f : HTailF2 → α),
          (∀ (t : HTailF2) (y : Option Nat), f { t with joinObj9 := y } = f t) →
          (∀ (t : HTailF2) (y : E), f { t with bitFactor9 := y } = f t) →
          (∀ (t u : HTailF2), f { t with
            vt := u.vt, vp := u.vp, eqFirst := u.eqFirst, rowX := u.rowX, loX := u.loX,
            gamX := u.gamX, gamV := u.gamV, foldTakenF := u.foldTakenF } = f t) →
          (∀ (t : HTailF2) (y z : Array Nat) (w : Nat),
            f { t with tieObj := y, tiesOn := z, nX4Laid := w } = f t) → f tl' = f tl :=
        fun f r1 r2 r3 r4 => eq_same f geq r1 r2 r3 r4
      have eNM : tl'.NM = tl.NM :=
        T (fun u => u.NM) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      have eshp : tl'.shp = tl.shp :=
        T (fun u => u.shp) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      have egt : tl'.gtTree = tl.gtTree :=
        T (fun u => u.gtTree) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ _ _ => rfl)
      unfold symbolsNo at hx
      rw [h1] at hx
      have hno : selfSymbols tl' G = false := by simpa using hx
      unfold selfSymbols at hno
      obtain ⟨mu, hmu', hr'⟩ := List.all_eq_false.1 hno
      rw [eNM] at hmu'
      have hmu := List.mem_range.1 hmu'
      rw [eshp, egt] at hr'
      have hr'' : noneZero (weightsOf G (tl.gtTree.getD mu 0) 0) 0
          ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k) = false :=
        Bool.eq_false_of_not_eq_true hr'
      obtain ⟨u, hu, hz⟩ := noneZero_no _ 0 _ (Or.inl (Nat.zero_le _)) hr''
      rw [Nat.zero_add] at hz
      -- the shape's J is 1 behind a yes; its k is the matrix's
      obtain ⟨tl0, hP0, -, etl0, -⟩ := hcut 0 0 0
      have hJ : (tl.shp.getD mu {}).J = 1 := by
        have e : tl0.shp = tl.shp ∧ tl0.NM = tl.NM :=
          ⟨same1 (fun u => u.shp) geq etl0 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ _ _ _ => rfl),
            same1 (fun u => u.NM) geq etl0 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ _ _ _ => rfl)⟩
        rw [← e.1]
        exact (hP0.shape mu (by rw [e.2]; exact hmu)).1
      have hkk : (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k := by
        simp only [symbolsLaid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          List.mem_range] at hP
        exact (hP mu hmu).1.2
      have wt : ∀ c, c < (tl.mats.getD mu {}).k →
          G.total Reading.gl (oneAt (tl.gtTree.getD mu 0) 0 c) - G.total Reading.gl allZero =
            K9L.termsSum (symTerms (fun j => a j (tl.gtTree.getD mu 0) 0 c) tl F.planClaimsF nf nb
              (readsList tl funs).length mu c) x := by
        intro c hc
        obtain ⟨tl1, hP1, -, etl, hc1⟩ := hcut (tl.gtTree.getD mu 0) 0 c
        rw [hc1, sym_cut geq etl hP1 mu c (symAt_of_laid tl hP mu c hmu hc), hθ, hpl]
        unfold symTerms plainTerms
        rw [termsSum_append, termsSum_append]
      have hL0 : ((G.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L0 =
          ((F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L0 := by
        rw [L0_of_shape, shG, ← L0_of_shape]
      have hu' : u < (tl.mats.getD mu {}).k := by
        rw [hJ, Nat.one_mul, hkk] at hu
        exact hu
      by_cases h0 : ((G.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L0 = 0
      · refine ⟨mu, Finset.mem_range.2 hmu, u, Finset.mem_range.2 hu, hu', ?_⟩
        rw [← wt u hu', total_oneAt Reading.gl G _ _ _ h0, hz]
        exact Reading.gl.zero
      · refine ⟨mu, Finset.mem_range.2 hmu, 0,
          Finset.mem_range.2 (Nat.lt_of_le_of_lt (Nat.zero_le _) hu),
          Nat.lt_of_le_of_lt (Nat.zero_le _) hu', ?_⟩
        rw [← wt 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hu')]
        exact total_below Reading.gl G _ _ 0 (Nat.pos_of_ne_zero h0)
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch symbolsNo s [chiAt x] = true
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨hcnt, -⟩ := root x₀ hx₀
    simp only [symbolsLive, List.all_eq_true, List.mem_range] at hL
    calc Prob.cnt (fun x : Cb.Gl.E => askBehind batch symbolsNo s [chiAt x] = true)
        ≤ Prob.cnt (fun x : Cb.Gl.E => ∃ mu ∈ Finset.range tl.NM,
            ∃ c ∈ Finset.range ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k),
              c < (tl.mats.getD mu {}).k ∧
              K9L.termsSum (symTerms (fun j => a j (tl.gtTree.getD mu 0) 0 c) tl F.planClaimsF
                nf nb (readsList tl funs).length mu c) x = 0) :=
          Prob.cnt_mono fun x hx => (root x hx).2
      _ ≤ ∑ mu ∈ Finset.range tl.NM, Prob.cnt (fun x : Cb.Gl.E =>
            ∃ c ∈ Finset.range ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k),
              c < (tl.mats.getD mu {}).k ∧
              K9L.termsSum (symTerms (fun j => a j (tl.gtTree.getD mu 0) 0 c) tl F.planClaimsF
                nf nb (readsList tl funs).length mu c) x = 0) :=
          Prob.cnt_exists_mem_le _ _
      _ ≤ ∑ mu ∈ Finset.range tl.NM, (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k * d := by
          refine Finset.sum_le_sum fun mu hmu => ?_
          refine (Prob.cnt_exists_mem_le _ _).trans ?_
          refine (Finset.sum_le_sum (g := fun _ => d) fun c _ => ?_).trans (by simp)
          by_cases hc : c < (tl.mats.getD mu {}).k
          · refine (Prob.cnt_mono fun x hx => hx.2).trans (K9L.count_terms Cb.Gl.E _ d
              (symTerms_ok _ tl F.planClaimsF nf nb _ mu c d hcnt (Finset.mem_range.1 hmu) hd)
              (symTerms_live _ tl F.planClaimsF nf nb _ mu c
                (hL mu (Finset.mem_range.1 hmu) c hc)))
          · rw [Prob.cnt_false fun x hx => hc hx.1]
            exact Nat.zero_le _
      _ = symCount tl * d := by
          unfold symCount
          rw [Finset.sum_mul]
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

/-- In the form of a count, the test a letter. -/
theorem symbols_from :
    CountFrom (fun tl _ => symbolsLaid tl && symbolsLive tl) symbolsNo symCount := by
  intro p g batch s tl F funs nf nb d a hb hs hok hG hd
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
  exact symbols_few p g batch s tl F funs nf nb d a hb hs h1 h2 hG hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.sym_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.symAt_of_laid
#print axioms VerifiableInference.Desc.First.K8.Honest.symbols_few
#print axioms VerifiableInference.Desc.First.K8.Honest.symbols_from
