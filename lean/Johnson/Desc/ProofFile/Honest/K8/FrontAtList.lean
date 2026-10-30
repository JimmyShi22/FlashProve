-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontAtList.lean: THE SMALLNESS TEST: `k8Front` AND
`zeroColumnWeight` (Johnson/Desc/ProofFile/Honest/K8/Share.lean) AGAINST THE LIST "K8.equations",
BOTH WAYS. Statements and proofs, on the list's own text. No prover. LEMMAS; NONE OF THE LIBRARY's
GOALS. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

  `k8Front_iff`, `k8Front_elems`   `k8Front` at a state that holds tl is `zeroColumnWeight tl` at
      the drawn element; it reads of what was drawn the elements alone
  `front_same`   the list's first two steps leave `zeroColumnWeight`
  `eq_bind_err`, `eq_get_err`, `eq_must_err`, `eq_ask_err`   a refusal of the list's text, cut
  **`eqRead_not_zero`**   SILENT: where no sum of the read's matrix's columns is 0 (`LiveAt`), the
      read does not refuse under "internal-f-table-read"; `eqRead_of_front`: so where
      `zeroColumnWeight` finds no column
  **`weight_of_yes`**   IT SPEAKS: a yes of the list says that no column of a matrix on which a
      table lies has the weight 0 at the ledger's batching element
Limits. `eqRead_not_zero` is on one read's text: there that name is borne by one test. In the whole
list a second test, on public numbers, bears the same name. The read's other steps can refuse.
`zeroColumnWeight` runs over all matrices, the list asks those on which a table lies.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port

/-! ## The state's text and the kernel's -/

theorem k8Front_elems (s : S) (d d' : Fmt.Drawn) (h : d.elems = d'.elems) :
    k8Front s [d] = k8Front s [d'] := by
  unfold k8Front
  simp only [List.map_cons, List.map_nil, h]

theorem k8Front_iff (s : S) (tl : HTailF2) (hs : s.tl? = some tl) (x : Cb.Gl.E) :
    k8Front s [chiAt x] = none ↔ zeroColumnWeight tl (E.ofTriple (Slice.ofE x)) = none := by
  unfold k8Front
  rw [hs]
  simp [chiAt]

theorem front_same (tl tla tlb : HTailF2) (front : Nat) (st₀ st₁ st₂ : St)
    (h8 : eqKeys tl front st₀ = .ok (tla, st₁)) (h9 : eqCounts tla front st₁ = .ok (tlb, st₂))
    (θ : E) : zeroColumnWeight tlb θ = zeroColumnWeight tl θ :=
  ((congrArg (fun t => zeroColumnWeight t θ)
    (eqCounts_spec tla tlb front st₁ st₂ h9)).trans rfl).trans
    ((congrArg (fun t => zeroColumnWeight t θ) (eqKeys_spec tl tla front st₀ st₁ h8)).trans rfl)

/-! ## A refusal, cut -/

theorem eq_bind_err {α β : Type} (x : EqM α) (f : α → EqM β) (front : Nat) (s : St) (e : String)
    (h : (x >>= f) front s = .error e) :
    x front s = .error e ∨ ∃ a s1, x front s = .ok (a, s1) ∧ f a front s1 = .error e := by
  have h' : Except.bind (x front s) (fun v => f v.1 front v.2) = .error e := h
  cases hx : x front s with
  | error e' =>
    rw [hx] at h'
    have h2 : (Except.error e' : Except String (β × St)) = .error e := h'
    exact Or.inl (by rw [Except.error.inj h2])
  | ok v =>
    rw [hx] at h'
    exact Or.inr ⟨v.1, v.2, rfl, h'⟩

theorem eq_must_err {n : String} {b : Bool} {front : Nat} {s : St} {e : String}
    (h : EqM.mustAs n b front s = .error e) : e = n ∧ b = false := by
  cases b with
  | true => cases h
  | false => exact ⟨(Except.error.inj h).symm, rfl⟩

theorem eq_get_err {α : Type} {n : String} {o : Option α} {front : Nat} {s : St} {e : String}
    (h : EqM.get n o front s = .error e) : e = n := by
  cases o with
  | some a => cases h
  | none => exact (Except.error.inj h).symm

theorem eq_ask_err {α : Type} {n : String} {f : Fork → Option α} {front : Nat} {s : St}
    {e : String} (h : EqM.ask n f front s = .error e) : e = n := by
  unfold EqM.ask EqM.liftF ForkM.ask at h
  cases hf : f s.1 with
  | some a => simp [hf] at h
  | none =>
    simp only [hf] at h
    exact (Except.error.inj h).symm

/-! ## Silent -/

/-- **Where no sum is 0 the read does not refuse for a sum that is 0.** -/
theorem eqRead_not_zero (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) (front : Nat) (s : St)
    (hl : LiveAt tl (Fn, sg)) :
    eqRead tl Fn sg laid sums front s ≠ .error "internal-f-table-read" := by
  intro h
  unfold eqRead at h
  dsimp only at h
  rcases eq_bind_err _ _ _ _ _ h with h1 | ⟨tU, t1, h1, k1⟩
  · exact absurd (eq_get_err h1) (by decide)
  rcases eq_bind_err _ _ _ _ _ k1 with h2 | ⟨cols, t2, h2, k2⟩
  · exact absurd (eq_ask_err h2) (by decide)
  rcases eq_bind_err _ _ _ _ _ k2 with h3 | ⟨u3, t3, h3, k3⟩
  · exact absurd (eq_must_err h3).1 (by decide)
  rcases eq_bind_err _ _ _ _ _ k3 with h4 | ⟨en, t4, h4, k4⟩
  · exact absurd (eq_get_err h4) (by decide)
  obtain ⟨hen, -⟩ := eq_get_ok h4
  obtain ⟨ents, nz⟩ := en
  have hnz : nz = true :=
    readEnts_keeps tl Fn sg tU cols _ _ _ 0 _ ents nz hen fun j _ hj => hl j (by simpa using hj)
  subst hnz
  dsimp only at k4
  rcases eq_bind_err _ _ _ _ _ k4 with h5 | ⟨u5, t5, h5, k5⟩
  · exact absurd (eq_must_err (n := "internal-f-table-read") h5).2 (by decide)
  rcases eq_bind_err _ _ _ _ _ k5 with h6 | ⟨c0, t6, h6, k6⟩
  · exact absurd (eq_get_err h6) (by decide)
  rcases eq_bind_err _ _ _ _ _ k6 with h7 | ⟨c1, t7, h7, k7⟩
  · exact absurd (eq_get_err h7) (by decide)
  cases k7

/-- So where `zeroColumnWeight` finds no column. -/
theorem eqRead_of_front (tlb tl1 : HTailF2) (front : Nat) (st st1 : St)
    (hW : eqWeights tlb front st = .ok (tl1, st1))
    (h : zeroColumnWeight tlb st.1.theta = none) (Fn : HFun) (hFn : Fn.mat < tl1.NM)
    (sg laid : Nat) (sums : E) (s : St) :
    eqRead tl1 Fn sg laid sums front s ≠ .error "internal-f-table-read" :=
  eqRead_not_zero tl1 Fn sg laid sums front s (live_of_front tlb tl1 front st st1 hW h (Fn, sg) hFn)

/-! ## It speaks -/

/-- **A yes of the list: no column of a matrix on which a table lies has the weight 0.** -/
theorem weight_of_yes {n₀ : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork}
    {k8 : List Claim} (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) (y : HFun × Nat)
    (hy : y ∈ readsList tl funs) (c : Nat) (hc : c < (tl.mats.getD y.1.mat {}).k) :
    isZeroE (columnWeight tl F₁.theta y.1.mat c) = false := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  obtain ⟨tl1, hW, hlive⟩ := eqTail_live before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain ⟨tl2, hW2, -, -, etl, -, new, hs', -, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain rfl : tl2 = tl1 := congrArg Prod.fst (Except.ok.inj (hW2.symm.trans hW))
  obtain ⟨hP, -, hgam⟩ := eqWeights_spec tlb tl2 n₀ s2 s2 hW
  have hF : F₂ = s2.1 := congrArg Prod.fst hs'
  have hθ : s2.1.theta = F₁.theta := by
    rw [← hF]
    exact (eq_side h).theta
  have hcond : y ∈ readsList tl2 funs ∧ c < (tl2.mats.getD y.1.mat {}).k :=
    (same1 (fun t : HTailF2 => (y ∈ readsList t funs ∧ c < (t.mats.getD y.1.mat {}).k)) h etl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr ⟨hy, hc⟩
  have hmat : y.1.mat < tl2.NM := ((mem_readsList tl2 funs y.1 y.2).1 hcond.1).2.1
  have hz := hlive y hcond.1 c hcond.2
  rw [(hgam y.1.mat hmat).2, gamAt_is tl2 s2.1.theta hP.vp y.1.mat c hcond.2, hθ] at hz
  rw [← same1 (fun t : HTailF2 => columnWeight t F₁.theta y.1.mat c) h etl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  exact hz

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Front_iff
#print axioms ProofFile.Honest.K8.front_same
#print axioms ProofFile.Honest.K8.eqRead_not_zero
#print axioms ProofFile.Honest.K8.eqRead_of_front
#print axioms ProofFile.Honest.K8.weight_of_yes
#print axioms ProofFile.Honest.K8.k8Front_elems
#print axioms ProofFile.Honest.K8.eq_bind_err
#print axioms ProofFile.Honest.K8.eq_must_err
#print axioms ProofFile.Honest.K8.eq_get_err
#print axioms ProofFile.Honest.K8.eq_ask_err
