-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumMember.lean: THE PART "THE MASKED SUMCHECK": THE PREMISES OF ITS
SOUNDNESS LAW CAN BE MET TOGETHER. Statements and proofs, in the part's letters.
WHAT IT DOES NOT SHOW. No soundness beyond the law that it repeats (
Part/MaskedSumTruth.lean: sound_hear_true). Not that the prover's program sends these rounds. Not
that a KIND's own start form, end term and ledger meet member_at's conditions: in the closed
statement (member_any) the start form is a CONSTANT form, nothing is kept, the end term is the
summand's value written out, the ledger is a fresh one of just the needed size, the world's slots
are the hiding coefficients themselves. The end values are arbitrary: the law asks nothing of them.
Nothing on probabilities or on hiding. A reading that is onto is a premise (lift). AT Cv = sigma THE
LAW's OWN CONCLUSION (Cv = sigma) SAYS NOTHING: a member can stand nowhere else, by the law itself.
WHAT IT IS. The letters of sound_hear_true stand first, at Cv = sigma (THE TRUTH).
  row_returns_free   the row returns where the sumcheck's own numbers are free.
  zip_fst, zip_wt, zip_val   the variables zipped with the challenges (the lines stand inside
                sound_true's proof).
  member_at     THERE ARE muT, badE, tq, bad WITH: the law's two sizes; THE LAW, to the letter; AND:
                for every start form C with a public part that reads as T, every ledger with the
                call's numbers free, every world that gives C the sum and the own slots the hiding
                coefficients, every end term S0 and kept form that make up the summand at the
                challenges, EVERY lead, EVERY eps, EVERY challenges and end values: there are rounds
                rs at which ALL TEN PREMISES OF THE LAW HOLD TOGETHER: hear returns, readAll
                returns, the target, the start form's value, the slots, the row returns, the row is
                worth 0, the end term, eps is not bad, no challenge is bad; with just these draws.
  run_of_chain  the construction itself, with muT and tq as letters: for a kind's own use.
  member_any    AGAINST ANY SETS badE, bad THAT NEVER FILL THE FIELD (so against whichever sets
                sound_hear hands out, where the field is larger than their sizes): C, the ledger,
                the world, S0 and kept EXHIBITED; all ten premises together; the lead and the end
                values arbitrary; eps and the challenges chosen round by round.

-/
import Johnson.Desc.Part.MaskedSumReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

theorem row_returns_free (h : Heard) (S0 : E) (kept : Aff) (F : Fork)
    (hfree : FreeIn F h.first (h.first + (hidingAt (h.vars.zip h.r)).1.length)) :
    ∃ f G, row h S0 kept F = some (f, G) := by
  obtain ⟨G, hG, _⟩ := hideRun_returns F h.first
    (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE)
    (by rw [Array.size_replicate]; exact hfree)
  have hx : ∃ x, row h S0 kept F = some x := by
    unfold row
    simp only [hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    exact ⟨_, rfl⟩
  obtain ⟨⟨f, G'⟩, hx⟩ := hx
  exact ⟨f, G', hx⟩

theorem zip_fst : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
    (vs.zip (l.map (·.2))).map (·.1) = vs
  | [], _, _ => rfl
  | _ :: _, [], h => h.elim
  | v :: vs, x :: l, h => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [zip_fst vs l h.2.2]

theorem zip_wt : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
    (vs.zip (l.map (·.2))).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ)
  | [], _, _ => rfl
  | _ :: _, [], h => h.elim
  | v :: vs, x :: l, h => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [zip_wt vs l h.2.2]

theorem zip_val : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
    (vs.zip (l.map (·.2))).map (fun x => ρ.val x.2) = (l.map (·.2)).map ρ.val
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | v :: vs, x :: l, h => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [zip_val vs l h.2.2]

/-- **THE HONEST RUN, AS THE PART HEARS IT.** muT and tq (for each eps: the true round polynomial
behind the challenges in front) are letters; asked of them: for all eps and challenges the run of tq
is a Chain from muT + eps T to the masked summand at the challenges, at Cv = sigma. Then, for every
start form, ledger, world, end term and kept form as in member_at, and ALL draws: rounds on which
the hearing and the row return, the row is worth 0, and the moves ARE the run of tq. -/
theorem run_of_chain (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (lead : Nat) (vs : List Var)
    (e : Ends) (hk : shapeOk ⟨lead, vs, some e⟩ = true) (hcoef : ℕ → K) (S : List K → K)
    (sigma T muT : K) (tq : K → List K → K[X])
    (hCh : ∀ (eps : K) (rs : List K),
      rs.length = ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)).length →
      Chain ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) (honest (tq eps) [] rs)
        (muT + eps * T)
        (hid ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) hcoef rs + eps * S rs +
          eps * (T - sigma) * psiProd ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) rs))
    (W : World K) (C : Aff) (F : Fork) (Tt S0 : E) (kept : Aff) (front : List E) (eps : E)
    (rsE values : List E) (hpub : F.publicPart C = some Tt) (hT : ρ.val Tt = T)
    (hC : C.value ρ W = sigma)
    (hfree : FreeIn F F.next (F.next + ownSlots (⟨lead, vs, some e⟩ : Call).all + e.n))
    (hslots : ∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (F.next + i) = hcoef i)
    (hend : S (rsE.map ρ.val) = ρ.val S0 + kept.value ρ W) (hf : front.length = lead)
    (hr : rsE.length = vs.length + 1) (hv : values.length = e.n) :
    ∃ (G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (G' : Fork) (f : Aff),
      hear C ⟨lead, vs, some e⟩ F rs = some (h, G) ∧
      readAll ⟨lead, vs, some e⟩ rs = some R ∧
      ρ.val h.target = T ∧ h.first = F.next ∧
      row h S0 kept G = some (f, G') ∧ f.value ρ W = 0 ∧
      leadScalars ⟨lead, vs, some e⟩ rs = some front ∧ R.eps = eps ∧ h.r = rsE ∧
      R.values = values ∧ R.mu = lift muT ∧
      movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds (addE R.mu (mulE R.eps h.target)) =
        honest (tq (ρ.val eps)) [] (rsE.map ρ.val) ∧
      rs.length = vs.length + 3 ∧
      ∀ P : E → Prop, (∀ k, P (lift k)) → (∀ x ∈ front, P x) → P eps → (∀ x ∈ rsE, P x) →
        (∀ x ∈ values, P x) → ∀ r ∈ rs,
          (∀ x, Fmt.ItemValue.e x ∈ r.vals → P (E.ofTriple x)) ∧
          ∀ x, x ∈ r.drawn.elems → P (E.ofTriple x) := by
  have hall : ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)).length = vs.length + 1 := by
    rw [List.length_map]
    show (vs ++ [Var.point zeroE (e.dY + 1)]).length = _
    simp
  have hch := hCh (ρ.val eps) (rsE.map ρ.val) (by rw [List.length_map, hr, hall])
  have hc0 : ρ.val (addE (lift muT) (mulE eps Tt)) = muT + ρ.val eps * T := by
    rw [ρ.add, ρ.mul, hlift, hT]
  obtain ⟨l, b1, b2, b3, b4, b5, b6, b7⟩ := honest_read ρ lift hlift lead vs e hk front hf
    (lift muT) eps Tt rsE values hv _ _ (by rw [hc0]; exact hch) (honest_chal _ _ [])
  obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := readAll_spec b1
  have hlens : Lens (⟨lead, vs, some e⟩ : Call).all l := lens_of_read hvr (two_le_all hk)
  obtain ⟨G, hG, g1, _, g3, g4⟩ := hear_returns C ⟨lead, vs, some e⟩ hk F Tt hpub _ _ b1
    (by
      show FreeIn F _ (_ + values.length)
      rw [hv]
      exact hfree.sub (by omega) (le_refl _))
  have hle := hidingAt_length_le ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))
  rw [zip_fst _ l hlens] at hle
  obtain ⟨f, G', hrow⟩ := row_returns_free
    { start := C, target := Tt, eps := eps,
      claim := after (⟨lead, vs, some e⟩ : Call).all l (addE (lift muT) (mulE eps Tt)),
      first := F.next, vars := (⟨lead, vs, some e⟩ : Call).all, r := l.map (·.2),
      sEnd := F.next + ownSlots (⟨lead, vs, some e⟩ : Call).all } S0 kept G
    ⟨by
      show F.next + (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).1.length ≤ G.ns
      rw [g1]
      have := hfree.1
      omega, g3, fun j j1 j2 => by
      have j1' : F.next ≤ j := j1
      have j2' : j < F.next +
          (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).1.length := j2
      rw [g4, if_neg (by omega)]
      exact hfree.2.2 j j1' (by omega)⟩
  refine ⟨G, _, _, _, G', f, hG, b1, hT, rfl, hrow, ?_, b2, rfl, b3, rfl, rfl, b4, b6,
    fun P h1 h2 h3 h4 h5 => b7 P h1 h2 (h1 muT) h3 h4 h5⟩
  have hv0 := row_value ρ W hrow
  obtain ⟨hu1, hu2⟩ := hidingAt_val ρ
    ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2))) hcoef
  rw [zip_wt ρ _ l hlens, zip_val ρ _ l hlens] at hu1 hu2
  have hdot : dotFrom ρ (fun i => W.slot (F.next + i))
      (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).1 =
      dotFrom ρ hcoef (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by omega)
  have hv1 : f.value ρ W =
      dotFrom ρ (fun i => W.slot (F.next + i))
        (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).1 +
      ρ.val eps * ρ.val (hidingAt ((⟨lead, vs, some e⟩ : Call).all.zip (l.map (·.2)))).2 *
        (ρ.val Tt - C.value ρ W) + ρ.val eps * kept.value ρ W -
      (ρ.val (after (⟨lead, vs, some e⟩ : Call).all l (addE (lift muT) (mulE eps Tt))) -
        ρ.val eps * ρ.val S0) := hv0
  rw [hv1, hdot, hu1, hu2, b5, hT, hC, b3]
  linear_combination (-(ρ.val eps)) * hend

/-- **THE LAW's PREMISES CAN BE MET TOGETHER, AT THE TRUTH, FOR ALL DRAWS.** -/
theorem member_at (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (lead : Nat) (vs : List Var)
    (e : Ends) (hk : shapeOk ⟨lead, vs, some e⟩ = true) (hcoef : ℕ → K) (S : List K → K)
    (sigma : K) (hS : IsSum ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) S sigma) (T : K) :
    ∃ (muT : K) (badE : K → Finset K) (tq : K → K → List K → K[X])
      (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) pre.length) ∧
      (∀ (W : World K) (C : Aff) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (S0 : E)
        (kept : Aff) (F' G' : Fork) (f : Aff),
        hear C ⟨lead, vs, some e⟩ F rs = some (h, G) → readAll ⟨lead, vs, some e⟩ rs = some R →
        ρ.val h.target = T → C.value ρ W = sigma →
        (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (h.first + i) = hcoef i) →
        row h S0 kept F' = some (f, G') → f.value ρ W = 0 →
        S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds
            (addE R.mu (mulE R.eps h.target)))) →
        sigma = sigma) ∧
      ∀ (W : World K) (C : Aff) (F : Fork) (Tt S0 : E) (kept : Aff) (front : List E) (eps : E)
        (rsE values : List E),
        F.publicPart C = some Tt → ρ.val Tt = T → C.value ρ W = sigma →
        FreeIn F F.next (F.next + ownSlots (⟨lead, vs, some e⟩ : Call).all + e.n) →
        (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (F.next + i) = hcoef i) →
        S (rsE.map ρ.val) = ρ.val S0 + kept.value ρ W →
        front.length = lead → rsE.length = vs.length + 1 → values.length = e.n →
        ∃ (G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (G' : Fork) (f : Aff),
          hear C ⟨lead, vs, some e⟩ F rs = some (h, G) ∧
          readAll ⟨lead, vs, some e⟩ rs = some R ∧
          ρ.val h.target = T ∧ C.value ρ W = sigma ∧
          (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (h.first + i) = hcoef i) ∧
          row h S0 kept G = some (f, G') ∧ f.value ρ W = 0 ∧
          S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W ∧
          ρ.val R.eps ∉ badE (ρ.val R.mu) ∧
          (haveI := Classical.decEq K
           NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
            (movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds
              (addE R.mu (mulE R.eps h.target)))) ∧
          leadScalars ⟨lead, vs, some e⟩ rs = some front ∧ R.eps = eps ∧ h.r = rsE ∧
          R.values = values ∧ ρ.val R.mu = muT := by
  obtain ⟨muT, badE, tq, bad, _, hE, hB, hlaw, hEt, hBt, hCh⟩ :=
    sound_hear_true ρ lead vs e hk hcoef S sigma hS T sigma
  refine ⟨muT, badE, tq, bad, hE, hB, hlaw, ?_⟩
  intro W C F Tt S0 kept front eps rsE values hpub hT hC hfree hslots hend hf hr hv
  obtain ⟨G, rs, h, R, G', f, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, _⟩ :=
    run_of_chain ρ lift hlift lead vs e hk hcoef S sigma T muT (tq muT) (hCh rfl muT) W C F Tt S0
      kept front eps rsE values hpub hT hC hfree hslots hend hf hr hv
  have hmu : ρ.val R.mu = muT := by rw [c11, hlift]
  refine ⟨G, rs, h, R, G', f, c1, c2, c3, hC, fun i hi => by rw [c4]; exact hslots i hi, c5, c6,
    by rw [c9]; exact hend, ?_, ?_, c7, c8, c9, c10, hmu⟩
  · rw [hEt rfl]
    simp
  · rw [c12, hmu, c8]
    haveI := Classical.decEq K
    exact noBad_honest (hBt muT (ρ.val eps)) _

/-- A fresh ledger of n numbers. -/
def freshLedger (n : Nat) : Fork := ({} : Fork).slots n

theorem freshLedger_free (n : Nat) : FreeIn (freshLedger n) 0 n := by
  refine ⟨le_refl _, ?_, fun j _ hj => ?_⟩
  · show (Array.replicate n false).size = n
    simp
  · show (Array.replicate n false).getD j true = false
    simp [Array.getD_eq_getD_getElem?, hj]

theorem publicPart_const (F : Fork) (x : E) : F.publicPart (Aff.ofConst x) = some x := by
  unfold Fork.publicPart Aff.ofConst
  simp

/-! ## Against any sets that never fill the field -/

/-- Challenges outside sets that never fill the field, chosen round by round. (It follows
OnBytes/Desc/First/NormBridge/HonestRounds.lean, exists_noBad_from, closely.) -/
theorem exists_noBad_from [DecidableEq K] (tq : List K → K[X])
    (bad : List (K[X] × K) → K[X] → Finset K) (hfree : ∀ pre g, ∃ x, x ∉ bad pre g) :
    ∀ (n : ℕ) (pre : List K) (front : List (K[X] × K)), ∃ rs : List K, rs.length = n ∧
      ∀ i m, (honest tq pre rs)[i]? = some m →
        m.2 ∉ bad (front ++ (honest tq pre rs).take i) m.1
  | 0, _, _ => ⟨[], rfl, fun i m h => by simp [honest] at h⟩
  | n + 1, pre, front => by
    obtain ⟨r, hr⟩ := hfree front (tq pre)
    obtain ⟨rs, hl, hrs⟩ := exists_noBad_from tq bad hfree n (pre ++ [r]) (front ++ [(tq pre, r)])
    refine ⟨r :: rs, by rw [List.length_cons, hl], fun i m h => ?_⟩
    rw [honest_cons] at h ⊢
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      rw [← Option.some.inj h, List.take_zero, List.append_nil]
      exact hr
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have := hrs i m h
      rw [List.append_assoc] at this
      exact this

theorem exists_noBad [DecidableEq K] (tq : List K → K[X])
    (bad : List (K[X] × K) → K[X] → Finset K) (hfree : ∀ pre g, ∃ x, x ∉ bad pre g) (n : ℕ) :
    ∃ rs : List K, rs.length = n ∧ NoBad bad (honest tq [] rs) := by
  obtain ⟨rs, hl, h⟩ := exists_noBad_from tq bad hfree n [] []
  exact ⟨rs, hl, fun i m hi => by
    have := h i m hi
    rwa [List.nil_append] at this⟩

/-- **A MEMBER AGAINST ANY BAD SETS THAT NEVER FILL THE FIELD**: so against whichever sets the law
(sound_hear) hands out at these letters, where the field is larger than their sizes. Every letter
under the law's "for all" is exhibited; all ten premises hold together; T = Cv = sigma. The lead and
the end values are arbitrary; eps and the challenges are CHOSEN, round by round. -/
theorem member_any (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (lead : Nat) (vs : List Var)
    (e : Ends) (hk : shapeOk ⟨lead, vs, some e⟩ = true) (hcoef : ℕ → K) (S : List K → K)
    (sigma : K) (hS : IsSum ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) S sigma)
    (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K)
    (hfE : ∀ mu, ∃ x, x ∉ badE mu) (hfB : ∀ mu eps pre g, ∃ x, x ∉ bad mu eps pre g)
    (front values : List E) (hf : front.length = lead) (hv : values.length = e.n) :
    ∃ (W : World K) (C : Aff) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (S0 : E)
      (kept : Aff) (G' : Fork) (f : Aff),
      hear C ⟨lead, vs, some e⟩ F rs = some (h, G) ∧
      readAll ⟨lead, vs, some e⟩ rs = some R ∧
      ρ.val h.target = sigma ∧ C.value ρ W = sigma ∧
      (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (h.first + i) = hcoef i) ∧
      row h S0 kept G = some (f, G') ∧ f.value ρ W = 0 ∧
      S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W ∧
      ρ.val R.eps ∉ badE (ρ.val R.mu) ∧
      (haveI := Classical.decEq K
       NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
        (movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds
          (addE R.mu (mulE R.eps h.target)))) ∧
      leadScalars ⟨lead, vs, some e⟩ rs = some front ∧ R.values = values := by
  haveI := Classical.decEq K
  obtain ⟨muT, _, tq, _, _, _, _, _, _, _, hCh⟩ :=
    sound_hear_true ρ lead vs e hk hcoef S sigma hS sigma sigma
  obtain ⟨epsK, heps⟩ := hfE muT
  obtain ⟨rsK, hrl, hnb⟩ := exists_noBad (tq muT epsK) (bad muT epsK) (hfB muT epsK)
    (vs.length + 1)
  have hmap : (rsK.map lift).map ρ.val = rsK := by
    rw [List.map_map]
    have e1 : (ρ.val ∘ lift) = id := funext hlift
    rw [e1, List.map_id]
  obtain ⟨G, rs, h, R, G', f, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, _⟩ :=
    run_of_chain ρ lift hlift lead vs e hk hcoef S sigma sigma muT (tq muT) (hCh rfl muT)
      ⟨hcoef, fun _ _ _ => 0⟩ (Aff.ofConst (lift sigma))
      (freshLedger (ownSlots (⟨lead, vs, some e⟩ : Call).all + e.n)) (lift sigma)
      (lift (S rsK)) {} front (lift epsK) (rsK.map lift) values (publicPart_const _ _) (hlift _)
      (by rw [Aff.value_ofConst, hlift])
      (by
        have := freshLedger_free (ownSlots (⟨lead, vs, some e⟩ : Call).all + e.n)
        show FreeIn _ 0 (0 + _ + _)
        rw [Nat.zero_add]
        exact this)
      (fun i _ => by
        show hcoef (0 + i) = hcoef i
        rw [Nat.zero_add])
      (by rw [hmap, hlift, Aff.value_empty, add_zero]) hf (by rw [List.length_map, hrl]) hv
  have hmu : ρ.val R.mu = muT := by rw [c11, hlift]
  refine ⟨_, _, _, G, rs, h, R, _, _, G', f, c1, c2, c3, by rw [Aff.value_ofConst, hlift],
    fun i _ => ?_, c5, c6, ?_, ?_, ?_, c7, c10⟩
  · rw [c4]
    show hcoef (0 + i) = hcoef i
    rw [Nat.zero_add]
  · rw [c9, hmap, hlift, Aff.value_empty, add_zero]
  · rw [hmu, c8, hlift]
    exact heps
  · rw [c12, hmu, c8, hlift, hmap]
    convert hnb

end VerifiableInference.Desc.Part.MaskedSum

end
