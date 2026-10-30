-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroRuns.lean: THE RUNS OF CLAIMS AND THE RUNS BEHIND THE BATCHING STAND IN
`KeepsZero`; SO EACH OF THESE MAKERS, WHOLE. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksRuns.lean, WITH THE ROWS' FIRST COLUMNS (`l0s`,
Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE OF
KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under a
new name; the others are called where they lie. None of the library's goals. No prover stands in it;
nothing on completeness, soundness or hiding.

  `kz_wrote`, `kz_head`, `kz_puts2`   a run's writing of the ledger
  **`rests_kz`**   RunRests KeepsZero (Johnson/Desc/First/Link/Law/RunRel.lean): the nine known
      runs; four of them from the ground facts themselves (BY HAND: the library's sameLooks_of has
      no like here)
  `k4C_wholeZ`, `k8W_wholeZ`, `k11_wholeZ`, `k5N_wholeZ`, `k6_runs_kz`, `k6S_wholeZ`   the makers,
      whole
  `k1Later_wholeZ`, `readsLay_wholeZ`, `readsHead_wholeZ`, `readsAtt_wholeZ`   these have no run
Limits. The nine runs that RunRests names. "Whole" is the library's Keeps.Whole
(Johnson/Desc/FoldKeeps.lean). Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroVia
import Johnson.Desc.First.Link.Law.LooksRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote blockAtC frontAtC_pays backAtC_pays)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.Kinds.Head.Law (join_hands)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9L
open Johnson.Desc.First.ForkMerge (headMergeClaim headClaimMergeKind)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

section

/-- A run's writing of the ledger into a layers' link's own part. -/
theorem kz_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (h : G.trees.map l0s = a.F.trees.map l0s) : KeepsZero e e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
  · simp [S.fork?, h1]
  · simp [S.link?, h1]
  · exact congrArg (·.link) (Option.some.inj hL')
  · rw [← Option.some.inj hG]
    exact h

/-- Into the head's own part. -/
theorem kz_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (h : G.trees.map l0s = a.F.trees.map l0s) :
    KeepsZero e { e with here := .head { a with F := G } } := by
  by_cases ho : a.opened = true
  · refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, h1, ho]
    · simp [S.link?, h1, ho]
    · have e0 : some a.L = some L' := by simpa [S.link?, ho] using hL'
      exact congrArg (·.link) (Option.some.inj e0)
    · have e0 : some G = some G' := by simpa [S.fork?, ho] using hG
      rw [← Option.some.inj e0]
      exact h
  · exact kz_none (by simp [S.fork?, ho])

end

section

/-- The two layings of the approximate range proof's runs. -/
theorem kz_puts2 {e : S} {F G : Fork} (hF : e.fork? = some F) (tl : HTailF2)
    (h : G.trees.map l0s = F.trees.map l0s) : KeepsZero e ((e.putTl tl).putFork G) :=
  kz_trans _ _ _
    (kzL_same (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link]))
    (kz_putFork (F := F) (by rw [First.K8.putTl_fork]; exact hF) h)

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_kz : RunRests KeepsZero where
  refl := kz_refl
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact kz_wrote hw (by rw [hc.trees])
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact kz_wrote hw (by rw [hc.trees])
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact kz_wrote hw rfl
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact kz_head h1 (congrArg (·.map l0s) (OnBytes.Desc.First.K4.hideRun_core hrunG).trees)
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact kz_head h1 (congrArg (·.map l0s) (OnBytes.Desc.First.K4.paid_core _ i).trees)
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, hF, _, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    exact kz_puts2 hF tl' (congrArg (·.map l0s) (First.TailClaims.Law.eq_side he).trees)
  ls e e₁ hr := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    exact kzL_same (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    exact kz_puts2 hF tl (l0s_of_sums (congrArg (·.1) (core_coefBody tl g F)))

/-! ## The makers, whole -/

theorem k4C_wholeZ (p : OnBytes.Desc.First.K4.Par) : Whole KeepsZero (blockAtC p) := by
  refine ⟨k4C_kz p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact (rests_kz).front p _ rfl n s y.1 y.2 h
    · obtain rfl := List.mem_singleton.1 hc
      exact (rests_kz).back p _ rfl n s y.1 y.2 h
  · obtain rfl := List.mem_singleton.1 hc
    exact (rests_kz).free p _ rfl s s' h

theorem k8W_wholeZ (p : First.K8.ParW) : Whole KeepsZero (First.K8.whole p) := by
  refine ⟨k8W_kz p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain rfl := List.mem_singleton.1 hc
    obtain ⟨r, hr, hu⟩ := k8_equations_under p
    obtain rfl := Option.some.inj hr
    exact (rests_kz).eq n s y.1 y.2 (hu n s y.1 y.2 h)
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨r, hr, hu⟩ := k8_lsTail_under p
      obtain rfl := Option.some.inj hr
      exact (rests_kz).ls s s' (hu s s' h)
    · obtain rfl := List.mem_singleton.1 hc
      obtain ⟨r, hr, hu⟩ := k8_tests_under p
      obtain rfl := Option.some.inj hr
      exact (rests_kz).tests p.nU s s' (hu s s' h)

theorem k11_wholeZ (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Whole KeepsZero (headClaimMergeKind P) := by
  refine ⟨k11_kz P, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  obtain rfl := List.mem_singleton.1 hc
  exact (rests_kz).merge n s y.1 y.2 h

theorem k5N_wholeZ (W : Verify.Public) (l g : ℕ) (before : List (ℕ × ℕ)) {b : Block S Claim}
    (h : First.Att.P.k5AtN W l g before = some b) : Whole KeepsZero b := by
  refine ⟨k5_kz_at h, ?_, ?_⟩
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    intro c hc n s y e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    obtain ⟨fs, e', -⟩ := First.Att.P.runN_ok e
    obtain ⟨r0, hr0, hx⟩ := List.mem_flatMap.1 hr
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Meaning.K2.runsK_keep KeepsZero (kz_refl) _ _ _ hr0 n s _ e'
      · obtain rfl := List.mem_singleton.1 hx
        exact joinRun_kz _ (fun _ => rfl) (fun _ _ => rfl) _ n s (fs, y.2) e'
    · obtain rfl := List.mem_singleton.1 hx
      exact Meaning.K2.runsK_keep KeepsZero (kz_refl) _ _ _ hr0 n s _ e'
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun _ hc => nomatch hc

open VerifiableInference.Desc.Kinds.Head in
/-- K6's three own runs hand the state back, at a seat whose laying of the key forms does. -/
theorem k6_runs_kz {Cl : Type} (L : Seat S) (h4 : ∀ s k, L.setKeyForms s k = s)
    (cl : Kinds.Form → Cl) (link piece : ℕ) (p : Par) :
    ∀ c ∈ (kind cl L link piece p).claims, ∀ n, FnCl KeepsZero (c.2 n) := by
  intro c hc n s y h
  have hc' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl p L := hc
  unfold runsBy at hc'
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨⟨g, b, x⟩, -, h⟩ := ok_bind h
  obtain ⟨fs, -, h⟩ := ok_bind h
  cases h
  dsimp only
  split
  · rw [h4]
    exact kz_refl s
  · exact kz_refl s

open VerifiableInference.Desc.Kinds.Head in
theorem k6S_wholeZ {W : Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : seatedClaims W l before = some b) : Whole KeepsZero b := by
  refine ⟨k6_kz_seated h, ?_, ?_⟩
  · unfold seatedClaims at h
    obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold blockClaims at h0
    obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
    intro c hc
    have hc' : c ∈ (kind (K3.seatCalls asClaim).claim (seatAt W.hS iU3) l 4
          (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.take 1 ++
        [("join", K3.joinRun (K3.seatCalls asClaim) (callerKeys
          (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))
          (seatAt W.hS iU3)))] ++
        (kind (K3.seatCalls asClaim).claim (seatAt W.hS iU3) l 4
          (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.drop 1 := hc
    rcases List.mem_append.1 hc' with k | k
    · rcases List.mem_append.1 k with k | k
      · exact k6_runs_kz _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_take k)
      · obtain rfl := List.mem_singleton.1 k
        exact fun n => joinRun_kz _ (fun _ => rfl) (fun _ _ => rfl) _ n
    · exact k6_runs_kz _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_drop k)
  · unfold seatedClaims at h
    obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold blockClaims at h0
    obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
    exact fun _ hc => nomatch hc

theorem k1Later_wholeZ {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Whole KeepsZero (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨k1Later_kz q gp link piece moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsLay_wholeZ (P : K8.ReadsQuiet.PG) :
    Whole KeepsZero (K8.ReadsQuiet.layers P) :=
  ⟨readsLay_kz P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsHead_wholeZ (P : K8.ReadsQuiet.PH) :
    Whole KeepsZero (K8.ReadsQuiet.head P) :=
  ⟨readsHead_kz P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsAtt_wholeZ {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : Whole KeepsZero b := by
  refine ⟨readsAtt_kz h, ?_, ?_⟩ <;>
    (unfold First.Att.readsAtO at h
     obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
     exact fun _ hc => nomatch hc)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kz_wrote
#print axioms VerifiableInference.Desc.LinkJoin.kz_head
#print axioms VerifiableInference.Desc.LinkJoin.kz_puts2
#print axioms VerifiableInference.Desc.LinkJoin.rests_kz
#print axioms VerifiableInference.Desc.LinkJoin.k4C_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k8W_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k11_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k5N_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k6_runs_kz
#print axioms VerifiableInference.Desc.LinkJoin.k6S_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_wholeZ
