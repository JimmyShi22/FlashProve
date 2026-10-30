-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsRuns.lean: THE NINE KNOWN RUNS; THE MAKERS, WHOLE.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
The walk is adapted from LooksRuns.lean (beside this file): that file's theorems on the arrays'
looks, carried over by program to the two numbers, name by name (…looks… ↦ …slots…; else a letter S
behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksRuns
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.Link.Law.SlotsVia
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.Batch.Law.K8Under
import Johnson.Goal.Meaning.RecK5K8
import Johnson.Stored.HeadAddsAtS

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

section
variable (nsOf : ℕ → ℕ × ℕ)

/-- A run's writing of the ledger into a layers' link's own part. -/
theorem keepsSlots_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (h : sl G = sl a.F) : KeepsSlots nsOf e e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
  · simp [S.fork?, h1]
  · simp [S.link?, h1]
  · exact congrArg (·.link) (Option.some.inj hL')
  · rw [← Option.some.inj hG]
    exact h

/-- Into the head's own part. -/
theorem keepsSlots_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (h : sl G = sl a.F) :
    KeepsSlots nsOf e { e with here := .head { a with F := G } } := by
  by_cases ho : a.opened = true
  · refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, h1, ho]
    · simp [S.link?, h1, ho]
    · have e0 : some a.L = some L' := by simpa [S.link?, ho] using hL'
      exact congrArg (·.link) (Option.some.inj e0)
    · have e0 : some G = some G' := by simpa [S.fork?, ho] using hG
      rw [← Option.some.inj e0]
      exact h
  · exact keeps_noneS nsOf (by simp [S.fork?, ho])

end

/-- A step on the ledger that hands on every `LooksAre sh` leaves the two numbers. -/
theorem sameSlots_of {F G : Fork} (h : ∀ sh, SlotsAre sh F → SlotsAre sh G) :
    sl G = sl F := h _ rfl

section
variable (nsOf : ℕ → ℕ × ℕ)

/-- The two layings of the approximate range proof's runs. -/
theorem keeps_puts2S {e : S} {F G : Fork} (hF : e.fork? = some F) (tl : HTailF2)
    (h : sl G = sl F) : KeepsSlots nsOf e ((e.putTl tl).putFork G) :=
  keeps_transS nsOf _ _ _
    (keeps_sameS nsOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link]))
    (keeps_putForkS nsOf (F := F) (by rw [First.K8.putTl_fork]; exact hF) h)

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_keepsS : RunRests (KeepsSlots nsOf) where
  refl := keeps_reflS nsOf
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact keepsSlots_wrote nsOf hw (by rw [(sl_core hc)])
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact keepsSlots_wrote nsOf hw (by rw [(sl_core hc)])
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact keepsSlots_wrote nsOf hw rfl
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact keepsSlots_head nsOf h1 (sameSlots_of fun sh => (slots_rests sh).hide _ _ _ _ _ hrunG)
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact keepsSlots_head nsOf h1 (sameSlots_of fun sh => (slots_rests sh).paid _ i)
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, hF, _, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    exact keeps_puts2S nsOf hF tl' (sameSlots_of fun sh => (slots_rests sh).eq _ _ _ _ _ _ _ he)
  ls e e₁ hr := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    exact keeps_sameS nsOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    exact keeps_puts2S nsOf hF tl (sameSlots_of fun sh => (slots_rests sh).coef tl g F)

/-! ## The makers, whole -/

theorem k4C_wholeS (p : OnBytes.Desc.First.K4.Par) : Whole (KeepsSlots nsOf) (blockAtC p) := by
  refine ⟨k4C_stepsS nsOf p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact (rests_keepsS nsOf).front p _ rfl n s y.1 y.2 h
    · obtain rfl := List.mem_singleton.1 hc
      exact (rests_keepsS nsOf).back p _ rfl n s y.1 y.2 h
  · obtain rfl := List.mem_singleton.1 hc
    exact (rests_keepsS nsOf).free p _ rfl s s' h

theorem k8W_wholeS (p : First.K8.ParW) : Whole (KeepsSlots nsOf) (First.K8.whole p) := by
  refine ⟨k8W_stepsS nsOf p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain rfl := List.mem_singleton.1 hc
    obtain ⟨r, hr, hu⟩ := k8_equations_under p
    obtain rfl := Option.some.inj hr
    exact (rests_keepsS nsOf).eq n s y.1 y.2 (hu n s y.1 y.2 h)
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨r, hr, hu⟩ := k8_lsTail_under p
      obtain rfl := Option.some.inj hr
      exact (rests_keepsS nsOf).ls s s' (hu s s' h)
    · obtain rfl := List.mem_singleton.1 hc
      obtain ⟨r, hr, hu⟩ := k8_tests_under p
      obtain rfl := Option.some.inj hr
      exact (rests_keepsS nsOf).tests p.nU s s' (hu s s' h)

theorem k11_wholeS (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Whole (KeepsSlots nsOf) (headClaimMergeKind P) := by
  refine ⟨k11_stepsS nsOf P, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  obtain rfl := List.mem_singleton.1 hc
  exact (rests_keepsS nsOf).merge n s y.1 y.2 h

theorem k5N_wholeS (W : Verify.Public) (l g : ℕ) (before : List (ℕ × ℕ)) {b : Block S Claim}
    (h : First.Att.P.k5AtN W l g before = some b) : Whole (KeepsSlots nsOf) b := by
  refine ⟨k5_steps_atS nsOf h, ?_, ?_⟩
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    intro c hc n s y e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    obtain ⟨fs, e', -⟩ := First.Att.P.runN_ok e
    obtain ⟨r0, hr0, hx⟩ := List.mem_flatMap.1 hr
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Meaning.K2.runsK_keep (KeepsSlots nsOf) (keeps_reflS nsOf) _ _ _ hr0 n s _ e'
      · obtain rfl := List.mem_singleton.1 hx
        exact joinRun_keepsS nsOf _ (fun _ => rfl) (fun _ _ => rfl) _ n s (fs, y.2) e'
    · obtain rfl := List.mem_singleton.1 hx
      exact Meaning.K2.runsK_keep (KeepsSlots nsOf) (keeps_reflS nsOf) _ _ _ hr0 n s _ e'
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun _ hc => nomatch hc

open VerifiableInference.Desc.Kinds.Head in
/-- K6's three own runs hand the state back, at a seat whose laying of the key forms does. -/
theorem k6_runs_keepS {Cl : Type} (L : Seat S) (h4 : ∀ s k, L.setKeyForms s k = s)
    (cl : Kinds.Form → Cl) (link piece : ℕ) (p : Par) :
    ∀ c ∈ (kind cl L link piece p).claims, ∀ n, FnCl (KeepsSlots nsOf) (c.2 n) := by
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
    exact keeps_reflS nsOf s
  · exact keeps_reflS nsOf s

open VerifiableInference.Desc.Kinds.Head in
theorem k6S_wholeS {W : Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : seatedClaims W l before = some b) : Whole (KeepsSlots nsOf) b := by
  refine ⟨k6_steps_seatedS nsOf h, ?_, ?_⟩
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
      · exact k6_runs_keepS nsOf _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_take k)
      · obtain rfl := List.mem_singleton.1 k
        exact fun n => joinRun_keepsS nsOf _ (fun _ => rfl) (fun _ _ => rfl) _ n
    · exact k6_runs_keepS nsOf _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_drop k)
  · unfold seatedClaims at h
    obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold blockClaims at h0
    obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
    exact fun _ hc => nomatch hc

theorem k1Later_wholeS {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Whole (KeepsSlots nsOf) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨k1Later_stepsS nsOf q gp link piece moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsLay_wholeS (P : K8.ReadsQuiet.PG) :
    Whole (KeepsSlots nsOf) (K8.ReadsQuiet.layers P) :=
  ⟨readsLay_stepsS nsOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsHead_wholeS (P : K8.ReadsQuiet.PH) :
    Whole (KeepsSlots nsOf) (K8.ReadsQuiet.head P) :=
  ⟨readsHead_stepsS nsOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsAtt_wholeS {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : Whole (KeepsSlots nsOf) b := by
  refine ⟨readsAtt_stepsS nsOf h, ?_, ?_⟩ <;>
    (unfold First.Att.readsAtO at h
     obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
     exact fun _ hc => nomatch hc)

end

end VerifiableInference.Desc.LinkJoin
