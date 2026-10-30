-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesRuns.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE KINDS' RUNS OF CLAIMS: EACH SEATED SUB-PROTOCOL WHOLE. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksRuns.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (15): keepsLooks_wrote → keepsArrNames_wrote · keepsLooks_head → keepsArrNames_head
· sameLooks_of → sameArrNames_of · keeps_puts2 → keeps_puts2N · rests_keeps → rests_keepsN ·
k4C_whole → k4C_wholeN · k8W_whole → k8W_wholeN · k11_whole → k11_wholeN · k5N_whole → k5N_wholeN ·
k6_runs_keep → k6_runs_keepN · k6S_whole → k6S_wholeN · k1Later_whole → k1Later_wholeN ·
readsLay_whole → readsLay_wholeN · readsHead_whole → readsHead_wholeN · readsAtt_whole →
readsAtt_wholeN.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksRuns
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesAre
import Johnson.Desc.K8.Honest.Names.ArrNamesVia
import Johnson.Desc.K8.Honest.Names.ArrNamesSeated
import Johnson.Desc.K8.Honest.Names.ArrNamesFrame
import Johnson.Desc.K8.Honest.Names.ArrNamesK5
import Johnson.Desc.K8.Honest.Names.ArrNamesK6

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
variable (shOf : ℕ → List String)

/-- A run's writing of the ledger into a layers' link's own part. -/
theorem keepsArrNames_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (h : G.trees.map treeName = a.F.trees.map treeName) : KeepsArrNames shOf e e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
  · simp [S.fork?, h1]
  · simp [S.link?, h1]
  · exact congrArg (·.link) (Option.some.inj hL')
  · rw [← Option.some.inj hG]
    exact h

/-- Into the head's own part. -/
theorem keepsArrNames_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (h : G.trees.map treeName = a.F.trees.map treeName) :
    KeepsArrNames shOf e { e with here := .head { a with F := G } } := by
  by_cases ho : a.opened = true
  · refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, h1, ho]
    · simp [S.link?, h1, ho]
    · have e0 : some a.L = some L' := by simpa [S.link?, ho] using hL'
      exact congrArg (·.link) (Option.some.inj e0)
    · have e0 : some G = some G' := by simpa [S.fork?, ho] using hG
      rw [← Option.some.inj e0]
      exact h
  · exact keeps_noneN shOf (by simp [S.fork?, ho])

end

/-- A step on the ledger that hands on every `ArrNamesAre sh` leaves the names. -/
theorem sameArrNames_of {F G : Fork} (h : ∀ sh, ArrNamesAre sh F → ArrNamesAre sh G) :
    G.trees.map treeName = F.trees.map treeName := by
  have e : G.trees.toList.map treeName = F.trees.toList.map treeName := h _ rfl
  apply Array.toList_inj.1
  rw [Array.toList_map, Array.toList_map]
  exact e

section
variable (shOf : ℕ → List String)

/-- The two layings of the approximate range proof's runs. -/
theorem keeps_puts2N {e : S} {F G : Fork} (hF : e.fork? = some F) (tl : HTailF2)
    (h : G.trees.map treeName = F.trees.map treeName) : KeepsArrNames shOf e
        ((e.putTl tl).putFork G) :=
  keeps_transN shOf _ _ _
    (keeps_sameN shOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link]))
    (keeps_putForkN shOf (F := F) (by rw [First.K8.putTl_fork]; exact hF) h)

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_keepsN : RunRests (KeepsArrNames shOf) where
  refl := keeps_reflN shOf
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact keepsArrNames_wrote shOf hw (by rw [hc.trees])
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact keepsArrNames_wrote shOf hw (by rw [hc.trees])
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact keepsArrNames_wrote shOf hw rfl
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact keepsArrNames_head shOf h1
        (sameArrNames_of fun sh => (arrNames_rests sh).hide _ _ _ _ _ hrunG)
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact keepsArrNames_head shOf h1 (sameArrNames_of fun sh => (arrNames_rests sh).paid _ i)
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, hF, _, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    exact keeps_puts2N shOf hF tl'
        (sameArrNames_of fun sh => (arrNames_rests sh).eq _ _ _ _ _ _ _ he)
  ls e e₁ hr := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    exact keeps_sameN shOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    exact keeps_puts2N shOf hF tl (sameArrNames_of fun sh => (arrNames_rests sh).coef tl g F)

theorem k4C_wholeN (p : OnBytes.Desc.First.K4.Par) : Whole (KeepsArrNames shOf) (blockAtC p) := by
  refine ⟨k4C_stepsN shOf p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact (rests_keepsN shOf).front p _ rfl n s y.1 y.2 h
    · obtain rfl := List.mem_singleton.1 hc
      exact (rests_keepsN shOf).back p _ rfl n s y.1 y.2 h
  · obtain rfl := List.mem_singleton.1 hc
    exact (rests_keepsN shOf).free p _ rfl s s' h

theorem k8W_wholeN (p : First.K8.ParW) : Whole (KeepsArrNames shOf) (First.K8.whole p) := by
  refine ⟨k8W_stepsN shOf p, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain rfl := List.mem_singleton.1 hc
    obtain ⟨r, hr, hu⟩ := k8_equations_under p
    obtain rfl := Option.some.inj hr
    exact (rests_keepsN shOf).eq n s y.1 y.2 (hu n s y.1 y.2 h)
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨r, hr, hu⟩ := k8_lsTail_under p
      obtain rfl := Option.some.inj hr
      exact (rests_keepsN shOf).ls s s' (hu s s' h)
    · obtain rfl := List.mem_singleton.1 hc
      obtain ⟨r, hr, hu⟩ := k8_tests_under p
      obtain rfl := Option.some.inj hr
      exact (rests_keepsN shOf).tests p.nU s s' (hu s s' h)

theorem k11_wholeN (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Whole (KeepsArrNames shOf) (headClaimMergeKind P) := by
  refine ⟨k11_stepsN shOf P, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  obtain rfl := List.mem_singleton.1 hc
  exact (rests_keepsN shOf).merge n s y.1 y.2 h

theorem k5N_wholeN (W : Verify.Public) (l g : ℕ) (before : List (ℕ × ℕ)) {b : Block S Claim}
    (h : First.Att.P.k5AtN W l g before = some b) : Whole (KeepsArrNames shOf) b := by
  refine ⟨k5_steps_atN shOf h, ?_, ?_⟩
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    intro c hc n s y e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    obtain ⟨fs, e', -⟩ := First.Att.P.runN_ok e
    obtain ⟨r0, hr0, hx⟩ := List.mem_flatMap.1 hr
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Meaning.K2.runsK_keep (KeepsArrNames shOf) (keeps_reflN shOf) _ _ _ hr0 n s _ e'
      · obtain rfl := List.mem_singleton.1 hx
        exact joinRun_keepsN shOf _ (fun _ => rfl) (fun _ _ => rfl) _ n s (fs, y.2) e'
    · obtain rfl := List.mem_singleton.1 hx
      exact Meaning.K2.runsK_keep (KeepsArrNames shOf) (keeps_reflN shOf) _ _ _ hr0 n s _ e'
  · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun _ hc => nomatch hc

open VerifiableInference.Desc.Kinds.Head in
/-- K6's three own runs hand the state back, at a seat whose laying of the key forms does. -/
theorem k6_runs_keepN {Cl : Type} (L : Seat S) (h4 : ∀ s k, L.setKeyForms s k = s)
    (cl : Kinds.Form → Cl) (link piece : ℕ) (p : Par) :
    ∀ c ∈ (kind cl L link piece p).claims, ∀ n, FnCl (KeepsArrNames shOf) (c.2 n) := by
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
    exact keeps_reflN shOf s
  · exact keeps_reflN shOf s

open VerifiableInference.Desc.Kinds.Head in
theorem k6S_wholeN {W : Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : seatedClaims W l before = some b) : Whole (KeepsArrNames shOf) b := by
  refine ⟨k6_steps_seatedN shOf h, ?_, ?_⟩
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
      · exact k6_runs_keepN shOf _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_take k)
      · obtain rfl := List.mem_singleton.1 k
        exact fun n => joinRun_keepsN shOf _ (fun _ => rfl) (fun _ _ => rfl) _ n
    · exact k6_runs_keepN shOf _ (fun _ _ => rfl) _ _ _ _ c (List.mem_of_mem_drop k)
  · unfold seatedClaims at h
    obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold blockClaims at h0
    obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
    exact fun _ hc => nomatch hc

theorem k1Later_wholeN {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Whole (KeepsArrNames shOf) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨k1Later_stepsN shOf q gp link piece moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsLay_wholeN (P : K8.ReadsQuiet.PG) :
    Whole (KeepsArrNames shOf) (K8.ReadsQuiet.layers P) :=
  ⟨readsLay_stepsN shOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsHead_wholeN (P : K8.ReadsQuiet.PH) :
    Whole (KeepsArrNames shOf) (K8.ReadsQuiet.head P) :=
  ⟨readsHead_stepsN shOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsAtt_wholeN {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : Whole (KeepsArrNames shOf) b := by
  refine ⟨readsAtt_stepsN shOf h, ?_, ?_⟩ <;>
    (unfold First.Att.readsAtO at h
     obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
     exact fun _ hc => nomatch hc)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keepsArrNames_wrote
#print axioms VerifiableInference.Desc.LinkJoin.keepsArrNames_head
#print axioms VerifiableInference.Desc.LinkJoin.sameArrNames_of
#print axioms VerifiableInference.Desc.LinkJoin.keeps_puts2N
#print axioms VerifiableInference.Desc.LinkJoin.rests_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.k4C_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k8W_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k11_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k5N_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k6_runs_keepN
#print axioms VerifiableInference.Desc.LinkJoin.k6S_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_wholeN
