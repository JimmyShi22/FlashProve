-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/ItemLaws.lean

Three short general laws on the road to `allSay`, for members 9 and 10 alike.


  `openKinds_of_thr`   at every border of the key's shared thread no open row is marked as a sample row:
                 from the fold in Made, by `flat_keeps₂'`. General in every letter; no e, no B
  `allSay_split`, `allSay_end`, `allSay_three`   a list is covered by consecutive slices
  `openSays_of_rows`   where the group's rows all say, each open row does
  `allSay_of_items`, `saysAt_of_items`   `allSay_of_met`, `saysAt_of_met` with `AllMet` replaced by what they
                 spend: InOrder, OpenSays, sampleItem

Limits. Conditionals: no item is paid here, and `WordsTied` stays a premise. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.KeySharedThread
import Johnson.RunOne.KeyWalkAny
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.Light.ItemLaws
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)
open Desc.K14 (St first)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey sits_two)
open ProofFile.Honest.K12 (TestCoins PlainRows)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : K14.WitLens Wt) (Nm : NumbersS) (Mg₀ : ProofFile.Honest.Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → ProofFile.Honest.Common W₀ Rc TableKey → List Fmt.Drawn → VerifiableInference.Desc.Place × Table)
  (rest : Coins Bk → ProofFile.Honest.Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : ProofFile.Honest.Common W₀ Rc TableKey → Prop) (w : ProofFile.Honest.Common W₀ Rc TableKey)

/-- **At every border no open row is marked as a sample row.** -/
theorem openKinds_of_thr {b : ℕ} {k : Coins Bk} {s : St} {m : ProofFile.Honest.Mid (ProofFile.Honest.Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) b k s m E) : OpenKinds s.st := by
  obtain ⟨-, -, -, -, made, -, -⟩ := u
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hfold⟩ := made
  have e₀ : s₀ = first (parKey Xs Pl).codes m.st.input.key := hbeg
  subst e₀
  have hbs := (sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1
  have hk := VerifiableInference.Desc.Keeps.foldBlocks_keeps
    (VerifiableInference.Desc.Ground.By (fun a b => OpenKinds a → OpenKinds b)
      Johnson.RunOne.KeyKeeps.st₂)
    (fun _ k => k) (fun _ _ _ k₁ k₂ x => k₂ (k₁ x)) _ _
    (fun x hx => Johnson.RunOne.KeyWalk.flat_keeps₂' groundKeeps_openKinds
      Johnson.RunOne.KeyWalk.begin_openKinds x (hbs ▸ List.mem_of_mem_take hx)) _ _ _ _ hfold
  exact hk (OpenKinds.start _)

end

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (S : Statement) (m : Words K)

theorem allSay_split (l : List Row) (i n : ℕ) (h1 : AllSay ρ S ((l.drop i).take n) m)
    (h2 : AllSay ρ S (l.drop (i + n)) m) : AllSay ρ S (l.drop i) m := by
  have e : (l.drop i).drop n = l.drop (i + n) := by
    rw [List.drop_drop]
    try rw [Nat.add_comm]
  intro r hr
  rw [← List.take_append_drop n (l.drop i), e] at hr
  rcases List.mem_append.1 hr with h | h
  · exact h1 r h
  · exact h2 r h

theorem allSay_end (l : List Row) (i : ℕ) (hl : l.length ≤ i) : AllSay ρ S (l.drop i) m := by
  rw [List.drop_eq_nil_of_le hl]
  intro r hr
  cases hr

/-- **Three consecutive slices that reach the end cover the list.** -/
theorem allSay_three (l : List Row) (a b c : ℕ) (hl : l.length ≤ a + b + c)
    (h1 : AllSay ρ S ((l.drop 0).take a) m) (h2 : AllSay ρ S ((l.drop a).take b) m)
    (h3 : AllSay ρ S ((l.drop (a + b)).take c) m) : AllSay ρ S l m := by
  have e3 := allSay_split ρ S m l (a + b) c h3 (allSay_end ρ S m l _ hl)
  have e2 := allSay_split ρ S m l a b h2 e3
  have e1 := allSay_split ρ S m l 0 a h1 (by rw [Nat.zero_add]; exact e2)
  exact e1

/-- **Where the group's rows all say, each open row does.** -/
theorem openSays_of_rows (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (h : AllSay ρ S G.rows.toList m) (i : ℕ) : OpenSays ρ S g i m := by
  intro r hr
  obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
  rw [hG] at hG'
  obtain rfl := Option.some.inj hG'
  exact h r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))

end

/-- **`allSay_of_met` with `AllMet` replaced by what it spends.** -/
theorem allSay_of_items (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (hI : InOrder S) (hK : OpenKinds S) (m : Words GE) (hO : ∀ i, OpenSays rdE S g i m)
    (hS : sampleItem rdE S G.members.toList m) (Ly : GroupLayout) (R : PlainRows)
    (hw : WordsTied S g G m Ly R) :
    AllSay rdE (begun S g G) (runRows S G).toList (ProofFile.Honest.K12.wordsAt (begun S g G) Ly R) :=
  (allSay_begun rdE hI g hG _).2 fun r hr =>
    (says_members (hI.runRows g G hG r hr) _ _ hw).1
      ((runRows_iff_items rdE hK g hG _).2 ⟨hO, hS⟩ r hr)

/-- **`SaysAt` from these**, at the job's own state on entry. -/
theorem saysAt_of_items {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (m : Words GE) (hI : InOrder (A.rec₀ w fr).st) (hK : OpenKinds (A.rec₀ w fr).st)
    (hO : ∀ i, OpenSays rdE (A.rec₀ w fr).st (A.rec₀ w fr).g i m)
    (hS : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      sampleItem rdE (A.rec₀ w fr).st G.members.toList m)
    (hw : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
        (plainMany A w fr C)) :
    SaysAt A w fr C :=
  fun G hG => allSay_of_items _ _ G hG hI hK m hO (hS G hG) _ _ (hw G hG)

end ProofFile.Honest.K12.Light.ItemLaws

#print axioms ProofFile.Honest.K12.Light.ItemLaws.openKinds_of_thr
#print axioms ProofFile.Honest.K12.Light.ItemLaws.allSay_split
#print axioms ProofFile.Honest.K12.Light.ItemLaws.allSay_end
#print axioms ProofFile.Honest.K12.Light.ItemLaws.allSay_three
#print axioms ProofFile.Honest.K12.Light.ItemLaws.openSays_of_rows
#print axioms ProofFile.Honest.K12.Light.ItemLaws.allSay_of_items
#print axioms ProofFile.Honest.K12.Light.ItemLaws.saysAt_of_items
