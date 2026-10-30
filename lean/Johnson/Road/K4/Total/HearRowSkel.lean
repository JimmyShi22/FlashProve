-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/HearRowSkel.lean: A SENTENCE OF Johnson/Road/K4/Total/RowReturns.lean, PROVED:
HearRowSkel: two returns of K4's hearing (hear at the plain engine), at one sub-proof's plan hp and
one group g, at two values of the public parameters with one layout, one list of reads and one
layout of the weights, leave merges of one skeleton (RowSkel): the merge's points are as long, and
the claims' rests name, one by one, one unit with factors of the same sizes. Statements and proofs.

WHY IT HOLDS.
  The point: the merge appends one challenge a column bit (wo_sizes,
    Johnson/Road/K4/MergeSizes.lean).
  The units: a claim's unit is wsLay.unitOf X (v.lay lam) (ClaimEnv.claim,
    OnBytes/Model/LayerPanels.lean): X and lam come off the layout's calls and segments, v.lay off
    the group's number and the layout. No drawn element is read for them. THE WALK: claim, claimsA,
    claimsT, weightClaims, claimE: where two environments of one layout, group and layout of the
    weights both return, the lists name the same units in the same order.
  The sizes: THE MERGE's OWN TEST pins them: it says no unless every claim has as many factors as
    its unit has groups, each of the sizes that its group asks (wsClaimShape; claimFits_iff,
    facFits_iff, Johnson/Top/H0/MergeLaw/Fits.lean). So two claims on one unit that both pass are
    alike; and what is left of two claims that are alike is alike (rowPart_alike,
    OnBytes/Flat/LinksFreeLayer.lean).

  `fac_pin`, `facs_pin`, `shape_pin`: the sizes, from the test. `rowPart_sizes`: so of the rests.
  `mapM_both`, `all2_flatten`, `all2_with`, `all2_zip_map2`: lists, member by member.
  `EnvPub c c₀`: two environments of claims of one layout, group and layout of the weights.
  `claim_ui`, `claim_both`, `claimsA_both`, `claimsT_both`, `weightClaims_both`, `claimE_ui`: the
    walk.
  `merge_shapes`: where the merge returns, its test on the claims' sizes held.
  `mergeClaims_both`: the lists that two hearings hand to the merge name the same units.
  `hear_row_skel : HearRowSkel`: the sentence.
New: the walk for the units, and that the test pins the sizes.
**Limits.** Five premises, as the sentence has them: the two returns, AT ONE hp AND g, and three
equations on the two values of the public parameters, which hold by rfl where they differ in the
tokens alone. It does not say that the hearing returns, nor that the pending row can be made.
Nothing on soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no
member.


-/
import Johnson.Road.K4.Total.RowReturns
import Johnson.Road.K4.MergeSizes
import Johnson.Top.H0.MergeLaw.Flat
import OnBytes.Flat.LinksFreeLayer
import OnBytes.Flat.PendingFreeOf
import OnBytes.Desc.First.K4.MergeClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Env ClaimEnv isAcc callsTS)
open OnBytes.Flat (All2 RecSizes FacAlike ClaimAlike rowPart_alike)
open Johnson.Desc.First.ForkMerge (facFits claimFits)
open VerifiableInference.Desc.First.MergeLaw (facFits_iff claimFits_iff claimFits_eq hear_of_flat
  mergeHear_inv)
open OnBytes.Desc.First.P1 (powers_size)

/-! ## The merge's test pins the sizes -/

theorem fac_pin {x x' : WsFac} {g : WsGrp} (h : facFits x g = true) (h' : facFits x' g = true) :
    FacAlike x x' := by
  rcases (facFits_iff x g).1 h with ⟨c, a1, a2, a3⟩ | ⟨c, a1, a2, a3⟩
  · rcases (facFits_iff x' g).1 h' with ⟨_, b1, b2, b3⟩ | ⟨c', _⟩
    · exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
    · exact absurd c c'
  · rcases (facFits_iff x' g).1 h' with ⟨c', _⟩ | ⟨_, b1, b2, b3⟩
    · exact absurd c' c
    · exact ⟨a2.trans b2.symm, a3.trans b3.symm, a1.trans b1.symm⟩

theorem facs_pin : ∀ (gs : List WsGrp) (l l' : List WsFac), l.length = gs.length →
    l'.length = gs.length → (∀ y ∈ l.zip gs, facFits y.1 y.2 = true) →
    (∀ y ∈ l'.zip gs, facFits y.1 y.2 = true) → All2 FacAlike l l'
  | [], [], [], _, _, _, _ => .nil
  | [], _ :: _, _, h, _, _, _ => by simp at h
  | [], [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp at h
  | g :: gs, x :: l, x' :: l', h1, h2, a1, a2 =>
    .cons (fac_pin (a1 (x, g) (by simp)) (a2 (x', g) (by simp)))
      (facs_pin gs l l' (by simpa using h1) (by simpa using h2)
        (fun y hy => a1 y (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hy))
        (fun y hy => a2 y (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hy)))

/-- Two claims on one unit that both pass the merge's test on sizes are alike. -/
theorem shape_pin (lay : WsLay) {c c' : WsClaim} (hu : c.ui = c'.ui)
    (h : (wsClaimShape lay c).isOk = true) (h' : (wsClaimShape lay c').isOk = true) :
    ClaimAlike c c' := by
  rw [← claimFits_eq] at h h'
  obtain ⟨u, e, n, a⟩ := (claimFits_iff lay c).1 h
  obtain ⟨u', e', n', a'⟩ := (claimFits_iff lay c').1 h'
  rw [hu, e'] at e
  obtain rfl := Option.some.inj e
  exact ⟨hu, facs_pin _ _ _ n n' a a'⟩

/-- What is left of two claims that are alike: one unit, factors of the same sizes. -/
theorem rowPart_sizes (lay : WsLay) {c c' : WsClaim} (h : ClaimAlike c c') (ka ka' : E) :
    RecSizes (wsRowPart lay c ka) (wsRowPart lay c' ka') :=
  ⟨(rowPart_alike lay h ka ka').1,
    OnBytes.Flat.All2.imp (fun _ _ q => q) (rowPart_alike lay h ka ka').2⟩

/-! ## Lists, member by member -/

theorem mapM_both {α β : Type} {R : β → β → Prop} {f f' : α → Option β}
    (h : ∀ a b b', f a = some b → f' a = some b' → R b b') :
    ∀ (l : List α) (r r' : List β), l.mapM f = some r → l.mapM f' = some r' → All2 R r r'
  | [], r, r', h1, h2 => by
    rw [List.mapM_nil] at h1 h2
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    exact .nil
  | a :: l, r, r', h1, h2 => by
    rw [List.mapM_cons] at h1 h2
    obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨bs, hbs, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨b', hb', h2⟩ := Option.bind_eq_some_iff.1 h2
    obtain ⟨bs', hbs', h2⟩ := Option.bind_eq_some_iff.1 h2
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    exact .cons (h a b b' hb hb') (mapM_both h l bs bs' hbs hbs')

theorem all2_flatten {β : Type} {R : β → β → Prop} {L L' : List (List β)}
    (h : All2 (All2 R) L L') : All2 R L.flatten L'.flatten := by
  induction h with
  | nil => exact .nil
  | cons h0 _ ih =>
    rw [List.flatten_cons, List.flatten_cons]
    exact h0.append ih

/-- A relation made stronger by what holds of all members of the two lists. -/
theorem all2_with {β : Type} {R R' : β → β → Prop} {p : β → Prop}
    (h : ∀ a b, R a b → p a → p b → R' a b) {l l' : List β} (hl : All2 R l l') :
    (∀ a ∈ l, p a) → (∀ b ∈ l', p b) → All2 R' l l' := by
  induction hl with
  | nil => exact fun _ _ => .nil
  | cons h0 _ ih =>
    exact fun a1 a2 => .cons (h _ _ h0 (a1 _ List.mem_cons_self) (a2 _ List.mem_cons_self))
      (ih (fun a ha => a1 a (List.mem_cons_of_mem _ ha))
        (fun b hb => a2 b (List.mem_cons_of_mem _ hb)))

/-- Two lists in R, each paired with a list of its own, the two as long, and mapped. -/
theorem all2_zip_map2 {α γ δ : Type} {R : α → α → Prop} {S : δ → δ → Prop} {f f' : α × γ → δ}
    (h : ∀ a b x y, R a b → S (f (a, x)) (f' (b, y))) {l l' : List α} (hl : All2 R l l') :
    ∀ r r' : List γ, r.length = r'.length → All2 S ((l.zip r).map f) ((l'.zip r').map f') := by
  induction hl with
  | nil =>
    intro r r' _
    rw [List.zip_nil_left, List.zip_nil_left]
    exact .nil
  | cons h0 _ ih =>
    intro r r' hr
    cases r with
    | nil =>
      cases r' with
      | nil =>
        rw [List.zip_nil_right, List.zip_nil_right]
        exact .nil
      | cons _ _ => simp at hr
    | cons x r =>
      cases r' with
      | nil => simp at hr
      | cons y r' =>
        rw [List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.map_cons]
        exact .cons (h _ _ x y h0) (ih r r' (by simpa using hr))

/-! ## The units: the walk -/

/-- Two environments of claims of one layout, one group and one layout of the weights. -/
structure EnvPub (c c₀ : ClaimEnv) : Prop where
  y : c.v.y = c₀.v.y
  g : c.v.g = c₀.v.g
  lay : c.wsLay = c₀.wsLay

/-- The relation of the walk: one unit. -/
abbrev OneUnit (a b : WsClaim) : Prop := a.ui = b.ui

theorem claim_ui {c : ClaimEnv} {X lam : Nat} {fac : WsGrp → Option WsFac} {a : WsClaim}
    (h : c.claim X lam fac = some a) : c.wsLay.unitOf X (c.v.lay lam) = some a.ui := by
  unfold ClaimEnv.claim at h
  obtain ⟨ui, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨f, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact h1

variable {c c₀ : ClaimEnv}

theorem claim_both (E : EnvPub c c₀) {X lam : Nat} {fac fac₀ : WsGrp → Option WsFac}
    {a b : WsClaim} (h : c.claim X lam fac = some a) (h₀ : c₀.claim X lam fac₀ = some b) :
    OneUnit a b := by
  have e1 := claim_ui h
  have e2 := claim_ui h₀
  have el : c.v.lay lam = c₀.v.lay lam := by
    unfold Env.lay
    rw [E.y, E.g]
  rw [E.lay, el] at e1
  exact Option.some.inj (e1.symm.trans e2)

theorem claimsA_both (E : EnvPub c c₀) (sn : String) {l l₀ : List WsClaim}
    (h : c.claimsA sn = some l) (h₀ : c₀.claimsA sn = some l₀) : All2 OneUnit l l₀ := by
  have hm : ∀ lam, c.v.isMoe lam = c₀.v.isMoe lam := fun lam => by
    unfold Env.isMoe
    rw [E.y]
  unfold ClaimEnv.claimsA at h h₀
  dsimp only at h h₀
  by_cases ha : (!isAcc sn) = true
  · rw [if_pos ha] at h h₀
    obtain rfl := Option.some.inj h
    obtain rfl := Option.some.inj h₀
    exact .nil
  · rw [if_neg ha] at h h₀
    rw [E.y] at h
    simp only [hm] at h
    exact mapM_both (fun _ _ _ h1 h2 => claim_both E h1 h2) _ _ _ h h₀

theorem claimsT_both (E : EnvPub c c₀) (sn : String) {l l₀ : List WsClaim}
    (h : c.claimsT sn = some l) (h₀ : c₀.claimsT sn = some l₀) : All2 OneUnit l l₀ := by
  unfold ClaimEnv.claimsT at h h₀
  dsimp only at h h₀
  rw [E.y] at h
  by_cases h1 : (sn == "QK") = true
  · rw [if_pos h1] at h h₀
    obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨x₀, _, h₀⟩ := Option.bind_eq_some_iff.1 h₀
    exact mapM_both (fun _ _ _ k1 k2 => claim_both E k1 k2) _ _ _ h h₀
  · rw [if_neg h1] at h h₀
    by_cases h2 : (c₀.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true
    · rw [if_pos h2] at h h₀
      exact mapM_both (fun _ _ _ k1 k2 => claim_both E k1 k2) _ _ _ h h₀
    · rw [if_neg h2] at h h₀
      obtain rfl := Option.some.inj h
      obtain rfl := Option.some.inj h₀
      exact .nil

theorem weightClaims_both (E : EnvPub c c₀) (TS : List Nat) {l l₀ : List WsClaim}
    (h : c.weightClaims TS = some l) (h₀ : c₀.weightClaims TS = some l₀) : All2 OneUnit l l₀ := by
  unfold ClaimEnv.weightClaims at h h₀
  dsimp only at h h₀
  rw [E.y] at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a₀, ha₀, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨t₀, ht₀, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain rfl := Option.some.inj h
  obtain rfl := Option.some.inj h₀
  exact (all2_flatten (mapM_both (fun sn _ _ k1 k2 => claimsA_both E sn k1 k2) _ _ _ ha ha₀)).append
    (all2_flatten (mapM_both (fun sn _ _ k1 k2 => claimsT_both E sn k1 k2) _ _ _ ht ht₀))

theorem claimE_ui {c : ClaimEnv} {ZE tkh : Array E} {V : Nat} {tokv : Array Nat} {a : WsClaim}
    (h : c.claimE ZE tkh V tokv = some a) : c.wsLay.unitOf 12 c.v.y.h.L = some a.ui := by
  unfold ClaimEnv.claimE at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ui, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨f, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact h1

/-! ## At the hearing -/

/-- Where the merge returns, its test on the claims' sizes held. -/
theorem merge_shapes {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    ∀ x ∈ cl.toList, (wsClaimShape lay x).isOk = true := by
  unfold flatForkEnd at h
  obtain ⟨_, A1, a1, c1, k1⟩ := OnBytes.Desc.First.P1.bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := OnBytes.Desc.First.P1.must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := OnBytes.Desc.First.P1.bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := OnBytes.Desc.First.P1.must_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := OnBytes.Desc.First.P1.bind_some.mp k2
  obtain ⟨m3, rfl, rfl⟩ := OnBytes.Desc.First.P1.must_some.mp c3
  have m3' : (cl.toList.all fun x => (wsClaimShape lay x).isOk) = true := by
    rw [Array.all_toList]
    exact m3
  exact fun x hx => List.all_eq_true.1 m3' x hx

/-- The lists that two hearings hand to the merge name the same units in the same order. -/
theorem mergeClaims_both {P P₀ : Pub} {g : Nat} {o o₀ : Own} (hy : P.y = P₀.y)
    (hrd : P.rd = P₀.rd) (E : EnvPub (envOf P o) (envOf P₀ o₀)) {cl cl₀ : Array WsClaim}
    (h : mergeClaims P g o = some cl) (h₀ : mergeClaims P₀ g o₀ = some cl₀) :
    All2 OneUnit cl.toList cl₀.toList := by
  have eTS : callsTS P = callsTS P₀ := by
    unfold callsTS
    rw [hrd, hy]
  unfold mergeClaims at h h₀
  rw [eTS] at h
  obtain ⟨TS, hTS, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS₀, hTS₀, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain rfl := Option.some.inj (hTS.symm.trans hTS₀)
  obtain ⟨cp, hcp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cp₀, hcp₀, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨ce₀, hce₀, rfl⟩ := Option.map_eq_some_iff.1 h₀
  rw [List.toList_toArray, List.toList_toArray]
  refine (weightClaims_both E TS hcp hcp₀).append ?_
  by_cases hg : (g == 0) = true
  · rw [if_pos hg] at hce hce₀
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hce
    obtain ⟨x₀, hx₀, rfl⟩ := Option.map_eq_some_iff.1 hce₀
    have e1 := claimE_ui hx
    have e2 := claimE_ui hx₀
    rw [E.lay, E.y] at e1
    exact .cons (Option.some.inj (e1.symm.trans e2)) .nil
  · rw [if_neg hg] at hce hce₀
    obtain rfl := Option.some.inj hce
    obtain rfl := Option.some.inj hce₀
    exact .nil

/-- **The sentence HearRowSkel.** -/
theorem hear_row_skel : HearRowSkel := by
  intro P P₀ hp g fo fo₀ F G F₀ G₀ t u t₀ u₀ o o₀ hy hrd hl h h₀
  obtain ⟨_, ey, _, eg, _, _, cl, _, _, _, _, G5, _, _, _, _, u5, _, _, _, _, _, _, hc, hs, hE⟩ :=
    hear_parts h
  obtain ⟨_, ey₀, _, eg₀, _, _, cl₀, _, _, _, _, G5₀, _, _, _, _, u5₀, _, _, _, _, _, _, hc₀, hs₀,
    hE₀⟩ := hear_parts h₀
  have E : EnvPub (envOf P o) (envOf P₀ o₀) :=
    ⟨(ey.trans hy).trans ey₀.symm, eg.trans eg₀.symm, hl⟩
  have hU := mergeClaims_both hy hrd E hc hc₀
  have sh := merge_shapes hE
  have sh₀ := merge_shapes hE₀
  rw [← hl] at sh₀
  have hA : All2 ClaimAlike cl.toList cl₀.toList :=
    all2_with (p := fun x => (wsClaimShape P.wsLay x).isOk = true)
      (fun _ _ hu a b => shape_pin P.wsLay hu a b) hU sh sh₀
  obtain ⟨x, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ :=
    mergeHear_inv (hear_of_flat hE)
  obtain ⟨x₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr₀, _⟩ :=
    mergeHear_inv (hear_of_flat hE₀)
  have hsv : (mergeSlots hp g o).size = (mergeSlots hp g o₀).size := by
    unfold mergeSlots
    by_cases hg : (g == 0) = true
    · simp [hg]
    · simp [hg]
  refine ⟨?_, ?_⟩
  · rw [(OnBytes.Road.K4.wo_sizes h).2.2, (OnBytes.Road.K4.wo_sizes h₀).2.2, hl]
  · rw [hr, hr₀, Array.toList_zip, Array.toList_zip, ← hl]
    refine all2_zip_map2 (fun a b _ _ hab => ?_) hA _ _ ?_
    · exact rowPart_sizes P.wsLay hab _ _
    · rw [Array.length_toList, Array.length_toList, powers_size, powers_size, hsv]

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.fac_pin
#print axioms OnBytes.Desc.First.K4.Total.facs_pin
#print axioms OnBytes.Desc.First.K4.Total.shape_pin
#print axioms OnBytes.Desc.First.K4.Total.rowPart_sizes
#print axioms OnBytes.Desc.First.K4.Total.mapM_both
#print axioms OnBytes.Desc.First.K4.Total.all2_flatten
#print axioms OnBytes.Desc.First.K4.Total.all2_with
#print axioms OnBytes.Desc.First.K4.Total.all2_zip_map2
#print axioms OnBytes.Desc.First.K4.Total.claim_ui
#print axioms OnBytes.Desc.First.K4.Total.claim_both
#print axioms OnBytes.Desc.First.K4.Total.claimsA_both
#print axioms OnBytes.Desc.First.K4.Total.claimsT_both
#print axioms OnBytes.Desc.First.K4.Total.weightClaims_both
#print axioms OnBytes.Desc.First.K4.Total.claimE_ui
#print axioms OnBytes.Desc.First.K4.Total.merge_shapes
#print axioms OnBytes.Desc.First.K4.Total.mergeClaims_both
#print axioms OnBytes.Desc.First.K4.Total.hear_row_skel
