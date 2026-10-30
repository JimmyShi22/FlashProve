-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/PlainFree.lean: K9's LAWS AND COUNT AT EVERY SEGMENT WHOSE RUNS OF CLAIMS, BUT FOR
"K8.equations", ARE FREE OF THE BATCHING ELEMENT: over part 1's general walk (Johnson/Desc/K8/Honest/GathersPlain.lean:
`walk_one`, `pre_two`, `k8_two`, `post_two`, `drawnAt_re`, `gathers_of_plain`). Statements and proofs ON THE VERIFIER's
TEXT; no prover is in this file, and no goal is stated.

  `PlainTies L i pre post`   part 1's premises, as one structure: L's order is pre ++ [(i, "K8.equations")] ++ post;
                    each run at an entry of pre stands under a run that is free of chi (`PlainRun`), at
                    (i, "K8.equations") under the smallness test's own run, at an entry of post under a `PlainBehind`
  `merge_putFork`, `merge_putTl`, `merge_reBoth`   the merge's slot is read off neither the ledger nor the smallness
                    test's data
  `two_ends`        two yeses of the gatherer behind the draw at two challenges, from one state: the same claims in
                    front, the same first four of "K8.equations", the same length, the same claims behind (part 1's
                    `walk_two`, by its road), AND THE SAME MERGE's SLOT BEHIND
  `cut_plain`       so `Cut` (Honest/K9/CutLaw.lean) at the lists of ANY ONE yes
  `facts_plain`     the law `RunsLaw.ledger` and the two numbers, out of part 1's `Gathers` and K9's own `draw_facts`
  `data_of_yes`     where draw and gatherer return, the state in front holds the smallness test's data and a list of
      tables
  `runsLaw_plain`   **`RunsLaw`, AT EVERY STATE.** IT IS A LAW ON THE YESES OF DRAW AND GATHERER: where they never
                    return it holds idly
  `free_few_plain`  **THE COUNT**: where s is good (`goodS`): at most n * (the state's ledger's plan's number of
                    claims - 1) readings
WHAT IS NOT CLAIMED. `PlainTies` at any segment (out of the ties: Honest/K9/AtSeatAll.lean). That draw and gatherer
return at any state. "Good" is here the proposition `goodS`, WHICH HOLDS A YES OF DRAW AND GATHERER: the lists are
those of some yes, not written off the state in front (at a feed-forward segment they are: Honest/K9/LayersFree.lean):
no Bool on s. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.CutLaw
import Johnson.Desc.ProofFile.Honest.K9.BatYes
import Johnson.Desc.K8.Honest.GathersPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.K8.Honest (drawnAt PreOk PostOk walk_one drawnAt_re reChi reBoth reChiF post_two
  pre_two pre_one drawnAt_part k8_two behind_k8 gathers_of_plain Gathers reChi_fork reChi_tl reChi_funs)
open VerifiableInference.Desc.K9 (atS Where mergeOf batch)

/-- Part 1's premises on a segment's runs. -/
structure PlainTies (L : Link S Claim) (i : Nat) (pre post : List (Nat × String)) : Prop where
  order : L.order = pre ++ (i, "K8.equations") :: post
  pre : PreOk L pre
  post : PostOk L post
  eq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2

theorem merge_putFork (s : S) (G : Fork) : mergeOf (s.putFork G) = mergeOf s := by
  unfold mergeOf S.putFork
  cases h : s.here with
  | lay a => rfl
  | att a => rfl
  | head a =>
    by_cases ho : a.opened = true
    · simp only [ho, if_true]
    · have hf : a.opened = false := by simpa using ho
      simp only [hf, Bool.false_eq_true, if_false, h]
  | _ => simp only [h]

theorem merge_putTl (s : S) (tl : HTailF2) : mergeOf (s.putTl tl) = mergeOf s := by
  unfold mergeOf S.putTl
  cases h : s.here with
  | lay a => rfl
  | att a => rfl
  | head a =>
    by_cases ho : a.opened = true
    · simp only [ho, if_true]
    · have hf : a.opened = false := by simpa using ho
      simp only [hf, Bool.false_eq_true, if_false, h]
  | _ => simp only [h]

theorem merge_reBoth (θ : E) (tl : HTailF2) (s : S) : mergeOf (reBoth θ tl s) = mergeOf s := by
  unfold reBoth reChi
  rw [merge_putTl]
  cases s.fork? with
  | none => rfl
  | some F => exact merge_putFork s _

/-- **Two yeses behind the draw at two challenges.** After part 1's `walk_two`, by its road; with the merge's slot. -/
theorem two_ends (L : Link S Claim) (pre post : List (Nat × String)) (Hpre : PreOk L pre)
    (Hpost : PostOk L post) (θ : E) {t e e' : S} {cls cls' fr fr' k8 k8' bk bk' : List Claim}
    {e₁ e₂ e₁' e₂' : S} {F F₂ F' F₂' : Fork} {tl tl₁ tl' tl₁' : HTailF2} {funs funs' : Array HFun}
    (W : VerifiableInference.Desc.First.K8.Honest.Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl₁ funs)
    (W' : VerifiableInference.Desc.First.K8.Honest.Walk L pre post (reChi θ t) e' cls' fr' k8' bk' e₁' e₂' F' F₂'
      tl' tl₁' funs') :
    fr' = fr ∧ k8'.take 4 = k8.take 4 ∧ k8'.length = k8.length ∧ bk' = bk ∧ mergeOf e' = mergeOf e := by
  obtain ⟨c, c1, c2, c3⟩ := pre_two L pre Hpre ([], t) ([], reChi θ t) _ _ θ rfl rfl W.a1 W'.a1
  have hfr : fr = c := by simpa using c1
  have hfr' : fr' = c := by simpa using c2
  have hff : fr' = fr := hfr'.trans hfr.symm
  have he₁ : e₁' = reChi θ e₁ := c3
  have hF : F' = reChiF θ F := by
    have h := W'.a2
    rw [he₁, reChi_fork, W.a2] at h
    exact (Option.some.inj h).symm
  have htl : tl' = tl := by
    have h := W'.a3
    rw [he₁, reChi_tl, W.a3] at h
    exact (Option.some.inj h).symm
  have hfu : funs' = funs := by
    have h := W'.a4
    rw [he₁, reChi_funs, W.a4] at h
    exact (Option.some.inj h).symm
  have a5' := W'.a5
  rw [hF, htl, hfu] at a5'
  obtain ⟨k4, kl, hF2⟩ := k8_two θ W.a5 a5'
  have he₂ : e₂' = reBoth θ tl₁' e₂ := by
    rw [W'.a6, W.a6, he₁, hF2]
    exact behind_k8 θ e₁ tl₁ tl₁' F₂
  obtain ⟨b, b1, b2, b3⟩ := post_two L post Hpost (fr ++ k8, e₂) (fr' ++ k8', e₂') _ _ θ tl₁'
    (by simp [kl, hff]) he₂ W.a7 W'.a7
  have hb : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
  have hb' : bk' = b := List.append_cancel_left (W'.a8.symm.trans b2)
  have he : e' = reBoth θ tl₁' e := b3
  exact ⟨hff, k4, kl, hb'.trans hb.symm, by rw [he, merge_reBoth]⟩

/-- **`Cut` at the lists of any one yes.** -/
theorem cut_plain (L : Link S Claim) (i : Nat) (pre post : List (Nat × String)) (T : PlainTies L i pre post)
    (p : Where) (s : S) (x₀ : E) (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p (claimsInBy L.each L.hear L.order) s x₀ = some y₀) :
    ∃ FR k₀ BK : List Claim,
      Cut p (claimsInBy L.each L.hear L.order) s FR (k₀.take 4) k₀.length BK (mergeOf y₀.1) := by
  obtain ⟨t₀, hd₀, hg₀, _⟩ := gathered_split p _ s x₀ y₀ h₀
  obtain ⟨fr₀, k₀, bk₀, u₁, u₂, G, G₂, v, v', w, W₀⟩ :=
    walk_one L i pre post T.order T.post T.eq t₀ y₀.1 y₀.2.2 hg₀
  refine ⟨fr₀, k₀, bk₀, fun x y hy => ?_⟩
  obtain ⟨t, hd, hg, _⟩ := gathered_split p _ s x y hy
  obtain ⟨θ, rfl⟩ := drawnAt_re p s t₀ t _ _ hd₀ hd
  obtain ⟨fr, k8, bk, e₁, e₂, F, F₂, tl₁, tl', funs₁, W⟩ :=
    walk_one L i pre post T.order T.post T.eq _ y.1 y.2.2 hg
  obtain ⟨hfr, k4, kl, hbk, hm⟩ := two_ends L pre post T.pre T.post θ W₀ W
  exact ⟨k8, _, tl₁, tl', funs₁, F, F₂, by rw [W.a8, hfr, hbk], W.a5, k4, kl, hm⟩

/-- Where draw and gatherer return, the state in front holds the smallness test's data and a list of tables. After part
1's `funs_of_yes` (Johnson/Desc/K8/Honest/FallAtt.lean). -/
theorem data_of_yes (L : Link S Claim) (i : Nat) (pre post : List (Nat × String)) (T : PlainTies L i pre post)
    (p : Where) (s : S) (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (hy : gathered p (claimsInBy L.each L.hear L.order) s x = some y) :
    ∃ tl funs, s.tl? = some tl ∧ s.funs? = some funs := by
  obtain ⟨t, hd, hg, _⟩ := gathered_split p _ s x y hy
  obtain ⟨fr, k8, bk, e₁, e₂, F, F₂, tl₁, tl', funs₁, W⟩ :=
    walk_one L i pre post T.order T.post T.eq t y.1 y.2.2 hg
  obtain ⟨c, -, -, c3, c4, -⟩ := pre_one L pre T.pre _ _ W.a1
  obtain ⟨-, xt, xf⟩ := drawnAt_part p s t _ hd
  have h3 := W.a3
  have h4 := W.a4
  rw [c3, xt] at h3
  rw [c4, xf] at h4
  exact ⟨tl₁, funs₁, h3, h4⟩

/-- What stands behind draw and gatherer: out of part 1's `Gathers` and K9's own draw. -/
theorem facts_plain (p : Where) (g : S → Except String (List Claim × S)) (s : S) (tl : HTailF2)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E) (G : Gathers p g s tl funs nf nb a)
    (a0 : VerifiableInference.Desc.K9.Part) (ha0 : atS.get? s = some a0) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (hy : gathered p g s x = some y) :
    y.2.1.F.theta = x ∧ y.2.1.F.LS.size = y.2.1.F.ns ∧ (∀ j, y.2.1.F.LS.getD j zeroE = zeroE) ∧
      y.2.1.F.nClaim = 0 ∧ y.2.1.F.planClaimsF = a0.F.planClaimsF := by
  obtain ⟨t₁, hd, hg, he⟩ := gathered_split p g s x y hy
  obtain ⟨a₁, h1, f⟩ := draw_facts p s t₁ x a0 ha0 hd
  obtain ⟨X, Y, _, _, _, _, _, _, _, hX, hY, hcore, _⟩ := G.each (drawnOne x) t₁ y.1 y.2.2 hd hg
  obtain rfl : a₁ = X := Option.some.inj (h1.symm.trans hX)
  obtain rfl : y.2.1 = Y := Option.some.inj (he.symm.trans hY)
  have cT : y.2.1.F.theta = a₁.F.theta := congrArg (·.2.1) hcore
  have cL : y.2.1.F.LS = a₁.F.LS := congrArg (·.1.2.1) hcore
  have cN : y.2.1.F.ns = a₁.F.ns := congrArg (·.1.2.2.2) hcore
  have cC : y.2.1.F.nClaim = a₁.F.nClaim := congrArg (·.2.2.1) hcore
  have cP : y.2.1.F.planClaimsF = a₁.F.planClaimsF := congrArg (·.2.2.2) hcore
  exact ⟨by rw [cT, f.chi], by rw [cL, cN, f.sized], fun j => by rw [cL]; exact f.empty j,
    by rw [cC, f.count], by rw [cP, f.plan]⟩

/-- **`RunsLaw` at a segment whose runs, but for "K8.equations", are free of chi.** -/
theorem runsLaw_plain (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (T : PlainTies L i pre post) (p : Where) (s : S) :
    RunsLaw p (claimsInBy L.each L.hear L.order) s := by
  refine ⟨fun x y hy => ?_, fun x x' y y' hy hy' => ?_⟩
  · obtain ⟨tl, funs, ht, hf⟩ := data_of_yes L i pre post T p s x y hy
    obtain ⟨nf, nb, a, G⟩ := gathers_of_plain L p i pre post T.order T.pre T.post T.eq s tl funs ht hf
    obtain ⟨t₁, hd, _, _⟩ := gathered_split p _ s x y hy
    obtain ⟨a0, ha0⟩ := draw_open p s t₁ x hd
    obtain ⟨f1, f2, f3, _, _⟩ := facts_plain p _ s tl funs nf nb a G a0 ha0 x y hy
    exact ⟨f1, f2, f3⟩
  · obtain ⟨tl, funs, ht, hf⟩ := data_of_yes L i pre post T p s x y hy
    obtain ⟨nf, nb, a, G⟩ := gathers_of_plain L p i pre post T.order T.pre T.post T.eq s tl funs ht hf
    obtain ⟨t₁, hd, _, _⟩ := gathered_split p _ s x y hy
    obtain ⟨a0, ha0⟩ := draw_open p s t₁ x hd
    obtain ⟨_, _, _, f4, f5⟩ := facts_plain p _ s tl funs nf nb a G a0 ha0 x y hy
    obtain ⟨_, _, _, f4', f5'⟩ := facts_plain p _ s tl funs nf nb a G a0 ha0 x' y' hy'
    obtain ⟨FR, k₀, BK, cut⟩ := cut_plain L i pre post T p s x y hy
    obtain ⟨k, m⟩ := keysSame_of_cut p _ s _ _ _ _ _ cut x x' y y' hy hy'
    exact ⟨k, by rw [f5, f5'], by rw [f4, f4'], m⟩

/-- **The count.** a0: K9's part of the state in front. -/
theorem free_few_plain {Cl : Type} (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (T : PlainTies L i pre post) (p : Where) (s : S) (a0 : VerifiableInference.Desc.K9.Part)
    (ha0 : atS.get? s = some a0) (n : Nat) (hg : goodS p (claimsInBy L.each L.hear L.order) s n)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t →
      (batch atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t) :
    Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧ FallsAt b' s n k4 x) ≤
      n * (a0.F.planClaimsF - 1) := by
  have hg' := hg
  obtain ⟨x₀, y₀, h₀, _⟩ := hg'
  obtain ⟨tl, funs, ht, hf⟩ := data_of_yes L i pre post T p s x₀ y₀ h₀
  obtain ⟨nf, nb, a, G⟩ := gathers_of_plain L p i pre post T.order T.pre T.post T.eq s tl funs ht hf
  exact quiet_few_good p _ s (runsLaw_plain L i pre post T p s) n hg _
    (fun x y hy => (facts_plain p _ s tl funs nf nb a G a0 ha0 x y hy).2.2.2.2) k4 hk b' hb'

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.merge_reBoth
#print axioms ProofFile.Honest.K9.two_ends
#print axioms ProofFile.Honest.K9.cut_plain
#print axioms ProofFile.Honest.K9.data_of_yes
#print axioms ProofFile.Honest.K9.facts_plain
#print axioms ProofFile.Honest.K9.runsLaw_plain
#print axioms ProofFile.Honest.K9.free_few_plain
#print axioms ProofFile.Honest.K9.PlainTies
#print axioms ProofFile.Honest.K9.merge_putFork
#print axioms ProofFile.Honest.K9.merge_putTl
