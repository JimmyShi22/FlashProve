-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LayersFree.lean: K9's "free-slot" TEST AT A FEED-FORWARD SEGMENT: K9's COUNT
(Honest/K9/CutLaw.lean: `free_few_cut`) OVER PART 1's WALK THROUGH THE SEGMENT's SEVEN RUNS
(Johnson/Desc/K8/Honest/FallLayersLaw.lean: `layers_walk`; FallLayersLists.lean: `layers_lists`). Statements and
proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `ListsAt L p4 p s a₀`, `lists_of_walk`   what part 1's `layers_lists` says, as one proposition; PAID BY ONE CALL OF
                    IT, under the walk's premises: from one yes of draw and gatherer: the four things heard are there;
                    the list is layersFront ++ k8 ++ layersBack; k8's first four are four8; the merge's slot is the
                    one in front; k8 is an answer of "K8.equations" at the smallness test's data and the list of
                    tables in front, at SOME number and SOME ledger
  `Walk`            the walk's own premises, as one structure: which run stands at which entry of the order
                    (`LayersTies` and the two on "objects"), the order, and that s stands in a feed-forward segment
  `cut_layers`      so `Cut` (Honest/K9/CutLaw.lean), at lists written off the state in front of the draw
  `behind_layers_facts`   the law `RunsLaw.ledger`, and the two numbers: out of `layers_walk`'s "the runs have left the
                    ledger's sums, chi, the count and the plan's number" and K9's own `draw_facts`
  `runsLaw_layers`  **`RunsLaw` AT A FEED-FORWARD SEGMENT**
  `GoodLayers`      **"GOOD", ON DATA IN FRONT OF THE DRAW**: whatever four things heard the state holds, the Bool
                    `goodCut` is true at the lists written off them. A proposition over a Bool; `goodLayersB`: A BOOL
                    WITH CODE for it (true where one of the four lacks); `goodLayers_of_B`: its yes gives it: ONE WAY
                    alone is typed; no `#guard` runs it
  `goodS_layers`    so "s is good" (`goodS`), where draw and gatherer return somewhere
  `free_few_layers`, `free_few_layers_canon`   **THE COUNT**, in readings and on machine words below the prime: at most
                    n * (the state's ledger's plan's number of claims - 1) values of chi at which a member that only
                    refuses more than K9's batching says yes and K9's "free-slot" at n slots, or with it K4's CONDITION
                    at the same n and the same state, speaks behind it. WITH NO PREMISE THAT THE FOUR THINGS WERE
                    HEARD: where one is missing, draw and gatherer never return, and nothing is counted

WHAT IS NOT CLAIMED. `Walk`: the walk's premises: they are paid, and the theorems here called, wherever the proof file's
description can be opened in the goals' scope: Honest/K9/AtSeat.lean. `RunsLaw` IS A LAW ON THE YESES OF DRAW AND
GATHERER: that they return at any state is not shown. NO MEMBER IS SHOWN of `Heard4` or, but idly, of `GoodLayers`
(where nothing was heard it holds idly, and nothing is counted). That `GoodLayers` is true at a state of a run. That n
is the plan's number of filled slots, or that the state's plan's number is the public parameters'. OF K4's OWN
"free-slot": that its number is K9's is shown nowhere, and its run is asked behind another run, at a later state.
Attention and the head. No probability. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.CutLaw
import Johnson.Desc.ProofFile.Honest.K9.BatYes
import Johnson.Desc.K8.Honest.FallLayersLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.K8.Honest (drawnAt layersFront layersBack layers_walk layers_lists GatherBody
  k8_cut lay_fork)
open VerifiableInference.Desc.K9 (atS Where mergeOf batch)

/-- **What `layers_lists` says**, as one proposition. -/
def ListsAt (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (p : Where) (s : S) (a₀ : LayOwn) : Prop :=
  ∀ (d : Fmt.Drawn) (t e : S) (cls : List Claim), drawnAt p s d = .ok t →
    claimsInBy L.each L.hear L.order t = .ok (cls, e) →
    ∃ (gC gD : Forest.Heard) (o : Layer.Own) (lf : List Aff) (k8 : List Claim),
      a₀.lookHeard = some gC ∧ a₀.tl.heard = some gD ∧ a₀.own = some o ∧
      K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some lf ∧
      cls = layersFront gC gD lf ++ k8 ++ layersBack o ∧ k8.take 4 = K9L.four8 a₀.tl gD ∧
      mergeOf e = mergeOf s ∧
      ∃ (n₀ : Nat) (F₁ F₂ : Fork) (tl' : HTailF2), equations n₀ a₀.tl o.funs F₁ = .ok (tl', F₂, k8)

/-- The walk's own premises. -/
structure Walk (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (s : S) (a₀ : LayOwn) :
    Prop where
  ties : LinkJoin.LayersTies L p4 nU
  calls : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsCalls
  digits : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsDigits
  order : L.order = VerifiableInference.Desc.First.orderOf .layers
  here : s.here = .lay a₀

/-- **`ListsAt`, PAID**: by one call of part 1's `layers_lists`, under the walk's own premises. -/
theorem lists_of_walk (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where) (s : S)
    (a₀ : LayOwn) (w : Walk L p4 nU s a₀) : ListsAt L p4 p s a₀ :=
  fun d t e cls hdr hg =>
    layers_lists L p4 nU p s a₀ w.ties w.calls w.digits w.order w.here d t e cls hdr hg

/-- The four things heard, at a state in a feed-forward segment. -/
structure Heard4 (p4 : OnBytes.Desc.First.K4.Par) (a₀ : LayOwn) (gC gD : Forest.Heard) (o : Layer.Own)
    (lf : List Aff) : Prop where
  calls : a₀.lookHeard = some gC
  digits : a₀.tl.heard = some gD
  own : a₀.own = some o
  front : K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some lf

/-- **`Cut` at a feed-forward segment.** -/
theorem cut_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (p : Where) (s : S) (a₀ : LayOwn)
    (lists : ListsAt L p4 p s a₀) (gC gD : Forest.Heard) (o : Layer.Own) (lf : List Aff)
    (hh : Heard4 p4 a₀ gC gD o lf) :
    Cut p (claimsInBy L.each L.hear L.order) s (layersFront gC gD lf) (K9L.four8 a₀.tl gD)
      (k8Len a₀.tl o.funs) (layersBack o) (mergeOf s) := by
  intro x y hy
  obtain ⟨t₁, hd, hg, _⟩ := gathered_split p _ s x y hy
  obtain ⟨gC', gD', o', lf', k8, hC', hD', ho', hf', e, h4, hm, n₀, F₁, F₂, tl', he⟩ :=
    lists (drawnOne x) t₁ y.1 y.2.2 hd hg
  obtain rfl : gC = gC' := Option.some.inj (hh.calls.symm.trans hC')
  obtain rfl : gD = gD' := Option.some.inj (hh.digits.symm.trans hD')
  obtain rfl : o = o' := Option.some.inj (hh.own.symm.trans ho')
  obtain rfl : lf = lf' := Option.some.inj (hh.front.symm.trans hf')
  obtain ⟨_, _, _, _, _, hlen, _⟩ := k8_cut he
  exact ⟨k8, n₀, a₀.tl, tl', o.funs, F₁, F₂, e, he, h4, hlen, hm⟩

/-- Where draw and gatherer return, the four things were heard. -/
theorem heard_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (p : Where) (s : S) (a₀ : LayOwn)
    (lists : ListsAt L p4 p s a₀) (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (hy : gathered p (claimsInBy L.each L.hear L.order) s x = some y) :
    ∃ gC gD o lf, Heard4 p4 a₀ gC gD o lf := by
  obtain ⟨t₁, hd, hg, _⟩ := gathered_split p _ s x y hy
  obtain ⟨gC, gD, o, lf, _, hC, hD, ho, hf, _⟩ := lists (drawnOne x) t₁ y.1 y.2.2 hd hg
  exact ⟨gC, gD, o, lf, hC, hD, ho, hf⟩

/-- What stands behind draw and gatherer at a feed-forward segment: out of the walk and K9's own draw. -/
theorem behind_layers_facts (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where)
    (s : S) (a₀ : LayOwn) (w : Walk L p4 nU s a₀) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (hy : gathered p (claimsInBy L.each L.hear L.order) s x = some y) :
    y.2.1.F.theta = x ∧ y.2.1.F.LS.size = y.2.1.F.ns ∧ (∀ j, y.2.1.F.LS.getD j zeroE = zeroE) ∧
      y.2.1.F.nClaim = 0 ∧ y.2.1.F.planClaimsF = a₀.F.planClaimsF := by
  obtain ⟨t₁, hd, hg, he⟩ := gathered_split p _ s x y hy
  obtain ⟨a, ha⟩ := draw_open p s t₁ x hd
  obtain ⟨a₁, h1, f⟩ := draw_facts p s t₁ x a ha hd
  have hFa : a.F = a₀.F :=
    Option.some.inj ((VerifiableInference.Desc.K9.get_fork s a ha).symm.trans (lay_fork s a₀ w.here))
  obtain ⟨_, _, _, _, _, _, _, _, X, Y, _, _, _, _, _, _, _, hX, hY, hcore, _⟩ :=
    layers_walk L p4 nU p s a₀ w.ties w.calls w.digits w.order w.here (drawnOne x) t₁ y.1 y.2.2 hd hg
  obtain rfl : a₁ = X := Option.some.inj (h1.symm.trans hX)
  obtain rfl : y.2.1 = Y := Option.some.inj (he.symm.trans hY)
  have cT : y.2.1.F.theta = a₁.F.theta := congrArg (·.2.1) hcore
  have cL : y.2.1.F.LS = a₁.F.LS := congrArg (·.1.2.1) hcore
  have cN : y.2.1.F.ns = a₁.F.ns := congrArg (·.1.2.2.2) hcore
  have cC : y.2.1.F.nClaim = a₁.F.nClaim := congrArg (·.2.2.1) hcore
  have cP : y.2.1.F.planClaimsF = a₁.F.planClaimsF := congrArg (·.2.2.2) hcore
  exact ⟨by rw [cT, f.chi], by rw [cL, cN, f.sized], fun j => by rw [cL]; exact f.empty j,
    by rw [cC, f.count], by rw [cP, f.plan, hFa]⟩

/-- **`RunsLaw` at a feed-forward segment.** -/
theorem runsLaw_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where)
    (s : S) (a₀ : LayOwn) (w : Walk L p4 nU s a₀) :
    RunsLaw p (claimsInBy L.each L.hear L.order) s := by
  have lists := lists_of_walk L p4 nU p s a₀ w
  have facts := behind_layers_facts L p4 nU p s a₀ w
  refine ⟨fun x y hy => ?_, fun x x' y y' hy hy' => ?_⟩
  · obtain ⟨f1, f2, f3, _, _⟩ := facts x y hy
    exact ⟨f1, f2, f3⟩
  · obtain ⟨gC, gD, o, lf, hh⟩ := heard_layers L p4 p s a₀ lists x y hy
    obtain ⟨_, _, _, f4, f5⟩ := facts x y hy
    obtain ⟨_, _, _, f4', f5'⟩ := facts x' y' hy'
    obtain ⟨k, m⟩ := keysSame_of_cut p _ s _ _ _ _ _ (cut_layers L p4 p s a₀ lists gC gD o lf hh)
      x x' y y' hy hy'
    exact ⟨k, by rw [f5, f5'], by rw [f4, f4'], m⟩

/-- **"Good", on data in front of the draw.** -/
def GoodLayers (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) : Prop :=
  ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf →
    goodCut n (mergeOf s) (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs) (layersBack o)
      a₀.F.planClaimsF = true

/-- **The same as a Bool with code**: the four things are read off the state; where one lacks, true. -/
def goodLayersB (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) : Bool :=
  match a₀.lookHeard, a₀.tl.heard, a₀.own with
  | some gC, some gD, some o =>
    match K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F with
    | some lf => goodCut n (mergeOf s) (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs)
        (layersBack o) a₀.F.planClaimsF
    | none => true
  | _, _, _ => true

theorem goodLayers_of_B (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    (h : goodLayersB p4 s a₀ n = true) : GoodLayers p4 s a₀ n := by
  intro gC gD o lf H
  unfold goodLayersB at h
  rw [H.calls, H.digits, H.own] at h
  simp only [H.front] at h
  exact h

/-- "s is good", where draw and gatherer return somewhere. -/
theorem goodS_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where)
    (s : S) (a₀ : LayOwn) (w : Walk L p4 nU s a₀) (n : Nat)
    (good : GoodLayers p4 s a₀ n) (x₀ : E) (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p (claimsInBy L.each L.hear L.order) s x₀ = some y₀) :
    goodS p (claimsInBy L.each L.hear L.order) s n := by
  have lists := lists_of_walk L p4 nU p s a₀ w
  obtain ⟨gC, gD, o, lf, hh⟩ := heard_layers L p4 p s a₀ lists x₀ y₀ h₀
  exact goodS_of_cut p _ s _ _ _ _ _ (cut_layers L p4 p s a₀ lists gC gD o lf hh) n a₀.F.planClaimsF
    (fun x y hy => (behind_layers_facts L p4 nU p s a₀ w x y hy).2.2.2) (good gC gD o lf hh) x₀ y₀ h₀

/-- **The count at a feed-forward segment**, in readings. -/
theorem free_few_layers {Cl : Type} (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : Where) (s : S) (a₀ : LayOwn) (w : Walk L p4 nU s a₀) (n : Nat)
    (good : GoodLayers p4 s a₀ n) (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t →
      (batch atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t) :
    Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧ FallsAt b' s n k4 x) ≤
      n * (a₀.F.planClaimsF - 1) := by
  by_cases hyes : ∃ x₀ y₀, gathered p (claimsInBy L.each L.hear L.order) s x₀ = some y₀
  · obtain ⟨x₀, y₀, h₀⟩ := hyes
    exact quiet_few_good p _ s (runsLaw_layers L p4 nU p s a₀ w) n
      (goodS_layers L p4 nU p s a₀ w n good x₀ y₀ h₀) _
      (fun x y hy => (behind_layers_facts L p4 nU p s a₀ w x y hy).2.2.2.2) k4 hk b' hb'
  · have hn : ∀ x, gathered p (claimsInBy L.each L.hear L.order) s x = none := by
      intro x
      cases hq : gathered p (claimsInBy L.each L.hear L.order) s x with
      | none => rfl
      | some y => exact absurd ⟨x, y, hq⟩ hyes
    rw [Prob.cnt_false fun z hz => by
      obtain ⟨x, _, hx⟩ := hz
      exact quiet_none p _ s hn n k4 b' hb' x hx]
    exact Nat.zero_le _

/-- **The count at a feed-forward segment**, on machine words below the prime. -/
theorem free_few_layers_canon {Cl : Type} (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par)
    (nU : Array Nat) (p : Where) (s : S) (a₀ : LayOwn) (w : Walk L p4 nU s a₀)
    (n : Nat) (good : GoodLayers p4 s a₀ n) (k4 : Option Nat)
    (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t →
      (batch atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (T : Finset E) (hT : ∀ x ∈ T, okE x = true) :
    Nat.card {x : E // x ∈ T ∧ FallsAt b' s n k4 x} ≤ n * (a₀.F.planClaimsF - 1) := by
  refine le_trans ?_ (free_few_layers L p4 nU p s a₀ w n good k4 hk b' hb')
  apply Nat.card_le_card_of_injective
    (fun c : {x : E // x ∈ T ∧ FallsAt b' s n k4 x} =>
      (⟨Reading.gl.val c.1, c.1, rfl, c.2.2⟩ :
        {y : Cb.Gl.E // ∃ x : E, Reading.gl.val x = y ∧ FallsAt b' s n k4 x}))
  intro a b hab
  have h1 : Reading.gl.val a.1 = Reading.gl.val b.1 := congrArg Subtype.val hab
  exact Subtype.ext (VerifiableInference.Desc.K9L.gl_injOn (hT a.1 a.2.1) (hT b.1 b.2.1) h1)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodLayers_of_B
#print axioms ProofFile.Honest.K9.lists_of_walk
#print axioms ProofFile.Honest.K9.cut_layers
#print axioms ProofFile.Honest.K9.heard_layers
#print axioms ProofFile.Honest.K9.behind_layers_facts
#print axioms ProofFile.Honest.K9.runsLaw_layers
#print axioms ProofFile.Honest.K9.goodS_layers
#print axioms ProofFile.Honest.K9.free_few_layers
#print axioms ProofFile.Honest.K9.free_few_layers_canon
#print axioms ProofFile.Honest.K9.ListsAt
#print axioms ProofFile.Honest.K9.Walk
#print axioms ProofFile.Honest.K9.Heard4
#print axioms ProofFile.Honest.K9.GoodLayers
#print axioms ProofFile.Honest.K9.goodLayersB
