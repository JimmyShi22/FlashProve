-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TripsWhole.lean: CONDITIONAL.

What is here. THE HYPOTHESIS `TripsAt` (TermsTrips.lean) ON THE PRODUCTS OF THE SECOND TOKEN
SUMCHECK's SUMMAND, FROM THE HYPOTHESIS `Kinds` (TripsOf.lean) ON WHAT THE FACTORS ARE MADE OF AND
FROM ONE PUBLIC TEST. The honest side's list of panels is the verifier's (`Sides.panels`,
Johnson/Desc/K4/Honest/Sides.lean): by PanelsShown.lean it is one list with open places. Its panels
of the second pass give the products, panel by panel (TripsOf.lean), laid end to end
(TripsKit.lean). Statements and proofs; two definitions with code (`triPlainB`, `ixAll`), and the
test's trials with three tools of their own (`toyS`, `looked`, `bent`).

THE PUBLIC TEST `triPlainB`: every panel of the second pass whose rows carry the selector has a
weight claim whose table counts extent 0 for the group "cd" (a unit that lacks the group counts so),
the one group that `Sides.weights` sums out under the rotation factor, which moves with the token
point; a panel without a claim, or whose claim's number lies beyond the tables, passes; WHERE THE
LIST OF PANELS IS NOT MADE AT THE EMPTY LIST OF SHOWN VALUES THE TEST ANSWERS TRUE. IT IS A
HYPOTHESIS OF STATEMENTS ON WHAT THE TERMS' FORM IS WORTH; WHERE IT IS FALSE NOTHING IS SAID. No
test of the verifier or of the honest parts asks it. That it is true at a layout of the weights that
`wsLayOf` returns FOR A MODEL WITH MIXTURES OF EXPERTS (its switch true: hws), where `Sides.of`
returns, is TermsPubOf.lean's `triPlainB_of_lay` (a later file; not called here); at the other
switch no theorem says it. The reading that stood here before that theorem (not by Lean; read
once): the verifier lays the rotation factor at the queries' and keys' call alone (`panelT`,
`claimsT`: OnBytes/Model/LayerPanels.lean); the layout's maker gives the group "cd" to units of kind
0 alone (`addLayer`, OnBytes/Model/Weights.lean), and a panel with the selector has a claim of kind
7, 8 or 10, the panels' and the claims' counts agreeing arm by arm. The trials at the end: true at
the small plan, both groups; false, at both groups, where each claim's table is given such a group;
false where one table alone is, that of the first panel that the test looks at; still true where all
tables but those that the test looks at are.

  `panels_all`   the honest side's list of panels is one list with open places
  `triPlainB`, `triPlain_at`   **the public test**; what it says of that list
  `ixAll`, `trips_open`, `trips_lin`   all products, at the point and at the corners
  `tripsAt_of`   **`TripsAt`**

Limits. At the reading `Reading.gl`. `Kinds` IS A HYPOTHESIS. Beside it and the test: the tokens'
rows are made; there are 2 ^ lt tokens; the reads at the point are made; THE PRODUCTS AT THE POINT
ARE MADE AT ALL VALUES IN THE PLACE OF THE SHOWN FACTORS (Law/AtEnds.lean has the like for the
summand); a table whose claim counts extent 0 for the group "cd" is the same words at all weights on
the tokens (hpl: Johnson/Road/K4/C/TokTables.lean has it). No example of the premises together is
known at the full size. From `TermsPub` and the tokens' rows the premises of `tripsAt_at` follow by
a theorem (TermsAll.lean's `terms_tripsAt`).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TripsOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTrips
import Johnson.Road.K4.C.TermsOpen
import Johnson.Desc.K4.Honest.SidesToyKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff eqTab)
open OnBytes.Model.Layer (SBlk PanelEnv panelsA panelsT placePanels stubO)
open OnBytes.Road (pt)
open OnBytes.Road.K4.C (tokenRows_trips tokenRows_size)
open OnBytes.Desc.First.K4.Honest

/-! ## 1 The list of panels -/

/-- **The honest side's list of panels is one list with open places**, or none at all lists of shown
values. -/
theorem panels_all (S : Sides) :
    ∃ r : Option (List SymBlk × ℕ), ∀ e : Array E,
      S.panels e = r.map fun x => ((x.1.map (·.at e)).toArray, x.2) := by
  obtain ⟨r, hr⟩ := panels_sym
    { v := S.v, e := S.fo.e, shownT := #[], zt := S.zt, stubO := stubO S.v.y } S.TS
  have hr' : ∀ e : Array E,
      panelsT { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } S.TS
        (panelsA { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } {}) =
        r.map (·.at e) := hr
  have hp0 : ∀ e : Array E, S.panels e =
      (panelsT { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } S.TS
        (panelsA { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } {})).bind
        fun pans => if pans.nextV = S.opens.size then some (placePanels pans.bl) else none := by
    intro e
    unfold Sides.panels
    dsimp only
    cases panelsT { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } S.TS
        (panelsA { v := S.v, e := S.fo.e, shownT := e, zt := S.zt, stubO := stubO S.v.y } {}) with
    | none => rfl
    | some pans => simp
  cases r with
  | none =>
    refine ⟨none, fun e => ?_⟩
    rw [hp0 e, hr' e]
    rfl
  | some D =>
    by_cases hn : D.2 = S.opens.size
    · obtain ⟨D', n, hp⟩ := place_sym D.1
      refine ⟨some (D', n), fun e => ?_⟩
      have hn' : (SymP.at D e).nextV = S.opens.size := hn
      rw [hp0 e, hr' e]
      show (if (SymP.at D e).nextV = S.opens.size then some (placePanels (SymP.at D e).bl)
        else none) = some _
      rw [if_pos hn']
      exact congrArg some (hp e)
    · refine ⟨none, fun e => ?_⟩
      have hn' : ¬ (SymP.at D e).nextV = S.opens.size := hn
      rw [hp0 e, hr' e]
      show (if (SymP.at D e).nextV = S.opens.size then some (placePanels (SymP.at D e).bl)
        else none) = none
      rw [if_neg hn']

/-! ## 2 The public test -/

/-- **The public test.** True where the list of panels is not made at the empty list of shown
values. -/
def triPlainB (S : Sides) : Bool :=
  match S.panels #[] with
  | none => true
  | some x => x.1.all fun b =>
      !(b.tri && b.claim == 1) || b.v0.all fun v0 => (S.opens.getD v0 {}).cd == 0

/-- What the test says of the list with open places. -/
theorem triPlain_at {S : Sides} (h : triPlainB S = true) {D : List SymBlk} {n : ℕ}
    (hD : ∀ e : Array E, S.panels e = some ((D.map (·.at e)).toArray, n)) (s : SymBlk)
    (hs : s ∈ D) (ht : s.b.tri = true) (hc : (s.b.claim == 1) = true) (v0 : ℕ)
    (hv : s.b.v0 = some v0) : (S.opens.getD v0 {}).cd = 0 := by
  unfold triPlainB at h
  rw [hD #[]] at h
  have h1 : ((D.map (·.at #[])).toArray.all fun b =>
      !(b.tri && b.claim == 1) || b.v0.all fun v0 => (S.opens.getD v0 {}).cd == 0) = true := h
  rw [← Array.all_toList, List.all_eq_true] at h1
  have h2 := h1 (s.at #[]) (List.mem_map_of_mem hs)
  have e1 : (s.at #[]).tri = true := ht
  have e2 : ((s.at #[]).claim == 1) = true := hc
  have e3 : (s.at #[]).v0 = some v0 := hv
  rw [e1, e2, e3] at h2
  simpa using h2

/-! ## 3 All products -/

/-- For each product of the second pass, in the products' order, the number of the shown value that
its first factor is. -/
def ixAll (D : List SymBlk) : List (Option ℕ) := (D.filter fun s => s.b.claim == 1).flatMap ixOf

/-- The maker's text of all products, opened at a list with open places. -/
theorem trips_open {S : Sides} {D : List SymBlk} {n : ℕ} {e : Array E}
    (hD : S.panels e = some ((D.map (·.at e)).toArray, n)) (R : Reads) (et : Array E)
    (hh : ℕ → ℕ → E) {l : Array Trip} (h : S.trips R et hh e = some l) :
    ∃ L : List (Array Trip),
      (D.filter fun s => s.b.claim == 1).mapM (fun s =>
        tripsOf S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights et) hh (s.at e)) =
          some L ∧ l.toList = L.flatMap Array.toList := by
  unfold Sides.trips at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hD] at hx
  obtain rfl := Option.some.inj hx
  dsimp only at h
  obtain ⟨L0, hL0, h⟩ := Option.bind_eq_some_iff.mp h
  have hf : ((D.map (·.at e)).toArray.filter fun b => b.claim == 1) =
      ((D.filter fun s => s.b.claim == 1).map (·.at e)).toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_filter, List.filter_map]
    rfl
  have hL1 : (((D.filter fun s => s.b.claim == 1).map (·.at e)).toArray.mapM
      (tripsOf S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights et) hh)) = some L0 := by
    rw [← hf]
    exact hL0
  rw [Array.mapM_eq_mapM_toList, List.mapM_map] at hL1
  obtain ⟨L, hL, eL⟩ := Option.map_eq_some_iff.mp hL1
  refine ⟨L, hL, ?_⟩
  rw [← Option.some.inj h, ← eL, Array.toList_flatMap]
  rfl

variable {N : ℕ} {q : ℕ → Cb.Gl.E}

/-- **All products of the second pass, at the point and at the corners.** -/
theorem trips_lin {S : Sides} {D : List SymBlk} {n : ℕ}
    (hD : ∀ e : Array E, S.panels e = some ((D.map (·.at e)).toArray, n))
    (hB : triPlainB S = true) (Rz : Reads) (Rt : ℕ → Reads) (etz : Array E) (ett : ℕ → Array E)
    (hhz : ℕ → ℕ → E) (hht : ℕ → ℕ → ℕ → E)
    (K : Kinds N q (fun a => valAff? S.v Rz (fun _ => zeroE) a)
      (fun t a => valAff? S.v (Rt t) (fun _ => zeroE) a) (S.weights etz)
      (fun t => S.weights (ett t)) hhz hht)
    (hpl : ∀ a, (S.opens.getD a {}).cd = 0 → ∀ et et' : Array E,
      (S.weights et).getD a #[] = (S.weights et').getD a #[])
    (e : Array E) (shs : ℕ → Array E) (lz : Array Trip) (lt : ℕ → Array Trip)
    (hz : S.trips Rz etz hhz e = some lz)
    (ht : ∀ t, t < N → S.trips (Rt t) (ett t) (hht t) (shs t) = some (lt t)) :
    LinAt N q e shs lz.toList (fun t => (lt t).toList) (ixAll D) := by
  obtain ⟨Lz, hLz, ez⟩ := trips_open (hD e) Rz etz hhz hz
  have hc := fun t (h : t < N) => trips_open (hD (shs t)) (Rt t) (ett t) (hht t) (ht t h)
  classical
  let Lt : ℕ → List (Array Trip) := fun t => if h : t < N then (hc t h).choose else []
  have hLt : ∀ t, t < N → (D.filter fun s => s.b.claim == 1).mapM (fun s =>
      tripsOf S (fun a => valAff? S.v (Rt t) (fun _ => zeroE) a) (S.weights (ett t)) (hht t)
        (s.at (shs t))) = some (Lt t) := fun t h => by
    have := (hc t h).choose_spec.1
    simpa only [Lt, dif_pos h] using this
  have et : ∀ t, t < N → (lt t).toList = (Lt t).flatMap Array.toList := fun t h => by
    have := (hc t h).choose_spec.2
    simpa only [Lt, dif_pos h] using this
  unfold ixAll
  rw [ez]
  refine (LinAt.mapM Array.toList
    (fun s => tripsOf S (fun a => valAff? S.v Rz (fun _ => zeroE) a) (S.weights etz) hhz (s.at e))
    (fun t s => tripsOf S (fun a => valAff? S.v (Rt t) (fun _ => zeroE) a) (S.weights (ett t))
      (hht t) (s.at (shs t))) ixOf _ (fun s hs bz bt hbz hbt => ?_) Lz Lt hLz hLt).congr et
  obtain ⟨hsD, hcl⟩ := List.mem_filter.mp hs
  exact tripsOf_lin K s (fun htri v0 hv t _ =>
    hpl v0 (triPlain_at hB hD s hsD htri hcl v0 hv) _ _) bz bt hbz hbt

/-! ## 4 The hypothesis on the summand's products -/

/-- **`TripsAt`**, at a point z of lt coordinates. -/
theorem tripsAt_of {S : Sides} {rows : TokRows} (hrows : tokenRows S = some rows)
    (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hB : triPlainB S = true) (z : Array E) (Rz : Reads)
    (hRz : S.readsTok z = some Rz)
    (K : ∀ Rt : ℕ → Reads,
      (∀ t, t < 2 ^ S.v.y.h.lt → S.readsTok (bitsOf S.v.y.h.lt t) = some (Rt t)) →
      Kinds (2 ^ S.v.y.h.lt) (Blocks.eqN S.v.y.h.lt 0 (pt Reading.gl z))
        (fun a => valAff? S.v Rz (fun _ => zeroE) a)
        (fun t a => valAff? S.v (Rt t) (fun _ => zeroE) a) (S.weights (eqTab z))
        (fun t => S.weights (eqTab (bitsOf S.v.y.h.lt t)))
        (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE)
        (fun t lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE))
    (hpl : ∀ a, (S.opens.getD a {}).cd = 0 → ∀ et et' : Array E,
      (S.weights et).getD a #[] = (S.weights et').getD a #[])
    (hmade : ∀ e : Array E, ∃ l, S.trips Rz (eqTab z)
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) e = some l) :
    ∃ idx, TripsAt S rows z idx := by
  -- the corners
  have hc := fun t (h : t < 2 ^ S.v.y.h.lt) => tokenRows_trips hrows (hT ▸ h)
  classical
  let Rt : ℕ → Reads := fun t => if h : t < 2 ^ S.v.y.h.lt then (hc t h).choose else Rz
  let sh : ℕ → Array E := fun t => (rows.getD t (#[], #[])).1
  let tr : ℕ → Array Trip := fun t => (rows.getD t (#[], #[])).2
  have hc' : ∀ t, t < 2 ^ S.v.y.h.lt → S.readsTok (bitsOf S.v.y.h.lt t) = some (Rt t) ∧
      S.trips (Rt t) (eqTab (bitsOf S.v.y.h.lt t))
        (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE) (sh t) = some (tr t) := by
    intro t h
    obtain ⟨sh', tr', a1, _, a3, a4⟩ := (hc t h).choose_spec
    have er : rows.getD t (#[], #[]) = (sh', tr') := by
      rw [Array.getD_eq_getD_getElem?, a4]
      rfl
    simp only [Rt, sh, tr, dif_pos h, er]
    exact ⟨a1, a3⟩
  -- the list of panels is made: the products at the point are
  obtain ⟨r, hr⟩ := panels_all S
  obtain ⟨l0, hl0⟩ := hmade #[]
  obtain ⟨D, n, hD⟩ : ∃ (D : List SymBlk) (n : ℕ), ∀ e : Array E,
      S.panels e = some ((D.map (·.at e)).toArray, n) := by
    cases r with
    | none =>
      unfold Sides.trips at hl0
      obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.mp hl0
      rw [hr #[]] at hx
      cases hx
    | some x => exact ⟨x.1, x.2, hr⟩
  have pos : 0 < 2 ^ S.v.y.h.lt := Nat.two_pow_pos _
  have lin := fun (e : Array E) (l : Array Trip) (hl : S.trips Rz (eqTab z)
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) e = some l) =>
    trips_lin hD hB Rz Rt (eqTab z) (fun t => eqTab (bitsOf S.v.y.h.lt t)) _ _
      (K Rt fun t h => (hc' t h).1) hpl e sh l tr hl fun t h => (hc' t h).2
  have tl : ∀ (a : Array Trip) k, a.toList.getD k trip0 = a.getD k trip0 := fun a k => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  refine ⟨fun k => (ixAll D).getD k none, ⟨fun e => ?_, fun k i hi t ht => ?_⟩⟩
  · obtain ⟨l, hl⟩ := hmade e
    have A := lin e l hl
    refine ⟨Rz, l, hRz, hl, ?_, fun k hk => ?_⟩
    · have := A.len 0 pos
      rw [Array.length_toList, Array.length_toList] at this
      exact this.symm
    · have B := A.at_ k (by rw [Array.length_toList]; exact hk)
      rw [tl] at B
      refine ⟨?_, ?_, ?_⟩
      · have := B.w 0 pos
        show Reading.gl.val (l.getD k trip0).1 = Reading.gl.val (wAt rows k)
        rw [← this]
        show _ = Reading.gl.val ((tr 0).getD k trip0).1
        rw [← tl]
      · cases ho : (ixAll D).getD k none with
        | some i =>
          rw [firstAt_some (idx := fun k => (ixAll D).getD k none) ho]
          exact congrArg Reading.gl.val (B.aS i ho).1
        | none =>
          rw [firstAt_none (idx := fun k => (ixAll D).getD k none) ho]
          refine Eq.trans (B.aN ho) ?_
          unfold Blocks.ext
          exact Finset.sum_congr rfl fun t _ => by
            show _ * Reading.gl.val ((tr t).toList.getD k trip0).2.1 = _
            rw [tl]
            rfl
      · refine Eq.trans B.b ?_
        unfold Blocks.ext
        exact Finset.sum_congr rfl fun t _ => by
          show _ * Reading.gl.val ((tr t).toList.getD k trip0).2.2 = _
          rw [tl]
          rfl
  · -- at a token a shown factor is that token's true value
    have A := lin #[] l0 hl0
    by_cases hk : k < l0.toList.length
    · have := ((A.at_ k hk).aS i hi).2 t ht
      show ((tr t).getD k trip0).2.1 = (sh t).getD i zeroE
      rw [← tl]
      exact this
    · -- there is no such product
      have : (ixAll D).getD k none = none := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [A.lix]; omega)]
        rfl
      rw [this] at hi
      cases hi

/-! ## 5 The test's trials -/

namespace TriPlainTest
open OnBytes.Desc.First.K4.Honest.SidesToy

/-- What the two jobs share at the small plan: group g of layers, synthetic numbers under a seed. -/
def toyS (g seed : Nat) : Option Sides :=
  toyPlans.toOption.bind fun x => do
    let Q ← toyQOf x g
    Sides.of Q ((made Q seed toyTokens).input (toyLook Q.P)) (ptsAt Q seed)

-- true at the small plan, both groups
#guard (toyS 0 1).map triPlainB == some true
#guard (toyS 1 1).map triPlainB == some true
-- negative tests: each claim's table is given the group
#guard (toyS 0 1).map (fun S =>
  triPlainB { S with opens := S.opens.map fun o => { o with cd := 1 } }) == some false
#guard (toyS 1 1).map (fun S =>
  triPlainB { S with opens := S.opens.map fun o => { o with cd := 1 } }) == some false

/-- The numbers of the claims that the test looks at. -/
def looked (S : Sides) : List Nat :=
  match S.panels #[] with
  | none => []
  | some x => (x.1.toList.filter fun b => b.tri && b.claim == 1).filterMap (·.v0)

/-- The tables with the group given to those whose number passes t. -/
def bent (S : Sides) (t : Nat → Bool) : Sides :=
  { S with opens := S.opens.zipIdx.map fun o => if t o.2 then { o.1 with cd := 1 } else o.1 }

-- the test looks at a claim
#guard (toyS 0 1).map (fun S => (looked S).isEmpty) == some false
-- negative test: one table alone is given the group: that of the first claim looked at
#guard (toyS 0 1).map (fun S => triPlainB (bent S fun i => (looked S).head? == some i)) ==
  some false
-- all tables but those looked at are given the group: the test still passes
#guard (toyS 0 1).map (fun S => triPlainB (bent S fun i => !(looked S).contains i)) == some true

end TriPlainTest

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.panels_all
#print axioms ProofFile.Honest.K4.triPlain_at
#print axioms ProofFile.Honest.K4.trips_open
#print axioms ProofFile.Honest.K4.trips_lin
#print axioms ProofFile.Honest.K4.tripsAt_of
