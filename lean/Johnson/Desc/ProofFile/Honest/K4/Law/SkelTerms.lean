-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelTerms.lean: CONDITIONAL: on `LookSkel`.

What is here. CONGRUENCE: THE SECOND SUMCHECK OVER THE TOKENS (`jobTerms`,
Johnson/Desc/K4/Honest/Terms.lean) at two inputs and two lists of what the lookup in front has
sampled, OF ONE SKELETON (`LookSkel`, Law/LookSkel.lean: a hypothesis, paid nowhere here). The
functions of the inner laws (panels, trips, readsTok, summand, endsOn, tripsOf) lie in
Johnson/Desc/K4/Honest/Sides.lean. No definition; eleven statements with their proofs.

  `panelsOn_rel`   the verifier's panels, placed, at two shared data of one skeleton.
  `tripsOf_rel`, `trips_rel`   the second pass's products: as many.
  `readsTok_has`, `endsOn_rel`, `tokenRows_rel`   for each token: as many values and products.
  `summand_rel`   the summand on given values of the shown factors.
  `sameWeights_true`   the job's test on the products' weights is true wherever the rows are made.
  `tabs_sizes`, `jobTermsOn_skel`, `jobTerms_skel`   **the job**: both makers return or neither, and
      the public test on a job's shape (`k4JobFits`) gives one answer at every call (`JobSkel`,
      Law/SkelJobs.lean).

Debts and ends. The file defines no relation. `LookSkel` IS A DEBT: see Law/LookSkel.lean: IT IS THE
ONE HYPOTHESIS OF `jobTerms_skel`, the law at two inputs that other files call (Law/MakersSkel.lean,
Law/MakersAt.lean); the two inputs w and w₀ are free letters there. `SidesSkel` (Law/SkelSides.lean)
IS AN END: see there: it is the hypothesis K of seven inner laws here (`panelsOn_rel`, `trips_rel`,
`readsTok_has`, `endsOn_rel`, `tokenRows_rel`, `summand_rel`, `jobTermsOn_skel`); `jobTerms_skel`
pays it on the spot with `sidesOf_rel`, from `LookSkel` alone. `HasSame` (Law/SkelReads.lean) IS AN
END: concluded here by `readsTok_has`; the hypothesis hR of `trips_rel` and `endsOn_rel`, paid with
it in `tokenRows_rel` and `summand_rel`. `JobSkel` IS AN END: `jobTermsOn_skel` and `jobTerms_skel`
end in it. BETWEEN TWO INPUTS THE LAWS HERE COMPARE WHETHER A VALUE IS THERE, HOW MANY VALUES AND
PRODUCTS THERE ARE, AND, IN `panelsOn_rel`, THE PANELS' KEYS AND THE NUMBER OF PLACES (the library's
`BlkKeys False`, Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean: the flag, the numbers, the
entries that the forms name; no weight): NOT WHAT A VALUE OR A PRODUCT IS; `sameWeights_true`
compares products' weights AT ONE SHARED DATA, token against token. `BlkKeys` and the library's
`FormKeys` are hypotheses of `tripsOf_rel` (hb; inside hval): `trips_rel` pays both on the spot,
from `panelsOn_rel` and with `valAff_rel` (Law/SkelReads.lean).

Not shown here. IT STANDS ON `sidesOf_rel` (Law/SkelSides.lean) AND `trips_weights`
(Law/SkelWeights.lean). NO MAKER IS SHOWN TO RETURN ANYWHERE: a statement on a maker compares two
calls, but `sameWeights_true`, which starts from one return. Nothing on what a table, a product or
an end value is worth.

Kin. `tripsOf_rel` and `panelTabs_rel` (Law/SkelStack.lean) take a panel apart in the same way, for
the products and for the two sides. `tripsOf_weights` (Law/SkelWeights.lean) is the sister of
`tripsOf_rel` on the products' weights at one shared data. Inner laws of this file are called in
Law/FitTerms.lean, Law/TermsAll.lean and Law/AtEnds.lean (all three: no part of the library yet) too
(how: the head of Law/SkelSides.lean), and `panelsOn_rel` in Law/SkelStack.lean. No twin in the
library is known to its writers.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelLists
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelJobs
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelSides
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelWeights
import Johnson.Desc.K4.Honest.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Aff longPoint)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same optRel_map' all_alike)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (fits_sizes)
open OnBytes.Desc.First.K4.RtPub

variable {S S₀ : Sides}

/-- The verifier's panels, placed, and the number of places. -/
theorem panelsOn_rel (K : SidesSkel S S₀) (sh sh₀ : Array E) :
    OptRel (fun x x₀ : Array SBlk × Nat =>
      All2 (BlkKeys False) x.1.toList x₀.1.toList ∧ x.2 = x₀.2) (S.panels sh) (S₀.panels sh₀) := by
  unfold Sides.panels
  dsimp only
  rw [K.TS]
  refine optRel_bind (panels_keys (W := False) K.v.keys (fun f => f.elim) _) fun a a₀ hp => ?_
  exact optRel_iteB (by rw [hp.nextV, K.opens]) (by trivial)
    (optRel_bind_same fun _ => optRel_pure (placePanels_keys hp.bl))

/-- The products of one panel: as many. -/
theorem tripsOf_rel {W : Prop} {val val₀ : Aff → Option E}
    (hval : ∀ a a₀, FormKeys a a₀ → OptRel (fun _ _ => True) (val a) (val₀ a₀))
    (F F₀ : Array (Array E)) (hh hh₀ : Nat → Nat → E) {b b₀ : SBlk} (hb : BlkKeys W b b₀) :
    OptRel (fun a a₀ : Array Trip => a.size = a₀.size) (tripsOf S val F hh b)
      (tripsOf S₀ val₀ F₀ hh₀ b₀) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri₀, v0₀, claim₀, ec₀, ni₀, ny₀, wy₀, w₀, off₀, A₀, B₀, wt₀, sl₀, xx₀, virt₀⟩ := b₀
  obtain ⟨e1, e2, e9, e3, e4, e5, e6, e7, e8, hA, hB, hx, _, _⟩ := hb
  dsimp only at e1 e2 e9 e3 e4 e5 e6 e7 e8 hA hB hx
  subst e1 e2 e9 e3 e4 e5 e6 e7 e8
  unfold tripsOf
  dsimp only
  refine optRel_ite ?_ (optRel_ite trivial ?_)
  · refine optRel_bind_same fun v0 => optRel_bind (S := fun _ _ => True) ?_ fun _ _ _ =>
      optRel_pure ?_
    · refine OptRel.mono (fun _ _ _ => by trivial) (amapM_size_rel ny fun yv _ => ?_)
      cases virt with
      | some k => rfl
      | none => exact OptRel.isSome_eq (hval _ _ (hx yv))
    · rw [Array.size_map, Array.size_map]
  · refine optRel_bind hA fun f f₀ hf => ?_
    refine optRel_bind (S := fun r r₀ : Array (Array Trip) =>
      All2 (fun a a₀ => a.size = a₀.size) r.toList r₀.toList) (amapM_rel (fun i => ?_) _)
      fun r r₀ hr => optRel_pure (size_flatMap_all2 hr)
    refine OptRel.mono (fun a a₀ k => k.1.trans k.2.symm) (amapM_size_rel ny fun yv _ => ?_)
    refine OptRel.isSome_eq (R := fun _ _ => True) ?_
    refine optRel_bind (hf i yv) fun q q₀ hq => optRel_bind (hval q q₀ hq) fun _ _ _ => ?_
    cases v0 with
    | some v0 => exact True.intro
    | none =>
      cases B with
      | none =>
        cases B₀ with
        | none => exact True.intro
        | some _ => exact False.elim hB
      | some g =>
        cases B₀ with
        | none => exact False.elim hB
        | some g₀ =>
          exact optRel_bind (hB i yv) fun q q₀ hq =>
            optRel_bind (hval q q₀ hq) fun _ _ _ => True.intro

/-- All products of the second pass: as many. -/
theorem trips_rel (K : SidesSkel S S₀) {R R₀ : Reads} (hR : HasSame R R₀) (et et₀ : Array E)
    (hh hh₀ : Nat → Nat → E) (sh sh₀ : Array E) :
    OptRel (fun a a₀ : Array Trip => a.size = a₀.size) (S.trips R et hh sh)
      (S₀.trips R₀ et₀ hh₀ sh₀) := by
  unfold Sides.trips
  refine optRel_bind (panelsOn_rel K sh sh₀) fun x x₀ hx => ?_
  obtain ⟨bl, n⟩ := x
  obtain ⟨bl₀, n₀⟩ := x₀
  dsimp only
  refine optRel_bind (S := fun r r₀ : Array (Array Trip) =>
    All2 (fun a a₀ => a.size = a₀.size) r.toList r₀.toList)
    (amapM_all2_rel (S := BlkKeys False) (fun b b₀ hb => tripsOf_rel
      (fun a a₀ k => valAff_rel K.v.keys.iU3 K.v.keys.K3 hR k _ _) _ _ _ _ hb)
      (aall2_filter (fun b b₀ hb => by rw [hb.claim]) hx.1))
    fun r r₀ hr => optRel_pure (size_flatMap_all2 hr)

/-- The reads at a token's point, at two points of one length: there at both or at neither, and in
`HasSame`. -/
theorem readsTok_has (K : SidesSkel S S₀) {z z₀ : Array E} (hz : z.size = z₀.size) :
    OptRel HasSame (S.readsTok z) (S₀.readsTok z₀) := by
  unfold Sides.readsTok
  rw [K.Q]
  refine readsAt_has _ _ _ K.fo (.cons ⟨rfl, hz⟩ (.cons ⟨rfl, ?_⟩ .nil))
  show (longPoint S.zlow z).size = (longPoint S₀.zlow z₀).size
  unfold longPoint
  rw [Array.size_append, Array.size_append, K.zlow, hz]

/-- The shown factors' values: as many. -/
theorem endsOn_rel (K : SidesSkel S S₀) {R R₀ : Reads} (hR : HasSame R R₀) :
    OptRel (fun a a₀ : Array E => a.size = a₀.size) (endsOn S R) (endsOn S₀ R₀) := by
  unfold endsOn
  exact OptRel.mono (fun _ _ k => k.length)
    (amapM_all2_rel (S := FormKeys) (R := fun _ _ : E => True)
      (fun a a₀ k => optRel_map' (valAff_rel K.v.keys.iU3 K.v.keys.K3 hR k _ _)
        fun _ _ _ => by trivial) K.ends)

/-- For each token: as many values, as many products. -/
theorem tokenRows_rel (K : SidesSkel S S₀) :
    OptRel (fun r r₀ : Array (Array E × Array Trip) =>
      All2 (fun x x₀ => x.1.size = x₀.1.size ∧ x.2.size = x₀.2.size) r.toList r₀.toList)
      (tokenRows S) (tokenRows S₀) := by
  unfold tokenRows
  dsimp only
  rw [K.v.keys.y]
  refine amapM_rel (fun t => ?_) _
  exact optRel_bind (readsTok_has K rfl) fun R R₀ hR =>
    optRel_bind (endsOn_rel K hR) fun sh sh₀ hs =>
      optRel_bind (trips_rel K hR _ _ _ _ sh sh₀) fun tr tr₀ ht => optRel_pure ⟨hs, ht⟩

/-- The summand at a point, on given values of the shown factors: there at both or at neither, at
two points of one length. -/
theorem summand_rel (K : SidesSkel S S₀) (sh sh₀ : Array E) {z z₀ : Array E}
    (hz : z.size = z₀.size) :
    OptRel (fun _ _ => True) (S.summand sh z) (S₀.summand sh₀ z₀) := by
  unfold Sides.summand
  refine optRel_bind (readsTok_has K hz) fun R R₀ hR => ?_
  dsimp only
  exact optRel_bind (trips_rel K hR _ _ _ _ sh sh₀) fun _ _ _ => True.intro

/-- **The job's test on the products' weights is true wherever the tokens' rows are made.** -/
theorem sameWeights_true (S : Sides) {rows : Array (Array E × Array Trip)}
    (h : tokenRows S = some rows) :
    (rows.all fun x => x.2.map (·.1) == ((rows.getD 0 (#[], #[])).2).map (·.1)) = true := by
  have hm : ∀ x ∈ rows.toList, ∃ R et hh sh, S.trips R et hh sh = some x.2 := by
    intro x hx
    obtain ⟨t, ht⟩ := amapM_mem h x hx
    obtain ⟨R, _, h1⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨sh, _, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨tr, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    obtain rfl : (sh, tr) = x := Option.some.inj h4
    exact ⟨R, _, _, sh, h3⟩
  rw [← Array.all_toList]
  refine List.all_eq_true.mpr fun x hx => ?_
  have hpos : 0 < rows.size := by
    have := List.length_pos_of_mem hx
    rwa [Array.length_toList] at this
  have e0 : rows.getD 0 (#[], #[]) = rows[0] := by simp [Array.getD, hpos]
  obtain ⟨R, et, hh, sh, a⟩ := hm x hx
  obtain ⟨R', et', hh', sh', a'⟩ := hm _ (Array.getElem_mem_toList hpos)
  rw [e0, trips_weights S a a']
  exact beq_self_eq_true _

/-- n tables made entry by entry of one array: each has that array's size. -/
theorem tabs_sizes {α : Type} (n : Nat) (rows : Array α) (g : Nat → α → E) :
    ((Array.range n).map fun i => rows.map (g i)).map Array.size =
      (Array.range n).map fun _ => rows.size := by
  rw [Array.map_map]
  congr 1
  funext i
  exact Array.size_map ..

/-- **The second sumcheck over the tokens**, of the shared data. -/
theorem jobTermsOn_skel (K : SidesSkel S S₀) : OptRel JobSkel (jobTermsOn S) (jobTermsOn S₀) := by
  unfold jobTermsOn
  refine optRel_bind_eq (tokenRows_rel K) fun rows rows₀ h1 h2 hr => ?_
  have hz : rows.size = rows₀.size := hr.length
  have hK : (rows.getD 0 (#[], #[])).2.size = (rows₀.getD 0 (#[], #[])).2.size :=
    (agetD_all2 (R := fun x x₀ : Array E × Array Trip =>
      x.1.size = x₀.1.size ∧ x.2.size = x₀.2.size) ⟨rfl, rfl⟩ hr 0).2
  dsimp only
  rw [K.v.keys.y]
  have hf := fits_sizes
    { n := S₀.v.y.h.lt, order := OnBytes.Model.orderDefault S₀.v.y.h.lt, way := .point S₀.zt
      maps :=
        ((Array.range (OnBytes.Model.Layer.nEndT S₀.v.y)).map fun i =>
          rows₀.map fun x => x.1.getD i zeroE) ++
        ((Array.range (rows₀.getD 0 (#[], #[])).2.size).map fun k =>
          rows₀.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.1) ++
        ((Array.range (rows₀.getD 0 (#[], #[])).2.size).map fun k =>
          rows₀.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.2)
      pairs := (List.range (rows₀.getD 0 (#[], #[])).2.size).map fun k =>
        (((rows₀.getD 0 (#[], #[])).2.getD k (zeroE, zeroE, zeroE)).1,
          OnBytes.Model.Layer.nEndT S₀.v.y + k,
          OnBytes.Model.Layer.nEndT S₀.v.y + (rows₀.getD 0 (#[], #[])).2.size + k) }
    { n := S₀.v.y.h.lt, order := OnBytes.Model.orderDefault S₀.v.y.h.lt, way := .point S.zt
      maps :=
        ((Array.range (OnBytes.Model.Layer.nEndT S₀.v.y)).map fun i =>
          rows.map fun x => x.1.getD i zeroE) ++
        ((Array.range (rows.getD 0 (#[], #[])).2.size).map fun k =>
          rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.1) ++
        ((Array.range (rows.getD 0 (#[], #[])).2.size).map fun k =>
          rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.2)
      pairs := (List.range (rows.getD 0 (#[], #[])).2.size).map fun k =>
        (((rows.getD 0 (#[], #[])).2.getD k (zeroE, zeroE, zeroE)).1,
          OnBytes.Model.Layer.nEndT S₀.v.y + k,
          OnBytes.Model.Layer.nEndT S₀.v.y + (rows.getD 0 (#[], #[])).2.size + k) }
    rfl rfl
    (by
      dsimp only
      rw [Array.map_append, Array.map_append, Array.map_append, Array.map_append, tabs_sizes,
        tabs_sizes, tabs_sizes, tabs_sizes, tabs_sizes, tabs_sizes, hz, hK])
    (by
      dsimp only
      rw [List.map_map, List.map_map, hK]
      rfl)
    (congrArg some K.zt)
  have ha : (rows.all fun x => x.1.size == OnBytes.Model.Layer.nEndT S₀.v.y &&
        x.2.size == (rows.getD 0 (#[], #[])).2.size) =
      (rows₀.all fun x => x.1.size == OnBytes.Model.Layer.nEndT S₀.v.y &&
        x.2.size == (rows₀.getD 0 (#[], #[])).2.size) := by
    rw [← Array.all_toList, ← Array.all_toList, hK]
    exact all_alike (fun a b k => by rw [k.1, k.2]) hr
  refine optRel_iteB (congrArg not (congrArg₂ and (congrArg₂ and hf
    ((sameWeights_true S h1).trans (sameWeights_true S₀ h2).symm)) ha)) (by trivial)
    (optRel_bind_same fun _ => optRel_pure
      (jobSkel_of hf (by rfl) (len_one _ _) (by rfl) (by rfl) fun rs => ?_))
  simp only [Array.length_toList, Array.size_map, Array.size_range]

/-- **The second sumcheck over the tokens**, at two inputs and two lists of one skeleton. -/
theorem jobTerms_skel (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts} (L : LookSkel p.fo p₀.fo) :
    OptRel JobSkel (jobTerms Q w p) (jobTerms Q w₀ p₀) := by
  unfold jobTerms
  exact optRel_bind (sidesOf_rel Q w w₀ L) fun _ _ K => jobTermsOn_skel K

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.panelsOn_rel
#print axioms ProofFile.Honest.K4.tripsOf_rel
#print axioms ProofFile.Honest.K4.trips_rel
#print axioms ProofFile.Honest.K4.readsTok_has
#print axioms ProofFile.Honest.K4.endsOn_rel
#print axioms ProofFile.Honest.K4.tokenRows_rel
#print axioms ProofFile.Honest.K4.summand_rel
#print axioms ProofFile.Honest.K4.sameWeights_true
#print axioms ProofFile.Honest.K4.tabs_sizes
#print axioms ProofFile.Honest.K4.jobTermsOn_skel
#print axioms ProofFile.Honest.K4.jobTerms_skel
