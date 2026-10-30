-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TripsThere.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: THE PRODUCTS OF THE
SECOND TOKEN SUMCHECK's SUMMAND ARE MADE (`tripsOf`, `Sides.trips`,
Johnson/Desc/K4/Honest/Sides.lean), on the honest reads at any point z of lt coordinates, at every
equality table, every never-sent vector and all values sh in the place of the shown factors for
which the panels are made.
`tripsOf_there`: one panel, from `PanelThere` (PanelTabsOf.lean), no never-sent vector where the
rows do not carry the selector, and that each form which the panel names is valued. `trips_there`:
all panels of the second pass.
How. The panels of the second pass name entries of the tables at rt and Y alone (SecondPass.lean),
whose weights the honest reads at [("rt", z), ("Y", …)] hold (`ptAt_has`, PtsHave.lean); a form that
names such entries alone is valued (`valued_of_inTest`, StackDataOf.lean). The sides return below
the panel's rows and columns because the verifier's `stackEnd` returns over the list
(`stackEnd_each`, Johnson/Road/FormsKeysEnd.lean; `there_of_end`; `panVB_mem`, PanVB.lean).

Not shown here. That the panels are made (hPan) and that `stackEnd` returns over them (hE):
PanelsOf.lean has both. The public facts hrd, hl, hT, hla, ht are hypotheses. A RETURN ALONE:
nothing on what a product is worth. Nothing on soundness, on completeness or on any other property.
No property is claimed.

  `tripsOf_there`   one panel's products are made
  `tok_two`   rt and Y stand in the list of a token's reads
  `trips_there`   **all products of the second pass are made**
-/
import Johnson.Road.K4.C.SecondPass
import Johnson.Road.K4.C.StackDataOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk StackEnd TableAsk TableAt layTables tableAsks readsOf stackEnd
  placePanels)
open OnBytes.Desc.First.K4.Slots (core)
open OnBytes.Desc.First.K4.Honest (Sides Trip matsOf readsAt valAff? tripsOf at2)

/-- CONDITIONAL on every hypothesis named. **ONE PANEL's PRODUCTS ARE MADE.** -/
theorem tripsOf_there (S : Sides) (val : Aff → Option E) (F : Array (Array E)) (hh : ℕ → ℕ → E)
    {b : SBlk} (T : PanelThere b) (hv : b.tri = false → b.virt = none)
    (hX : ∀ yv, (val (b.xx.getD yv {})).isSome = true)
    (hA : ∀ A i yv f, b.A = some A → A i yv = some f → (val f).isSome = true)
    (hB : ∀ B i yv f, b.B = some B → B i yv = some f → (val f).isSome = true) :
    (tripsOf S val F hh b).isSome = true := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  cases tri with
  | true =>
    cases v0 with
    | none => exact absurd (T.triV rfl) (by simp)
    | some v0 =>
      cases virt with
      | some k =>
        obtain ⟨cols, hc⟩ := amapM_there (g := fun yv => some (hh (k - 1) yv)) (Array.range ny)
          (fun _ _ => rfl)
        exact Option.isSome_iff_exists.mpr ⟨_, Option.bind_eq_some_iff.mpr ⟨cols, hc, rfl⟩⟩
      | none =>
        obtain ⟨cols, hc⟩ := amapM_there (g := fun yv => val (xx.getD yv {})) (Array.range ny)
          (fun yv _ => hX yv)
        exact Option.isSome_iff_exists.mpr ⟨_, Option.bind_eq_some_iff.mpr ⟨cols, hc, rfl⟩⟩
  | false =>
    have ev : virt = none := hv rfl
    subst ev
    obtain ⟨A', eA, rA⟩ := T.sideA rfl rfl
    have eA' : A = some A' := eA
    subst eA'
    cases v0 with
    | some v0 =>
      obtain ⟨rows, hr⟩ := amapM_there (g := fun i => (Array.range ny).mapM fun yv => do
          let a ← val (← A' i yv)
          let c ← some (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
          pure ((mulE ec (wt.getD i zeroE), a, c) : Trip)) (Array.range ni) (fun i hi => by
        have hi' : i < ni := by simpa using hi
        obtain ⟨l, hl⟩ := amapM_there (g := fun yv => do
            let a ← val (← A' i yv)
            let c ← some (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip)) (Array.range ny) (fun yv hy => by
          have hy' : yv < ny := by simpa using hy
          obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (rA _ _ hi' hy')
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hA A' _ _ f rfl hf)
          show (do
            let a ← val (← A' i yv)
            let c ← some (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip) : Option Trip).isSome = true
          rw [hf]
          show (do
            let a ← val f
            let c ← some (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip) : Option Trip).isSome = true
          rw [hz]
          rfl)
        exact Option.isSome_iff_exists.mpr ⟨l, hl⟩)
      exact Option.isSome_iff_exists.mpr ⟨_, Option.bind_eq_some_iff.mpr ⟨rows, hr, rfl⟩⟩
    | none =>
      obtain ⟨B', eB, rB⟩ := T.sideB rfl rfl rfl
      have eB' : B = some B' := eB
      subst eB'
      obtain ⟨rows, hr⟩ := amapM_there (g := fun i => (Array.range ny).mapM fun yv => do
          let a ← val (← A' i yv)
          let c ← val (← B' i yv)
          pure ((mulE ec (wt.getD i zeroE), a, c) : Trip)) (Array.range ni) (fun i hi => by
        have hi' : i < ni := by simpa using hi
        obtain ⟨l, hl⟩ := amapM_there (g := fun yv => do
            let a ← val (← A' i yv)
            let c ← val (← B' i yv)
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip)) (Array.range ny) (fun yv hy => by
          have hy' : yv < ny := by simpa using hy
          obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (rA _ _ hi' hy')
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hA A' _ _ f rfl hf)
          obtain ⟨f2, hf2⟩ := Option.isSome_iff_exists.mp (rB _ _ hi' hy')
          obtain ⟨z2, hz2⟩ := Option.isSome_iff_exists.mp (hB B' _ _ f2 rfl hf2)
          show (do
            let a ← val (← A' i yv)
            let c ← val (← B' i yv)
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip) : Option Trip).isSome = true
          rw [hf, hf2]
          show (do
            let a ← val f
            let c ← val f2
            pure ((mulE ec (wt.getD i zeroE), a, c) : Trip) : Option Trip).isSome = true
          rw [hz, hz2]
          rfl)
        exact Option.isSome_iff_exists.mpr ⟨l, hl⟩)
      exact Option.isSome_iff_exists.mpr ⟨_, Option.bind_eq_some_iff.mpr ⟨rows, hr, rfl⟩⟩

/-- rt and Y stand in the list of a token's reads, each with the number of coordinates of its sort.
-/
theorem tok_two (y : OnBytes.Model.Layer.Lay) (zlow z : Array E) (hz : z.size = y.h.lt)
    (hY : (longPoint zlow z).size = y.h.la) :
    PtIn y [("rt", z), ("Y", longPoint zlow z)] "rt" ∧
      PtIn y [("rt", z), ("Y", longPoint zlow z)] "Y" :=
  ⟨Or.inl ⟨by decide, ("rt", z), rfl, hz⟩, Or.inr ⟨by decide, ("Y", longPoint zlow z), rfl, hY⟩⟩

variable {S : Sides} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {R : OnBytes.Desc.First.K4.Honest.Reads}

/-- CONDITIONAL on every hypothesis named. **ALL PRODUCTS OF THE SECOND PASS ARE MADE.** -/
theorem trips_there (hrd : readsOf S.Q.P.y = .ok S.Q.P.rd)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hT : S.Q.P.y.T = 2 ^ S.Q.P.y.h.lt) (hla : S.Q.P.y.ls + S.Q.P.y.h.lt = S.Q.P.y.h.la)
    (ht : S.v.tab = r.1) {z : Array E} (hz : z.size = S.Q.P.y.h.lt)
    (hY : (longPoint S.zlow z).size = S.Q.P.y.h.la) (hR : S.readsTok z = some R)
    {sh : Array E} {x : Array SBlk × ℕ} (hPan : S.panels sh = some x)
    {y : OnBytes.Model.Layer.Lay} {rs om H1 V : Array E} {lam : ℕ} {a b : E} {fin : StackEnd}
    (hE : stackEnd y x.1 rs lam om H1 V a b = some fin) (et : Array E) (hh : ℕ → ℕ → E) :
    (S.trips R et hh sh).isSome = true := by
  obtain ⟨pans, hp, hx⟩ := panels_opened hPan
  obtain ⟨bl, places⟩ := x
  have ebl : bl = (placePanels pans.bl).1 := congrArg Prod.fst hx
  obtain ⟨p1, p2⟩ := tok_two S.Q.P.y S.zlow z hz hY
  have H := ptAt_has (v := S.v) hrd hl hR hT hla ht
  have P2 : Pan2 S.v (fun e => R.has e = true) bl := by
    rw [ebl]
    exact placePanels_2 (panelsT_2 (sidesEnv S sh) H p1 p2 S.TS
      (panelsA_2 (sidesEnv S sh) pan2_empty) pans hp)
  have PV : PanVB bl := by
    rw [ebl]
    exact placePanels_vb (panelsT_vb (sidesEnv S sh) S.TS
      (panelsA_vb (sidesEnv S sh) panVB_empty) pans hp)
  obtain ⟨l, hl2⟩ := amapM_there
    (g := tripsOf S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights et) hh)
    (bl.filter fun b => b.claim == 1) (fun b hb => by
      have hb' : b ∈ bl.toList ∧ (b.claim == 1) = true := by
        simpa using hb
      obtain ⟨s1, s2, h1⟩ := stackEnd_each hE b hb'.1
      obtain ⟨⟨cA, cB, cX⟩, _, h3⟩ := pan2_mem P2 hb'.1 (eq_of_beq hb'.2)
      exact tripsOf_there S _ _ hh (there_of_end (panVB_mem PV hb'.1) h1) (fun e => (h3 e).1)
        (fun yv => valued_of_inTest (cX yv) _)
        (fun A i yv f eA ef => valued_of_inTest (cA A eA i yv f ef) _)
        (fun B i yv f eB ef => valued_of_inTest (cB B eB i yv f ef) _))
  unfold Sides.trips
  exact Option.isSome_iff_exists.mpr ⟨_, Option.bind_eq_some_iff.mpr
    ⟨(bl, places), hPan, Option.bind_eq_some_iff.mpr ⟨l, hl2, rfl⟩⟩⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tripsOf_there
#print axioms OnBytes.Road.K4.C.tok_two
#print axioms OnBytes.Road.K4.C.trips_there
