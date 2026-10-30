-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Split.lean: the yes of the shared chain's "SPLIT" gives `SplitLaid`
(Johnson/Desc/Key/Laid/SplitDef.lean). Theorems.

Main names.
  `laid_split`: `split p d [r] = some d'`, where the shape splits, gives all of `SplitLaid`'s
    fields: by `split_inv` (Johnson/Desc/K14/Law/Lays.lean) and the ground's three yeses
    read back (Johnson/Desc/Key/Laid/GroundYes.lean).
  `splitLaid_irrefl`: `SplitLaid` holds of no record and itself: G_u has an open row more behind.

Limits. Of splitL's five tests "two groups" alone is carried. Of the function `split`; of the block
that decides by it: Johnson/Desc/Key/Laid/AtBlocks.lean. Of the form "a yes gives". Nothing on
soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.SplitDef
import Johnson.Desc.Key.Laid.GroundYes
import Johnson.Desc.K14.Law.Lays
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState Par)
open VerifiableInference.Desc.Ground (ok)
open _root_.Desc.K14 (St split splitL)
open _root_.Desc.K14.Law (split_inv onOmega onU)

namespace VerifiableInference.Desc.Key

theorem withRow_groupOff (S : Statement) (g : Nat) (r : Row) (i : Nat) (h : g ≠ i) :
    (withRow S g r).groups[i]? = S.groups[i]? := by
  simp [withRow, Array.getElem?_modify, h]

/-- **The yes of "SPLIT" gives SplitLaid.** -/
theorem laid_split (p : Par) (d d' : St) (r : Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : split p d [r] = some d') :
    ∃ GU GO x l n row mu, SplitLaid p.S d d' GU GO x l n row mu := by
  obtain ⟨row, xs, GO, n, d₁, d₂, hf, _, hGO, hok, hk, h2, h3⟩ := split_inv p d d' r hS h
  obtain ⟨x, l, hx, hl, hc, hleft, e1⟩ := takeMaskP_eq _ _ _ _ hk
  have e2 := addRowP_eq _ _ _ _ h2
  have e3 := addRowP_eq _ _ _ _ h3
  have htwo : d.loc.gOmega ≠ d.loc.gU := by
    simp only [ok, splitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    simpa using hok.1
  -- the statements, step by step
  have g1 : d₁.st.groups = d.st.groups := by rw [e1]
  have c1 : d₁.st.codes = d.st.codes := by rw [e1]
  have s2 : d₂.st =
      withRow d₁.st d.loc.gOmega (onOmega row GO.members d.loc.oSp n (E.ofTriple xs)) := by
    rw [e2]
  have s3 : d'.st = withRow d₂.st d.loc.gU (onU row GO.members d.loc.oSp n (E.ofTriple xs)) := by
    rw [e3]
  have o3 : d'.st.oracles = d₁.st.oracles := by
    rw [s3, s2]
    rfl
  have hGO1 : d₁.st.groups[d.loc.gOmega]? = some GO := by
    rw [g1]
    exact hGO
  have hGO2 : d₂.st.groups[d.loc.gOmega]? = some { GO with
      rows := GO.rows.push (onOmega row GO.members d.loc.oSp n (E.ofTriple xs)) } := by
    rw [s2]
    exact withRow_group _ _ _ _ hGO1
  -- G_u is there: the second adding says so
  obtain ⟨GU, hGU2⟩ : ∃ G, d₂.st.groups[d.loc.gU]? = some G := by
    cases hg : d₂.st.groups[d.loc.gU]? with
    | some G => exact ⟨G, rfl⟩
    | none =>
      exfalso
      unfold VerifiableInference.Desc.Ground.addRowP at h3
      split at h3
      · rename_i hk3
        simp only [ok, VerifiableInference.Desc.Ground.rowL, List.all_cons, List.all_nil,
          Bool.and_true, Bool.and_eq_true] at hk3
        have t := hk3.1
        rw [hg] at t
        cases t
      · cases h3
  have hGU1 : d₁.st.groups[d.loc.gU]? = some GU := by
    rw [s2, withRow_groupOff _ _ _ _ htwo] at hGU2
    exact hGU2
  have hGU : d.st.groups[d.loc.gU]? = some GU := by
    rw [g1] at hGU1
    exact hGU1
  have hGU3 : d'.st.groups[d.loc.gU]? = some { GU with
      rows := GU.rows.push (onU row GO.members d.loc.oSp n (E.ofTriple xs)) } := by
    rw [s3]
    exact withRow_group _ _ _ _ hGU2
  have hGO3 : d'.st.groups[d.loc.gOmega]? = some { GO with
      rows := GO.rows.push (onOmega row GO.members d.loc.oSp n (E.ofTriple xs)) } := by
    rw [s3, withRow_groupOff _ _ _ _ (Ne.symm htwo)]
    exact hGO2
  have inO1 := addRowP_in _ _ _ _ _ h2 hGO1
  have inU2 := addRowP_in _ _ _ _ _ h3 hGU2
  have E12 : Means.Extends d₁.st d₂.st := by
    rw [s2]
    exact Means.extends_withRow _ _ _
  have E23 : Means.Extends d₂.st d'.st := by
    rw [s3]
    exact Means.extends_withRow _ _ _
  refine ⟨GU, GO, x, l, n, row, E.ofTriple xs, ?_, ?_, ?_, ?_, ?_, ?_, htwo, hf, hx, hl, hc, hleft,
    ?_, ?_, ?_, hGU, hGO, hGU3, hGO3, ?_, ?_, ?_,
    fun hI => (Means.addRowP_keeps h3 (Means.addRowP_keeps h2 (Means.takeMaskP_keeps hk hI)).1).1⟩
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [s3, s2]
    exact c1
  · rw [o3, e1]
    simp
  · rw [o3, e1]
    simp [Array.getElem?_modify, hx]
  · intro o ho
    rw [o3, e1]
    simp [Array.getElem?_modify, Ne.symm ho]
  · rw [s3, s2]
    simp [withRow, g1]
  · intro i hU hO
    rw [s3, withRow_groupOff _ _ _ _ (Ne.symm hU), s2, withRow_groupOff _ _ _ _ (Ne.symm hO), g1]
  · refine Means.RowIn.extends E23 ?_ inU2
    exact fun _ hh => hh
  · refine Means.RowIn.extends E23 ?_ (Means.RowIn.extends E12 (G' := GO) ?_ inO1)
    · exact fun _ hh => hh
    · exact fun _ hh => hh

/-- SplitLaid holds of no record and itself. -/
theorem splitLaid_irrefl (S : Params.LinShape) (d : St) (GU GO : Group) (x : Oracle) (l : Ledger)
    (n : Nat) (row : Row) (mu : E) : ¬ SplitLaid S d d GU GO x l n row mu := by
  intro h
  have e := Option.some.inj (h.gU.symm.trans h.gU')
  have t : GU.rows.size = (GU.rows.push (onU row GO.members d.loc.oSp n mu)).size :=
    congrArg (fun G : Group => G.rows.size) e
  rw [Array.size_push] at t
  omega

end VerifiableInference.Desc.Key
