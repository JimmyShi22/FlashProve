-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TabIsEXInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TEST WITH
CODE tabIsEXB (Law/TabIsEXCode.lean: "the table of the exponential's lookup is the library's EX at
each of its 2^16 rows") ACCEPTS THE TABLE THAT IS READ OFF THE PLACE OF THE LOOKUP ON THE OUTPUT
HEAD's CALLS. Statements and proofs.

How. NO ROW IS EVALUATED. The head's layout makes the table of its calls of the kind "FE" by
tauFEOf at three numbers of the head's shape (OnBytes/Model/HeadLayout.lean: layout, lookups); in
scope these are 24, 8 and 4 (Goal/Meaning/HeadCondScope.lean: numbers_in_scope): NONE OF THE EIGHT
FREE NUMBERS. That this array holds the library's EX is proved (Law/LibTab.lean: tab_EX_of_tau); and
the walk's verdict is yes just if the rows are right (Law/TabIsEX.lean: tabRun_spec, an "if and only
if").

  lookOne_tau_FE     a call of the kind "FE" bears the table that is handed in for that kind.
  tau3_of_layout     where the head's layout returns and the call lines are the stored example's
                     six: row u of call 3's table is row u of tauFEOf at the shape's own numbers.
  tau3_in_scope      in scope: of tauFEOf 24 8 4.
  headAt_fs          the place's shape is the layout's.
  tabIsEXB_of_rows   the test's yes from the rows' equation.
  tabIsEX_in_scope   MAIN.

WHAT IT IS NOT. A fact on public parameters alone. Nothing on soundness. UNDER THE LIBRARY's
publicOf. It speaks of tabOf (rowH x); that a composed meaning's letter for the head's table is
that term is its own definition's to say.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.Kinds.Law.TabIsEX
import Johnson.Desc.Kinds.Law.LibTab
import Johnson.Desc.First.Look.K3CallerHeadParts
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (CallD Call place)
open OnBytes.Model.Head (Shape HL tauFEOf)
open VerifiableInference.Desc.First.Look (placeAt lookAt P)

/-- A call of the kind "FE" bears the table that is handed in for that kind. -/
theorem lookOne_tau_FE (h : Shape) (a b : Array UInt64) (c : CallD) (hk : c.kind = "FE") :
    (lookOne h a b c).tau = some b := by
  unfold lookOne
  dsimp only
  rw [hk]
  rfl

/-- **Row u of call 3's table is row u of the head's table of exponentials.** -/
theorem tau3_of_layout {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hl : OnBytes.Model.Head.callLines h = VerifierAndGoals.Lines.callsHRef)
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) (u : Nat) :
    FoNums.tauN L.fs 3 u = ((tauFEOf h.famF h.digSh h.tabS).getD u 0).toNat := by
  obtain ⟨L0, calls, fs0, pub, _, h4, _, _, _, hcl, hfs⟩ := layout_fs hy
  have hc := calls_six h4 hl
  have e3 : L.cl.getD 3 {} =
      { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
          (place "FEa" "FE" [("HE0", L0.JVa, false)] (OnBytes.Model.Head.keyFloor h - h.lt)) with
        iota := fs0.iota.getD 3 0 } := by
    rw [hcl, lookups_is, hc]
    simp [Array.getD_eq_getD_getElem?]
  unfold FoNums.tauN
  rw [hfs]
  show ((L.cl.getD 3 {}).tauAt u).toNat = _
  rw [e3]
  unfold Call.tauAt
  show (match (lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
      (place "FEa" "FE" [("HE0", L0.JVa, false)] (OnBytes.Model.Head.keyFloor h - h.lt))).tau with
    | none => u.toUInt64
    | some a => a.getD u 0).toNat = _
  rw [lookOne_tau_FE h tauFC _ _ rfl]

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **In scope: of the table at 24, 8 and 4.** -/
theorem tau3_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) (u : Nat) :
    FoNums.tauN X.HLy.fs 3 u = ((tauFEOf 24 8 4).getD u 0).toNat := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  have hP := OnBytes.Road.Hd.scan_of_scope hZ hR h
  have Zs : SizesH X.hS := by
    rw [St.hS, hP]
    exact sizesH_scan _ _
  have N := numbers_in_scope hZ hR h
  have e := tau3_of_layout Zs.lines St.head u
  rw [N.F, N.sh, N.sT] at e
  exact e

/-- **The place's shape is the layout's.** -/
theorem headAt_fs (hZ : VerifierAndGoals.InScope Z = true)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {x : First.Look.Place}
    (hx : headAt X = some x) : x.fs = X.HLy.fs := by
  obtain ⟨h4, hN⟩ := head_24 hZ h
  obtain ⟨p, hp, hs, _, _⟩ := calls_place hZ h
  unfold headAt at hx
  rw [h4, hN] at hx
  have e24 : (if true = true then 2 else 1) * 12 = 24 := rfl
  rw [e24] at hx
  unfold placeAt at hp
  cases hl : lookAt X 24 false with
  | none =>
    rw [hl] at hx
    cases hx
  | some x0 =>
    rw [hl] at hx hp
    obtain rfl : P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x0 = p :=
      Option.some.inj hp
    have hx' : ((P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x0).shape.map
        fun k => { x0 with fs := k }) = some x := hx
    rw [hs] at hx'
    obtain rfl := Option.some.inj hx'
    rfl

/-- **The test's yes, from the rows' equation.** -/
theorem tabIsEXB_of_rows {tab : Nat → Nat}
    (h : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) : tabIsEXB tab = true := by
  show (tabRun tab 65536).1 = true
  refine (tabRun_spec tab 65536).2.2 fun u hu => ?_
  have e := h u (by norm_num; exact hu)
  unfold Inst.Model.EX at e
  exact_mod_cast e

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TEST ACCEPTS.** -/
theorem tabIsEX_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {x : First.Look.Place}
    (hx : headAt X = some x) : tabIsEXB (tabOf (rowH x)) = true :=
  tabIsEXB_of_rows (Came.tab_EX_of_tau (rowH x) fun u _ => by
    show FoNums.tauN x.fs 3 u = _
    rw [headAt_fs hZ h hx]
    exact tau3_in_scope hZ hR h u)

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tau3_of_layout
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tau3_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.headAt_fs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tabIsEXB_of_rows
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tabIsEX_in_scope
