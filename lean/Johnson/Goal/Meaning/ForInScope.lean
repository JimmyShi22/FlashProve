-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ForInScope.lean: the bridge from a lookup's calls to a group's key vectors, at
all public files in the goals' scope, FROM THE LOOKUP's OWN CLAUSE, at the record's own numbers.

layerBridge_in_scope (Johnson/Goal/Meaning/BridgeScope.lean) takes InTables at the calls
Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf, where nOf and kOf are closed functions of that file. The
lookup's clause stands at the record's own n and k: Alg.ForInG P g Mz Wi
(Johnson/Road/Lane5ForInG.lean:67), which is InTables at Alg.callsG P g Mz Wi (nF P.y.fo)
(kN P.y.fo) (forInG_iff_inTables, :78): another term. So whoever holds the lookup's clause could not
hand it over by name. Here it can:
  layerKeys_in_scope: ForInG (pubAt X tokv) g Mz Wi gives LayerKeys, by
    layerKeys_of_forIn (:120), whose premise hL is hL_in_scope to the letter.
  keyField_of_forIn: the same under the name KeyField.
  layerOrd_of_forIn: LayerR0 and ForInG give LayerOrd. layerOrds_of_forIn: all twelve groups.
  linkOK_of_forIn_in_scope: LayerR0 and ForInG give the library's link 2 g.
Premises beside the three facts on the files and g < 12: hl and hw: that layTables and weighedOf
return. No function of public data alone pays them here: publicOf calls neither. What returns is
the hearing of the link of group g, in a run: for `verify-on-bytes` hearOwn_ran
(OnBytes/Tie/Pv/Lay/HearOwn.lean:102) and joinStart_ok
(OnBytes/Tie/Pv/Lookup/Ends/FoJoinStart.lean [not in this library]:54).
Not claimed: ForInG or LayerR0 of anything.
-/
import Johnson.Goal.Meaning.LayerJoint
import Johnson.Road.Lane5ForInG

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5 OnBytes.Ends OnBytes.Road.Rows.Norms
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Mat AcceptancePolicy)
open Inst.Model.All (DF nGr)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- FROM THE LOOKUP's OWN CLAUSE TO THE LOOKUP CLAUSE OF THE GROUP, at all public files in the
goals' scope. -/
theorem layerKeys_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerKeys (layerShape X.P) X.layers.sc X.y g Mz Wi := by
  obtain ⟨hy, S, hs, hrd, Zd, -, hN, hfl, Zw, -, hlw, h4⟩ := pub34_public hZ hR h
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hsh := shape_in_scope hZ hR h
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout hy S.p3).2.Lam, shape_of_public h, hsh]
    rfl
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  exact Alg.layerKeys_of_forIn (P := pubAt X tokv) (rd := X.layers.rd) hy S hs
    (by show g < X.y.NGr; rw [B.groups]; exact hg) hrd hl Zd h4
    (by rw [show (layerShape X.P).dh = 128 from A.num 7]) (hmats_of_layout hy S.p3)
    (by
      show X.y.T = DF.T
      rw [(laid2_of_layout hy).T, shape_of_public h, hsh]
      rfl)
    Zw hlw
    (fun l hl4 => by
      show g * X.y.Lam + l < 48
      have : l < 4 := hl4
      rw [hLam]
      omega)
    (Rope.ropeOK_in_scope hZ hR h hg) h8
    (fun cc cd hcd => by
      have e := line_at hN cc
      have eg : X.y.calls.getD cc.val default = cd := by
        have hq : cc.val < X.y.calls.size := by rw [h8]; exact cc.isLt
        have hcd' : X.y.calls[cc.val]? = some cd := hcd
        rw [Array.getElem?_eq_getElem hq] at hcd'
        simp [Array.getD, hq, Option.some.inj hcd']
      rw [eg] at e
      exact e)
    hfl hw (hL_in_scope hZ hR h) Mz Wi I

/-- The same under the name of the record's fifth clause. -/
theorem keyField_of_forIn (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    KeyField (layerShape X.P) X.layers.sc X.y g Mz Wi :=
  layerKeys_in_scope hZ hR h tokv hg hl hw I

/-- The layers' joint from the lookup's own clause. -/
theorem layerOrd_of_forIn (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} {x : Cm.Seg.XI}
    (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x :=
  layerOrd_iff_split.2 ⟨R, layerKeys_in_scope hZ hR h tokv hg hl hw I⟩

/-- All twelve groups, at a family of lists. -/
theorem layerOrds_of_forIn (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) (own : ℕ → Mats ℤ) {Wi : Mat}
    {x : Cm.Seg.XI}
    (hl : ∀ g < 12, ∃ mats r, layTables mats (tableAsks X.y X.layers.rd g) 0 = some r ∧
      ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    (R : ∀ g < 12, LayerR0 (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x)
    (I : ∀ g < 12, Alg.ForInG (pubAt X tokv) g (own (2 * g)) Wi) :
    ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x := by
  intro g hg
  obtain ⟨mats, r, h1, h2⟩ := hl g hg
  exact layerOrd_of_forIn hZ hR h tokv hg h1 h2 (R g hg) (I g hg)

/-- The seam before the lookup of group g, from the lookup's own clause. -/
theorem linkOK_of_forIn_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ)
    {g : ℕ} (hg : g < 12) {mats : Array (ℕ × ℕ)}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} (nf : Inst.Model.NormPar) (pol : AcceptancePolicy) (x : Cm.Seg.XI)
    (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc nf) pol) Wi x
      (2 * g) (libMZ X.y g Mz) := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  have hN := (pub34_public hZ hR h).2.2.2.2.2.2.1
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  exact linkOK_of_layerSplit B.lay B.switches B.sized B.sized2 B.p4 (show g < nGr from hg)
    X.layers.sc nf pol x (fun _ => layerKeys_in_scope hZ hR h tokv hg hl hw I) R
    ((Alg.forInG_iff_inTables (P := pubAt X tokv) B.lay h8 Mz Wi).1 I)

#print axioms layerKeys_in_scope
#print axioms keyField_of_forIn
#print axioms layerOrd_of_forIn
#print axioms layerOrds_of_forIn
#print axioms linkOK_of_forIn_in_scope

end Meaning.P34
