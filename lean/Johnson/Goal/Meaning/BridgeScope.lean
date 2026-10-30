-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/BridgeScope.lean: the bridge from a lookup's calls to a group's key vectors
(layerBridge_of_calls, Johnson/Road/Ends/AlgBridgeL5.lean:58) at all public files in the goals'
scope, with its premises on public data paid.

layerBridge_of_calls has twenty-one premises. Nineteen speak of the public files alone and are paid
here from VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp, publicOf Z.pol Z.KL lay = .ok X and
g < 12: hy S hs hg hrd Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hnn hL. Two say that a
function of public data returns, and stay premises: hl (layTables) and hw (weighedOf): a run of the
check that has returned has computed both.
  mat_of_layTensors, hmats_of_layout: every tensor of a layout that the verifier returns for a shape
    with routed experts lies in one of the four families of matrices. General in the shape.
  nOf, kOf: the logarithms of the numbers of keys and of rows of the eight calls.
  layerBridge_in_scope; linkOK_in_scope (the seam before the lookup of group g, by
    linkOK_of_layerSplit, Johnson/Road/Lane5SplitG.lean:92).
-/
import Johnson.Goal.Meaning.HearPremises
import Johnson.Goal.Meaning.TabsScope
import Johnson.Goal.Meaning.RopeInt
import Johnson.Road.Ends.AlgBridgeL5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5 OnBytes.Ends
open OnBytes.Model.Layer (Lay Shape Ten TableAsk TableAt layout layTensors tensorAsks layTables
  tableAsks)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (Mat ppref tbRef AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used aC lut)

/-! ## The tensors' matrices -/

/-- A laid tensor has the matrix of one of the asks. -/
theorem mat_of_layTensors : ∀ (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (off : Array ℕ) (t : Ten),
    t ∈ (layTensors asks off).1 → ∃ a ∈ asks, t.mat = a.2.1
  | [], _, t, h => by cases h
  | (n, mat, nl, cnt, J) :: rest, off, t, h => by
    rw [layTensors] at h
    by_cases h0 : (nl == 0) = true
    · rw [if_pos h0] at h
      obtain ⟨a, ha, e⟩ := mat_of_layTensors rest off t h
      exact ⟨a, List.mem_cons_of_mem _ ha, e⟩
    · rw [if_neg h0] at h
      rcases List.mem_cons.mp h with e | h'
      · exact ⟨_, List.mem_cons_self, by rw [e]⟩
      · obtain ⟨a, ha, e⟩ := mat_of_layTensors rest _ t h'
        exact ⟨a, List.mem_cons_of_mem _ ha, e⟩

/-- Every ask names one of the four families. -/
theorem mat_of_asks (h : Shape) (Lam LamM nqk dq dkv : ℕ) :
    ∀ a ∈ tensorAsks h Lam LamM nqk dq dkv, a.2.1 < 4 := by
  have all : ((tensorAsks h Lam LamM nqk dq dkv).all fun a => decide (a.2.1 < 4)) = true := by
    unfold tensorAsks
    generalize h.gcl = b1
    generalize h.p3 = b2
    generalize h.rcl = b3
    generalize h.p4 = b4
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl
  intro a ha
  simpa using List.all_eq_true.mp all a ha

/-- hmats, of every layout that the verifier returns for a shape with routed experts. -/
theorem hmats_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hp3 : h.p3 = true) :
    ∀ (n : String) (Tn : Ten), y.T_ n = some Tn → Tn.mat < 4 := by
  intro n Tn hT
  have hm : Tn ∈ y.ten := List.mem_of_find?_eq_some hT
  rw [(laid_of_layout hy hp3).2.ten] at hm
  obtain ⟨a, ha, e⟩ := mat_of_layTensors _ _ _ hm
  rw [e]
  exact mat_of_asks _ _ _ _ _ _ a ha

/-! ## The bridge -/

/-- The logarithm of the number of keys of call q: the library's. -/
def nOf (q : ℕ) : ℕ := if h : q < 8 then aC DF ⟨q, h⟩ else 0

/-- The logarithm of the number of rows of the table of call q. -/
def kOf (q : ℕ) : ℕ := if q = 3 then 8 else 16

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- THE BRIDGE AT ALL PUBLIC FILES IN THE GOALS' SCOPE. Of layerBridge_of_calls' premises two are
left: that layTables and weighedOf return. -/
theorem layerBridge_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    (Mz : Mats ℤ) (Wi : Mat) :
    LayerBridge (layerShape X.P) X.layers.sc X.y g Mz Wi
      (Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf) := by
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
  exact Alg.layerBridge_of_calls (P := pubAt X tokv) (rd := X.layers.rd) hy S hs
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
    hfl hw nOf kOf
    (fun cc => by
      unfold nOf
      rw [dif_pos cc.isLt])
    (fun cc => by
      obtain ⟨c0, h1, h2, h3⟩ := hL_in_scope hZ hR h cc
      refine ⟨c0, h1, h2, ?_, h3⟩
      rw [h3]
      unfold kOf
      by_cases e : cc = 3
      · rw [if_pos e, e]
        rfl
      · rw [if_neg e, if_neg (show ¬ cc.val = 3 from fun e' => e (Fin.ext e'))])
    Mz Wi

/-- THE SEAM BEFORE THE LOOKUP OF GROUP g, at all public files in the goals' scope: where the
group's relation without the keys holds of Mz and Wi and the calls' keys lie in the tables, the
library's link 2 g is in order. By linkOK_of_layerSplit. -/
theorem linkOK_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} (nf : Inst.Model.NormPar) (pol : AcceptancePolicy) (x : Cm.Seg.XI)
    (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : (Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf).InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc nf) pol) Wi x
      (2 * g) (libMZ X.y g Mz) := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  exact linkOK_of_layerSplit B.lay B.switches B.sized B.sized2 B.p4 (show g < nGr from hg)
    X.layers.sc nf pol x (layerBridge_in_scope hZ hR h tokv hg hl hw Mz Wi) R I

#print axioms hmats_of_layout
#print axioms layerBridge_in_scope
#print axioms linkOK_in_scope

end Meaning.P34
