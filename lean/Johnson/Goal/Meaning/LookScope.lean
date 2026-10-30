-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LookScope.lean: four public facts on the record of the lookup of a layer
sub-proof, X.y.fo, at all public files in the goals' scope, in the letters of the lookup's port
(OnBytes/Tie/Pv/Lookup/Port/FoNums.lean, ShiftQPort.lean).

  look_eight: it has eight calls.
  look_hot: a position's bits lie within a tree's depth: DF.lT ≤ X.y.fo.dT. (The depth is the
    library's Dk DF, by Dk_of_layout, Johnson/Road/FormsKeysShape.lean:227.)
  look_sizes: call c has 2^(aC DF c) keys: the library's number, not only room for it.
  look_rows: call c's table has 2^8 rows at c = 3 and 2^16 rows otherwise.
  look_tabs: every row of the verifier's table of call c, as a number, read in the challenge field,
    is the image of an entry of the library's table of that call (lut tbRef c). From hL_in_scope
    (Johnson/Goal/Meaning/TabsScope.lean) and word_cast
    (Johnson/Road/Ends/AlgIn.lean:43).
A caller that asks these of a lookup's record by a test on public data has them here as theorems,
where its record is X.y.fo. Not claimed: that any caller's record is X.y.fo.
-/
import Johnson.Goal.Meaning.TabsScope
import Johnson.Road.Ends.AlgIn
import OnBytes.Tie.Pv.Lookup.Port.ShiftQPort

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (aC lJ lut Dk fams used)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem look_eight (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.y.fo.NC = 8 := by
  obtain ⟨hy, -, -, -, -, -, hN, -⟩ := pub34_public hZ hR h
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, h8]

/-- The premise H of Dk_of_layout (Johnson/Road/FormsKeysShape.lean). -/
theorem lines_floor (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (cc : Fin 8) :
    ∃ cd, X.y.calls[cc.val]? = some cd ∧ cd.segs.map (·.name) = (fams cc).map segName ∧
      (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
        Nat.clog 2 (used DF cc) := by
  obtain ⟨-, -, -, -, -, -, hN, hfl, -⟩ := pub34_public hZ hR h
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  have hq : cc.val < X.y.calls.size := by rw [h8]; exact cc.isLt
  refine ⟨X.y.calls[cc.val], Array.getElem?_eq_getElem hq, ?_, hfl cc⟩
  have e := line_at hN cc
  have eg : X.y.calls.getD cc.val default = X.y.calls[cc.val] := by simp [Array.getD, hq]
  rw [eg] at e
  exact e

theorem look_hot (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : DF.lT ≤ X.y.fo.dT := by
  obtain ⟨hy, S, -, -, Zd, hc, hN, -⟩ := pub34_public hZ hR h
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  have e := Dk_of_layout (v := ⟨X.y, X.layers.sc, 0, 0, 0, [], #[]⟩) hy S Zd hc h8
    (lines_floor hZ hR h)
  have e' : Dk DF = X.y.fo.dT := e
  rw [← e']
  decide +kernel

theorem look_sizes (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (c : Fin 8) :
    Cb.LdLkp.Port.nOf X.y.fo c = aC DF c := by
  obtain ⟨hy, S, -, -, Zd, -, -, -⟩ := pub34_public hZ hR h
  obtain ⟨cd, hcq, hn, hfl⟩ := lines_floor hZ hR h c
  have hfl' : (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤ lJ DF c := hfl
  have hsh := (admitted_of_layout hy S.p3).shape
  have h2 : X.y.fo.calls[c.val]? = some (X.y.callRecord c.val cd) := by
    rw [(fo_of_layout hy).1, cl_of_layout hy]
    simp [hcq]
  unfold Cb.LdLkp.Port.nOf
  rw [h2]
  show X.y.h.ll + cd.lJ + X.y.h.lt = DF.lL + lJ DF c + DF.lT
  rw [lJ_of_call (v := ⟨X.y, X.layers.sc, 0, 0, 0, [], #[]⟩) hy S Zd
    (Array.mem_of_getElem? hcq) hn, hsh, Zd.lL, Zd.lT, Nat.max_eq_left hfl']

theorem look_rows (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (c : Fin 8) :
    Cb.LdLkp.Port.kOf X.y.fo c = if c = 3 then 8 else 16 := by
  obtain ⟨c0, h1, -, h3⟩ := hL_in_scope hZ hR h c
  unfold Cb.LdLkp.Port.kOf
  rw [h1]
  exact h3

/-- EVERY ROW OF THE VERIFIER's TABLE OF A CALL IS AN ENTRY OF THE LIBRARY's. -/
theorem look_tabs (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (c : Fin 8) (u : ℕ)
    (hu : u < 2 ^ Cb.LdLkp.Port.kOf X.y.fo c) :
    ∃ v ∈ (Cm.Seg.tabOf (lut tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
      ((FoNums.tauN X.y.fo c u : ℕ) : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E v := by
  obtain ⟨c0, h1, h2, h3⟩ := hL_in_scope hZ hR h c
  have hk : Cb.LdLkp.Port.kOf X.y.fo c = c0.k := by
    unfold Cb.LdLkp.Port.kOf
    rw [h1]
    rfl
  rw [hk] at hu
  have hu' : u < (lut tbRef c).rows := by
    rw [← h2.rows]
    exact hu
  obtain ⟨m, hm1, hm2⟩ := h2.row u hu'
  have ht : FoNums.tauN X.y.fo c u = (c0.tauAt u).toNat := by
    unfold FoNums.tauN
    have e : X.y.fo.calls.getD c.val {} = c0 := by
      rw [Array.getD_eq_getD_getElem?, h1]
      rfl
    rw [e]
  refine ⟨(((lut tbRef c).row u : ℤ) : Cb.Gl.F), ⟨u, ?_, rfl⟩, ?_⟩
  · show u < 2 ^ (if c = 3 then 8 else 16)
    rw [← h3]
    exact hu
  · rw [ht, hm1, Alg.word_cast, map_intCast, ← hm2, Int.cast_natCast]

#print axioms look_eight
#print axioms look_hot
#print axioms look_sizes
#print axioms look_rows
#print axioms look_tabs

end Meaning.P34
