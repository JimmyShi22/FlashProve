-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/LayLiveTables.lean: the proofs of the three statements of
Johnson/Desc/K8/Honest/LayLiveTablesStatement.lean, to the letter, and four helpers. Lemmas; none of
the library's goals.

How. `layTables_has`: by the list of families, as the library's `layTables_mem`
(Johnson/Desc/First/Link/Law/LayTablesLive.lean) goes the other way. `famTables`: that;
`layParts_eq` (Johnson/Road/FormsKeysTab.lean): the parts' matrices are M0, M0 + 1, ..; `funsOf_mem`
(Johnson/Road/FormsKeysPoint.lean). `cut_fine`: a coordinate of the last k of a point is one of the
point's (`lastOf_ok`, FormsKeysPoint.lean; `mem_extract`, DigitsLiveOf.lean of this folder).
`pin_asked`, `pin_phi`: the family "b-pin" by the two functions' texts. `layLiveTables`: the six
families with their numbers (`six_numbers`, FormsKeysTab.lean) and weights (`weights_of_names`,
FormsKeysPoint.lean); no weight reads 0: `longPhiNe`, `phiPNe` (HeadLiveTables.lean of this folder),
`eqTab_ne` (PlanesLiveOf.lean); the matrix's number by cases along `matIx`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K8.Honest.LayLiveTablesStatement
import Johnson.Desc.K8.Honest.HeadLiveTables
import Johnson.Desc.K8.Honest.PlanesLiveOf
import Johnson.Desc.K8.Honest.DigitsLiveOf
import Johnson.Road.FormsKeysTab
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model

/-- The first statement, with the list as a pattern. -/
theorem layTables_has_aux {mats : Array (Nat × Nat)} : ∀ (asks : List Layer.TableAsk) (p : Nat)
    (r : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat),
    Layer.layTables mats asks p = some r →
    ∀ a ∈ asks, ∃ b, (a, (Layer.layParts mats a a.parts b).1) ∈ r.2.1
  | [], _, _, _, _, ha => nomatch ha
  | a0 :: rest, p, r, h, a, ha => by
    rw [Layer.layTables] at h
    split at h
    · exact nomatch h
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 ha with rfl | h'
      · exact ⟨p, List.mem_cons_self⟩
      · obtain ⟨b, hb⟩ := layTables_has_aux rest _ r' hr' a h'
        exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- **Every family that was asked is laid.** -/
theorem layTables_has : LayTablesHas := fun _ asks p r h a ha => layTables_has_aux asks p r h a ha

/-- **Every part of a family has its table.** -/
theorem famTables : FamTables := by
  intro y fo pts mats asks p r funs a m k phi h ha hm hf hp i hi
  obtain ⟨b, hb⟩ := layTables_has mats asks p r h a ha
  obtain ⟨phi', e1, e2⟩ := OnBytes.Road.funsOf_mem hf hb
  obtain rfl : phi' = phi := Option.some.inj (e1.symm.trans hp)
  have hmem : (a.M0 + i, b + i * (k * (m / a.L))) ∈ (Layer.layParts mats a a.parts b).1 := by
    rw [OnBytes.Road.layParts_eq mats a m k hm b]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  exact ⟨_, Array.mem_def.1 (e2 _ hmem), rfl, rfl, rfl, rfl⟩

/-- A coordinate of the last k coordinates of a point is a coordinate of the point. -/
theorem cut_fine {z Z : Array E} {k : Nat} (h : lastOf z k = .ok Z)
    (hz : ∀ w ∈ z.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) :
    ∀ w ∈ Z.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  obtain ⟨-, rfl⟩ := OnBytes.Road.lastOf_ok h
  intro w hw
  exact hz w (mem_extract z _ _ w hw)

/-- The family "b-pin" is asked. -/
theorem pin_asked (y : Layer.Lay) (rd : Layer.Reads) (g : Nat) :
    (⟨"b-pin", (Layer.matIx y).iB, 1, 2 ^ y.h.lmb, "", false⟩ : Layer.TableAsk) ∈
      Layer.tableAsks y rd g := by
  unfold Layer.tableAsks
  exact List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Its weights are the public numbers. -/
theorem pin_phi (y : Layer.Lay) (fo : Forest.Heard) (pts : List (String × Array E)) (M0 L : Nat) :
    Layer.phiOf y fo pts ⟨"b-pin", M0, 1, L, "", false⟩ = some (Forest.phiP y.h.lmb) := by
  show (if ("b-pin" == "b-bits-0") = true then Forest.phiB fo y.h.lmb 0
    else if ("b-pin" == "b-bits-1") = true then Forest.phiB fo y.h.lmb 1
    else if ("b-pin" == "b-pin") = true then some (Forest.phiP y.h.lmb) else _) = _
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]

/-- **Every matrix of the segment has a live table.** -/
theorem layLiveTables : LayLiveTables := by
  intro y rd g mats H hd hd2 pts r funs tl hrd hAF hQA hXI hXO hAD hAR hp hzt hl hf htl hmats hNM
    hsh hlong hshort hb hT hla hz mu hmu
  -- one family, one part
  have one : ∀ (a : Layer.TableAsk) (phi : Array E) (m k : Nat), a ∈ Layer.tableAsks y rd g →
      Layer.phiOf y H.fo pts a = some phi →
      (∀ j, j < a.L → Reading.gl.val (phi.getD j zeroE) ≠ 0) →
      (∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = (m, k)) → 0 < a.L → m % a.L = 0 →
      ∀ i, i < a.parts → ∃ Fn, LiveTable tl (a.M0 + i) Fn := by
    intro a phi m k ha hphi hw hm hL hdiv i hi
    obtain ⟨Fn, hFn, e1, e2, e3, e4⟩ :=
      famTables y H.fo pts mats _ 0 r funs a m k phi hl ha hm hf hphi i hi
    have em : (tl.mats.getD (a.M0 + i) {}).m = m :=
      (congrArg Prod.fst ((hmats (a.M0 + i)).symm.trans (hm i hi)))
    refine ⟨Fn, by rw [htl]; exact hFn, e1, Or.inr e4, by rw [e2]; exact hL, ?_, ?_⟩
    · rw [em, e2]
      exact hdiv
    · intro j hj
      rw [e3]
      exact hw j (by rw [← e2]; exact hj)
  obtain ⟨⟨a0, h0, n0, M0, P0, L0⟩, ⟨a3, h3, n3, M3, P3, L3⟩, ⟨a4, h4, n4, M4, P4, L4⟩,
    ⟨a5, h5, n5, M5, P5, L5⟩, ⟨a1, h1, n1, M1, P1, L1⟩, ⟨a2, h2, n2, M2, P2, L2⟩⟩ :=
    OnBytes.Road.six_numbers y rd g hAF hQA hXI hXO hAD hAR
  obtain ⟨Z, hZ, wL, wS⟩ := OnBytes.Road.weights_of_names hrd g hAF hQA hXI hXO hAD hAR hp hzt
  have sZ : Z.size = y.ls + y.h.lt := by rw [OnBytes.Road.size_last hZ, hla]
  have st : H.ztF.size = y.h.lt := OnBytes.Road.size_last hzt
  have long : ∀ j, j < 2 ^ y.h.la → Reading.gl.val ((longPhi Z y.ls y.h.lt).getD j zeroE) ≠ 0 := by
    intro j hj
    exact longPhiNe Z y.ls y.h.lt sZ (cut_fine hZ hz) j (by rw [← hla]; exact hj)
  have short : ∀ j, j < y.T → Reading.gl.val ((eqTab H.ztF).getD j zeroE) ≠ 0 := by
    intro j hj
    exact eqTab_ne H.ztF (cut_fine hzt hz) j (by rw [st, ← hT]; exact hj)
  have pa : 0 < 2 ^ y.h.la := Nat.two_pow_pos _
  have pT : 0 < y.T := by rw [hT]; exact Nat.two_pow_pos _
  have q0 := one a0 _ _ _ h0 (wL a0 h0 (by rw [n0]; exact List.mem_cons_self))
    (by rw [L0]; exact long) (fun q hq => by rw [M0]; exact hsh 0 (by decide) q (P0 ▸ hq))
    (by rw [L0]; exact pa) (by rw [L0]; exact hlong 0 (by decide))
  have q3 := one a3 _ _ _ h3
    (wL a3 h3 (by rw [n3]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (by rw [L3]; exact long) (fun q hq => by rw [M3]; exact hsh 3 (by decide) q (P3 ▸ hq))
    (by rw [L3]; exact pa) (by rw [L3]; exact hlong 3 (by decide))
  have q4 := one a4 _ _ _ h4 (wL a4 h4 (by
    rw [n4]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by rw [L4]; exact long) (fun q hq => by rw [M4]; exact hsh 4 (by decide) q (P4 ▸ hq))
    (by rw [L4]; exact pa) (by rw [L4]; exact hlong 4 (by decide))
  have q5 := one a5 _ _ _ h5 (wL a5 h5 (by
    rw [n5]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))) (by rw [L5]; exact long)
    (fun q hq => by rw [M5]; exact hsh 5 (by decide) q (P5 ▸ hq))
    (by rw [L5]; exact pa) (by rw [L5]; exact hlong 5 (by decide))
  have q1 := one a1 _ _ _ h1 (wS a1 h1 (by rw [n1]; exact List.mem_cons_self))
    (by rw [L1]; exact short) (fun q hq => by rw [M1]; exact hsh 1 (by decide) q (P1 ▸ hq))
    (by rw [L1]; exact pT) (by rw [L1]; exact hshort 1 (by decide))
  have q2 := one a2 _ _ _ h2
    (wS a2 h2 (by rw [n2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (by rw [L2]; exact short) (fun q hq => by rw [M2]; exact hsh 2 (by decide) q (P2 ▸ hq))
    (by rw [L2]; exact pT) (by rw [L2]; exact hshort 2 (by decide))
  obtain ⟨kb, hkb⟩ := hb
  have qb := one _ _ (2 ^ y.h.lmb) kb (pin_asked y rd g) (pin_phi y H.fo pts _ _)
    (fun j hj => phiPNe y.h.lmb j hj)
    (fun q hq => by
      have hq1 : q < 1 := hq
      obtain rfl : q = 0 := by omega
      exact hkb)
    (Nat.two_pow_pos _) (Nat.mod_self _) 0 Nat.one_pos
  rw [M0, P0] at q0
  rw [M1, P1] at q1
  rw [M2, P2] at q2
  rw [M3, P3] at q3
  rw [M4, P4] at q4
  rw [M5, P5] at q5
  -- the matrix's number
  have eN : tl.NM = y.parts.getD 0 0 + y.parts.getD 1 0 + 4 + 1 := hNM
  rw [eN] at hmu
  by_cases c0 : mu < y.parts.getD 0 0
  · have k := q0 mu c0
    have e : OnBytes.Road.firstM y 0 + mu = mu := Nat.zero_add mu
    rw [e] at k
    exact k
  by_cases c1 : mu < y.parts.getD 0 0 + y.parts.getD 1 0
  · have k := q1 (mu - y.parts.getD 0 0) (by
      show mu - y.parts.getD 0 0 < y.parts.getD 1 0
      omega)
    have e : OnBytes.Road.firstM y 1 + (mu - y.parts.getD 0 0) = mu := by
      show y.parts.getD 0 0 + (mu - y.parts.getD 0 0) = mu
      omega
    rw [e] at k
    exact k
  have pick : ∀ (t : Nat), mu = y.parts.getD 0 0 + y.parts.getD 1 0 + t →
      (∃ Fn, LiveTable tl (y.parts.getD 0 0 + y.parts.getD 1 0 + t + 0) Fn) →
      ∃ Fn, LiveTable tl mu Fn := by
    intro t e k
    rw [e]
    exact k
  by_cases d0 : mu = y.parts.getD 0 0 + y.parts.getD 1 0 + 0
  · exact pick 0 d0 (q2 0 Nat.one_pos)
  by_cases d1 : mu = y.parts.getD 0 0 + y.parts.getD 1 0 + 1
  · exact pick 1 d1 qb
  by_cases d2 : mu = y.parts.getD 0 0 + y.parts.getD 1 0 + 2
  · exact pick 2 d2 (q3 0 Nat.one_pos)
  by_cases d3 : mu = y.parts.getD 0 0 + y.parts.getD 1 0 + 3
  · exact pick 3 d3 (q5 0 Nat.one_pos)
  · exact pick 4 (by omega) (q4 0 Nat.one_pos)

end VerifiableInference.Desc.First.K8.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms VerifiableInference.Desc.First.K8.Honest.layTables_has_aux
#print axioms VerifiableInference.Desc.First.K8.Honest.layTables_has
#print axioms VerifiableInference.Desc.First.K8.Honest.famTables
#print axioms VerifiableInference.Desc.First.K8.Honest.cut_fine
#print axioms VerifiableInference.Desc.First.K8.Honest.pin_asked
#print axioms VerifiableInference.Desc.First.K8.Honest.pin_phi
#print axioms VerifiableInference.Desc.First.K8.Honest.layLiveTables
