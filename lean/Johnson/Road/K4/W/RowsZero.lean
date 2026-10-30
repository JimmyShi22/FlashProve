-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/RowsZero.lean: CONDITIONAL.

What is here. Groups 4 to 6 of the layers' own rounds (sub-protocol K4): each form of the list
`rowsForms` (OnBytes/Desc/First/K4/Claims.lean) has the value 0 (`Aff.value`) in a world whose
slots hold the library's terms, at cells at which the library's seventeen identities of every norm
hold at every position. It is `shown_says` (Johnson/Road/K4/Says2.lean) and `idnP_of_forms`
(OnBytes/Desc/First/NormBridge/BridgeWorld.lean) read from right to left. Statements and proofs.

  `digits_value`      a digit of a norm's row, at the norms' token point and at the end point of the
                      row products' sumcheck: the library's byte, extended over the positions.
  `four_zero`         group 4, one norm: the four claims on the shown end values.
  `seventeen_zero`    groups 5 and 6, one norm: the nine carries and the eight lines.
  **`rows_zero`**     the whole list.

Not shown here. That any world meets the premises: no example is known. THAT THE TABLES OF THE
READS ARE TRUE OF THE CELLS IN W IS A PREMISE (Fits, Johnson/Road/FormsKeysKit.lean; TrueAt3,
Johnson/Road/FormsKeysTrue3.lean); so are NormWords (Johnson/Road/FormsKeysIdnW.lean) and
NI = nNu. That the list is there anywhere: `rows_zero` starts from its return. That the library's
identities hold at any cells (hI): nothing here says that the cells are those of an inference. That
a prover's play lays these values under the slots. ρ, W, the cells and the eight points are free.
No property is claimed.
-/
import Johnson.Road.K4.W.RowsAll
import Johnson.Road.K4.NormsReads
import Johnson.Road.K4.Says2
import OnBytes.Desc.First.NormBridge.BridgeWorld
import OnBytes.Desc.First.NormBridge.IdnDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard Pub epsOf twoM)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal led bS npOf)
open Blocks (ext)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (rowsForms normsForms digitsAt digitsAt_found)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- A digit of a norm's row at the two token points. -/
theorem digits_value (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (ν : ℕ) :
    (∀ Dg, digitsAt v "P_V" ν = some Dg → ∀ n, n < 99 →
        (Dg n).value ρ W = ledAt D t ν uP n) ∧
      (∀ Dg, digitsAt v "r_tV" ν = some Dg → ∀ n, n < 99 →
        (Dg n).value ρ W = ledAt D t ν uR n) := by
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  constructor
  · intro Dg h n hn
    obtain ⟨b, hb⟩ := digitsAt_found h
    exact Road.K4.digitsAt_value F.num hb hrow hJ T (by rw [hm]; exact T3.arP b hb) h n hn
  · intro Dg h n hn
    obtain ⟨b, hb⟩ := digitsAt_found h
    exact Road.K4.digitsAt_value F.num hb hrow hJ T (by rw [hm]; exact T3.arR b hb) h n hn

/-- **Group 4, one norm.** j: the first of the norm's four slots. -/
theorem four_zero (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {ν : ℕ} {Dr : ℕ → Aff}
    (hDr : digitsAt v "r_tV" ν = some Dr) (j : ℕ)
    (hE : W.slot (j + 0) = ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) uR ∧
      W.slot (j + 1) = ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) uR ∧
      W.slot (j + 2) = ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) uR ∧
      W.slot (j + 3) = ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) uR) :
    ∀ f ∈ ([(P6.Row.ofDigits Dr).a, (P6.Row.ofDigits Dr).b, (P6.Row.ofDigits Dr).Rlo,
        (P6.Row.ofDigits Dr).Rhi].zipIdx.map fun x => Aff.slot (j + x.2) - x.1),
      f.value ρ W = 0 := by
  have hd := (digits_value F T3 ν).2 Dr hDr
  obtain ⟨va, vb, vl, vh⟩ := P6.fields_value ρ W Dr
  have ea : Inst.Model.Ledger.sa (P6.dv ρ W Dr) =
      ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) uR :=
    (D6.Bridge.sa_congr hd).trans (Inst.Model.Ledger.ext_sa D.lT (fun m i => led t ν i m) uR).symm
  have eb : Inst.Model.Ledger.sb (P6.dv ρ W Dr) =
      ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) uR :=
    (D6.Bridge.sb_congr hd).trans (Inst.Model.Ledger.ext_sb D.lT (fun m i => led t ν i m) uR).symm
  have el : Inst.Model.Ledger.Rlo (P6.dv ρ W Dr) =
      ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) uR :=
    (D6.Bridge.Rlo_congr hd).trans
      (Inst.Model.Ledger.ext_Rlo D.lT (fun m i => led t ν i m) uR).symm
  have eh : Inst.Model.Ledger.Rhi (P6.dv ρ W Dr) =
      ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) uR :=
    (D6.Bridge.Rhi_congr hd).trans
      (Inst.Model.Ledger.ext_Rhi D.lT (fun m i => led t ν i m) uR).symm
  intro f hf
  have hf4 : f ∈ [Aff.slot (j + 0) - (P6.Row.ofDigits Dr).a,
      Aff.slot (j + 1) - (P6.Row.ofDigits Dr).b, Aff.slot (j + 2) - (P6.Row.ofDigits Dr).Rlo,
      Aff.slot (j + 3) - (P6.Row.ofDigits Dr).Rhi] := hf
  rcases List.mem_cons.mp hf4 with rfl | hf4
  · rw [Aff.value_sub, Aff.value_slot, hE.1, va, ea, sub_self]
  rcases List.mem_cons.mp hf4 with rfl | hf4
  · rw [Aff.value_sub, Aff.value_slot, hE.2.1, vb, eb, sub_self]
  rcases List.mem_cons.mp hf4 with rfl | hf4
  · rw [Aff.value_sub, Aff.value_slot, hE.2.2.1, vl, el, sub_self]
  · obtain rfl := List.mem_singleton.mp hf4
    rw [Aff.value_sub, Aff.value_slot, hE.2.2.2, vh, eh, sub_self]

/-- **Groups 5 and 6, one norm.** jW, jP: the first of the norm's nine slots of sums and of its
seven slots of products. -/
theorem seventeen_zero (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (N : NormWords v D) {ν : ℕ}
    (hν : ν < D.nNu) {Dp : ℕ → Aff} (hDp : digitsAt v "P_V" ν = some Dp) (jW jP : ℕ)
    (hI : ∀ k, k < 17 → ∀ i, i < 2 ^ D.lT →
      idnVal D t (fun _ _ => 0) (fun _ => 0) (.jn k ν i) = 0)
    (hW : ∀ s, s < 9 → W.slot (jW + s) = wHat D t ν uP s)
    (hP : ∀ j, j < 7 → W.slot (jP + j) = pHat D t ν uP j) :
    (∀ f ∈ P6.carries (P6.Row.ofDigits Dp) Dp (fun s => Aff.slot (jW + s)), f.value ρ W = 0) ∧
      ∀ f ∈ P6.lines (P6.Row.ofDigits Dp) (fun j => Aff.slot (jP + j)) (epsOf v.y ν) (twoM v ν),
        f.value ρ W = 0 := by
  have hd := (digits_value F T3 ν).1 Dp hDp
  have heps : ρ.val (epsOf v.y ν) = ((npOf D ν).eps : K) := by
    unfold epsOf
    rw [F.num.ofNat, ← N.eps ν hν]
    norm_cast
  have htwo : (twoM v ν).value ρ W = 2 ^ ((npOf D ν).M + 1) := by
    unfold twoM
    rw [Aff.value_ofConst, F.num.pw, N.M ν hν]
  refine D6.Bridge.forms_of_idnP ρ W Dp (fun s => Aff.slot (jW + s)) (fun j => Aff.slot (jP + j))
    (npOf D ν) (epsOf v.y ν) (twoM v ν) heps htwo fun k => ?_
  by_cases hk : 17 ≤ k
  · exact Inst.Model.Ledger.idnP_of_le _ _ _ _ hk
  · rw [D6.Bridge.idnP_congr (npOf D ν) (Ws' := wHat D t ν uP) _ _ k
        (fun s hs => (Aff.value_slot ρ W _).trans (hW s hs)),
      D6.Bridge.idnP_congr_D (npOf D ν) _ _ hd k,
      D6.Bridge.idnP_congr_pv (npOf D ν) _ _ (pv' := pHat D t ν uP) k
        (fun j hj => (Aff.value_slot ρ W _).trans (hP j hj)), ← idnAt_eq]
    exact Blocks.ext_zero_of_forall (fun X hX => hI k (by omega) X hX) uP

/-- **GROUPS 4 TO 6: every form of the list is worth 0.** hI: the library's seventeen identities of
every norm at every position. hW, hP, hE: what the slots hold. -/
theorem rows_zero (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (N : NormWords v D)
    (hNI : v.y.NI = D.nNu) {H : Heard}
    (hI : ∀ ν, ν < D.nNu → ∀ k, k < 17 → ∀ i, i < 2 ^ D.lT →
      idnVal D t (fun _ _ => 0) (fun _ => 0) (.jn k ν i) = 0)
    (hW : ∀ ν, ν < D.nNu → ∀ s, s < 9 → W.slot (H.sW + 9 * ν + s) = wHat D t ν uP s)
    (hP : ∀ ν, ν < D.nNu → ∀ j, j < 7 → W.slot (H.sPv + 7 * ν + j) = pHat D t ν uP j)
    (hE : ∀ ν, ν < D.nNu →
      W.slot (H.tV.sEnd + 4 * ν + 0) = ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) uR ∧
      W.slot (H.tV.sEnd + 4 * ν + 1) = ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) uR ∧
      W.slot (H.tV.sEnd + 4 * ν + 2) = ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) uR ∧
      W.slot (H.tV.sEnd + 4 * ν + 3) = ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) uR) :
    ∀ l, rowsForms v H = some l → ∀ f ∈ l, f.value ρ W = 0 := by
  intro l h f hf
  obtain ⟨i, hi, Dr, Dp, hDr, hDp, hc⟩ := rowsForms_all h hf
  have hν : i < D.nNu := hNI ▸ hi
  rcases hc with hc | hc | hc
  · exact four_zero F T3 hDr _ (hE i hν) f hc
  · exact (seventeen_zero F T3 N hν hDp _ _ (hI i hν) (hW i hν) (hP i hν)).1 f hc
  · exact (seventeen_zero F T3 N hν hDp _ _ (hI i hν) (hW i hν) (hP i hν)).2 f hc

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.digits_value
#print axioms OnBytes.Road.K4.W.four_zero
#print axioms OnBytes.Road.K4.W.seventeen_zero
#print axioms OnBytes.Road.K4.W.rows_zero
