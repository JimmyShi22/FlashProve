-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.CanonOk
import Johnson.Desc.K12.Law.RoundIsOf
/-
Johnson/Desc/K12/Law/CanonLaw.lean: WHAT A YES OF canonOk AND OF logOk GIVES (Johnson/Desc/K12/Law/CanonOk.lean): CanonK and LogK, the two new premises of accK_yes_view (Johnson/Desc/K12/Law/RoundIsOf.lean); and that theorem with the two Booleans in their place. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  canon_of_ok · log_of_ok · accK_yes_bool
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Onto (Canon orcsOf)
open H2K.Pub (WR writtenOf)
open H2K.First (nzOk canonOk canonE logOk logOn ok)

theorem canon_of_ok (rs : List Fmt.RoundView) (h : canonOk rs = true) : CanonK rs := by
  intro r hr x hx
  unfold canonOk at h
  rw [List.all_eq_true] at h
  have h1 := h r hr
  rw [List.all_eq_true] at h1
  have h2 := h1 x hx
  unfold canonE at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨h2.1.1, h2.1.2, h2.2⟩

theorem log_of_ok (p : P12) (ds : List Fmt.DeclaredRound) (hd : H2U.roundsOfNums p.nums = some ds)
    (h : logOk p = true) : LogK ds := by
  unfold logOk at h
  rw [hd, Option.any_some] at h
  unfold ok logOn at h
  rw [List.all_map, List.all_eq_true] at h
  intro d hdm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hdm
  have := h (d, i) (by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hi)
  exact of_decide_eq_true this

/-- accK_yes_view with the two Booleans in the place of LogK and CanonK. -/
theorem accK_yes_bool (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W0 : ℕ → WO) (ft : ℕ) (fM : H2K.Pub.Msg1 c → WO)
    (hfM : ∀ m m', orc1 c m = orc1 c m' → fM m = fM m')
    (w0 : WR) (ws : List WR) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true)
    (hwr : writtenOf p.nums = some (w0 :: ws)) (hrds : c.rds = ws.map WR.rd)
    (hro : H2U.roundsOfNums p.nums = some (d0 :: ds)) (hlog : logOk p = true)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (τ₀ : Tr (PQ.uL (ckP .two) c.rds))
    (htab : cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
      colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
        (srcK p c (blOf c τ₀) ts fun z x =>
          colW (wAt c W0 ft fM (blOf c τ₀) z).1 (wAt c W0 ft fM (blOf c τ₀) z).2 x)) :
    ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
      orcsOf c.rds τ = orcsOf c.rds τ₀ ∧ accK p F t0 r0 c ts (wAt c W0 ft fM) τ = true ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ) ts fun z x =>
            colW (wAt c W0 ft fM (blOf c τ) z).1
              (wAt c W0 ft fM (blOf c τ) z).2 x) :=
  accK_yes_view p F t0 r0 c ts W0 ft fM hfM w0 ws d0 ds hplan hnz hwr hrds hro
    (fun d hd => log_of_ok p _ hro hlog d (List.mem_cons_of_mem _ hd)) rs' cols
    (canon_of_ok rs' hcan) tE n hstep τ₀ htab

end H2K.JointK

#print axioms H2K.JointK.canon_of_ok
#print axioms H2K.JointK.log_of_ok
#print axioms H2K.JointK.accK_yes_bool
