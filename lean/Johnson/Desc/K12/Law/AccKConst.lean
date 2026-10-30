-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKHas
/-
Johnson/Desc/K12/Law/AccKConst.lean: accK's YES, STATED AT THE LETTER THAT IS IN FACT GIVEN: fM := THE CONSTANT fun _ => W0 D.fresh.t: THE FIRST MASK's TABLE FIXED OUTSIDE THE GAME. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
WHY: in accK_yes_place | accK_yes_real «∃ fM» hides that the fM handed over is a constant: a spender at a place where the mask is the test's own cannot see that it is of no use to him.
  tables_of_view_const   tables_of_view (Johnson/Desc/K12/Law/TabsView.lean), ITS PROOF LINE FOR LINE (cut out by program; two lines turned), with the constant in the statement
  accK_yes_real_const    accK_yes_real's premises ⇒ … ∃ W0, DeepK D W0 (fun _ => W0 D.fresh.t) ∧ ∃ τ that shows just rs' (the sealed digests apart), accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fun _ => W0 D.fresh.t) τ = true ∧ THE VIEW's COLUMNS, AS MANY AS THE STEP WANTS, ARE τ's OWN WRITTEN COLUMNS (cols.take … = colsOf … (srcK p c (blOf c τ) D.ts …))
WHICH ARM IS THE LAW's: where p.nums.ownMask = false (the mask came in an earlier message) the constant is the law's own letter: THIS FILE · where p.nums.ownMask = true the law is spent at fM := orc1 c: Johnson/Desc/K12/Law/AccKOwn.lean. By a print of a program of ours, not in this repository, ownMask is true at one of the four places of the stored proofs (a run's word).
ALL THAT Johnson/Desc/K12/Law/AccKHas.lean's HEAD SAYS AGAINST ITSELF UNDER (2)-(5) STANDS HERE TOO.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf kk sgOf chainFrom Letters)
open H2K.Onto (Orcs orcsOf tr_with)

theorem tables_of_view_const (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s :
    Sg}
    (c : Chain s) (w0 : WR) (ws : List WR) (t : T12) (row : GroupRow) (L : GroupLayout) (D : Plain)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hs : p.nums.stages = a :: rest) (hst : stagesOf c = p.nums.stages)
    (hw : writtenOf p.nums = some (w0 :: ws)) (hr : c.rds = ws.map WR.rd)
    (hD : gpOf p t a L = some D) (hok : H2K.First.ok (gpL p a row D) = true)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : (proximityTestKind guardedProximityTestParts p : Blk').Fits F (r0 :: rs') cols) :
    ∃ (W0 : ℕ → WO) (τ₀ : Tr (PQ.uL (ckP .two) c.rds)),
      DeepK D W0 (fun _ : H2K.Pub.Msg1 c => W0 D.fresh.t) ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ₀) D.ts fun z x =>
            colW (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ₀) z).1
              (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ₀) z).2 x) := by
  have hm := made_of p t a L D hD
  have hR := ready_of p F a rest t row L D hplan hdeal htie hs hD hok (r0 :: rs') cols hfit
  obtain ⟨W0, hW0⟩ := book_tables hR (WR.rd w0)
  have hat : ∀ z ∈ D.ts, PQ.posN (W0 z).1.tree = 2 ^ logAt D.book z ∧
      PQ.colW (W0 z).1.tree = widthAt D.book z := by
    intro z hz
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
    exact tab_deep p a row D _ hok i z hi _ (hW0 i z hi)
  have hfr := fresh_in p t a L D hm
  have hdeep : DeepK D W0 (fun _ : H2K.Pub.Msg1 c => W0 D.fresh.t) := by
    refine ⟨fun i => ?_, fun _ => ?_, fun _ _ _ => rfl, fun z hz _ => (hat z hz).2,
      fun _ => (hat _ hfr).2⟩
    · rw [← (keyAt_of (F := 0) (hm.mem i).2).2]
      exact (hat _ (mem_in p t a L D hm i)).1
    · rw [← (keyAt_of (F := 0) hm.fresh).2]
      exact (hat _ hfr).1
  obtain ⟨τd, _⟩ := tr_with c.rds (dOrcs c.rds)
  obtain ⟨b, _, hb⟩ := tabs_join p F a rest c w0 ws D hdeal htie hs hst hw hr (r0 :: rs') cols hfit
    hR W0 hW0 (H2K.Pub.msg1 c (blOf c τd))
  refine ⟨W0, c.trL b, hdeep, ?_⟩
  rw [blOf_trL]
  have hwA : wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) b = W0 := Function.update_eq_self _ _
  rw [hwA]
  exact hb

end H2K.First

namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk ownTieOk aloneOk canonOk logOk)


theorem accK_yes_real_const (X : Letters) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (t0 : T12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hnz : nzOk p = true) (hdeal : dealOk p = true) (htie : tieOk p = true)
    (hlog : logOk p = true) (F : ℕ)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO), DeepK D W0 (fun _ : H2K.Pub.Msg1 c => W0 D.fresh.t) ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fun _ => W0 D.fresh.t) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ) z).1
                    (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ) z).2 x) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, _⟩ :=
    k12_step_accH X p he ha t0 hp F tE (r0 :: rs') cols n hstep
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, ?_⟩
  obtain ⟨hfit, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, hb, hg⟩ := k12_guards p he t0 tE _ _ hp hdec
  obtain rfl : noDigest r0 = r := (List.cons.inj hr).1
  obtain ⟨D, hD, hok⟩ := H2K.First.gpOk_inv p _ a rest row L e1 rfl hg
  have hfr : FrontK p t0 a r0 e row L S' D := ⟨hb, hg, hD⟩
  refine ⟨e, row, L, S', D, hok, hfr, ?_⟩
  obtain ⟨W0, τ₀, hdeep, htab⟩ :=
    H2K.First.tables_of_view_const p F a rest c w0 l _ row L D hp hdeal htie e1 e5 e2 e4 hD hok
      r0 rs' cols hfit
  refine ⟨W0, hdeep, ?_⟩
  have hro := K12.k12_rounds (Cl := Unit) guardedProximityTestParts p hp
  cases hrd : (proximityTestKind guardedProximityTestParts p : Blk').rounds with
  | nil =>
    have h1 := hfit.1
    rw [hrd] at h1
    cases h1
  | cons d0 ds =>
    rw [hrd] at hro
    obtain ⟨τ, t1, _, t3, t4⟩ := accK_yes_bool p F t0 r0 c D.ts W0 D.fresh.t
      (fun _ => W0 D.fresh.t) (fun _ _ _ => rfl) w0 l d0 ds hp hnz e2 e4 hro hlog rs' cols hcan tE
          n hstep τ₀ htab
    exact ⟨τ, t1, t3, by rw [← hrd]; exact t4⟩

end H2K.JointK

#print axioms H2K.First.tables_of_view_const
#print axioms H2K.JointK.accK_yes_real_const
