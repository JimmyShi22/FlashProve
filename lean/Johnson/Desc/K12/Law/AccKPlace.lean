-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.CanonLaw
import Johnson.Desc.K12.Law.AccKFront
/-
Johnson/Desc/K12/Law/AccKPlace.lean: THE JOIN: AT A PLACE AND A VIEW WHERE Block.step OF proximityTestKind guardedProximityTestParts p SAYS YES AND FIVE BOOLEANS HOLD, accK HAS A YES, AT THE LEMMA's OWN LETTERS: GIVEN «THE VIEW's COLUMNS ARE COLUMNS OF TABLES» AS ONE NAMED PROPOSITION (TablesOfView). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  TablesOfView     A PROPOSITION, NOT A THEOREM HERE: the statement asked of other files («tables_of_view»), to the letter
  accK_yes_place   TablesOfView → early · answers = 1 · planOk · nzOk · dealOk · tieOk · logOk · canonOk of the rounds behind "BAT" · a yes of Block.step at (r0 :: rs', cols) ⇒ the place's chain c (k12_step_accH's five conjuncts) ∧ ∃ e row Ly S' D, gpL's yes ∧ FrontK p t0 a r0 e row Ly S' D ∧ ∃ W0 fM, DeepK D W0 fM ∧ ∃ τ that shows just rs' (the sealed digests apart), accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = true ∧ THE VIEW's COLUMNS, AS MANY AS THE STEP WANTS, ARE τ's OWN WRITTEN COLUMNS (cols.take … = colsOf … (srcK p c (blOf c τ) D.ts …))
THE RIDER STANDS: one accepting transcript is not a prover that is not doomed; the tests of work pass because the bits of work are laid as zeros; the oracle model; nothing on a view from bytes.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT (accK_yes_place TAKES TablesOfView AS A PREMISE): nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Onto (orcsOf)
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk canonOk logOk)

/-- The statement asked of «tables_of_view». -/
def TablesOfView : Prop :=
  ∀ (p : P12) (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s : Sg}
    (c : Chain s) (w0 : WR) (ws : List WR) (t : T12) (row : GroupRow) (L : GroupLayout) (D : Plain),
    (proximityTestKind guardedProximityTestParts p : Blk').planOk = true → dealOk p = true → tieOk p = true →
    p.nums.stages = a :: rest → stagesOf c = p.nums.stages →
    writtenOf p.nums = some (w0 :: ws) → c.rds = ws.map WR.rd →
    gpOf p t a L = some D → H2K.First.ok (gpL p a row D) = true →
    ∀ (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
    (proximityTestKind guardedProximityTestParts p : Blk').Fits F (r0 :: rs') cols →
    ∃ (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO) (τ₀ : Tr (PQ.uL (ckP .two) c.rds)),
      DeepK D W0 fM ∧ (∀ m m', orc1 c m = orc1 c m' → fM m = fM m') ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ₀) D.ts fun z x =>
            colW (wAt c W0 D.fresh.t fM (blOf c τ₀) z).1 (wAt c W0 D.fresh.t fM (blOf c τ₀) z).2 x)


theorem accK_yes_place (H : TablesOfView) (X : Letters) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (t0 : T12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hnz : nzOk p = true) (hdeal : dealOk p = true) (htie : tieOk p = true)
    (hlog : logOk p = true) (F : ℕ) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1
                    (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, _⟩ :=
    k12_step_accH X p he ha t0 hp F tE (r0 :: rs') cols n hstep
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, ?_⟩
  obtain ⟨hfit, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, hb, hg⟩ := k12_guards p he t0 tE _ _ hp hdec
  obtain rfl : noDigest r0 = r := (List.cons.inj hr).1
  obtain ⟨D, hD, hok⟩ := H2K.First.gpOk_inv p _ a rest row L e1 rfl hg
  refine ⟨e, row, L, S', D, hok, ⟨hb, hg, hD⟩, ?_⟩
  obtain ⟨W0, fM, τ₀, hdeep, hfM, htab⟩ :=
    H p F a rest c w0 l _ row L D hp hdeal htie e1 e5 e2 e4 hD hok r0 rs' cols hfit
  refine ⟨W0, fM, hdeep, ?_⟩
  have hro := K12.k12_rounds (Cl := Unit) guardedProximityTestParts p hp
  cases hrd : (proximityTestKind guardedProximityTestParts p : Blk').rounds with
  | nil =>
    have h1 := hfit.1
    rw [hrd] at h1
    cases h1
  | cons d0 ds =>
    rw [hrd] at hro
    obtain ⟨τ, t1, _, t3, t4⟩ := accK_yes_bool p F t0 r0 c D.ts W0 D.fresh.t fM hfM w0 l d0 ds hp
        hnz
      e2 e4 hro hlog rs' cols hcan tE n hstep τ₀ htab
    exact ⟨τ, t1, t3, by rw [← hrd]; exact t4⟩

end H2K.JointK

#print axioms H2K.JointK.accK_yes_place
