-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKHas
import Johnson.Desc.K12.Law.OwnSeatLaw
/-
Johnson/Desc/K12/Law/AccKOwn.lean: accK's YES AT THE OWN MASK's ARM: fM := orc1 c, THE LETTER THAT READS THE FIRST MASK's TABLE OFF THE CHAIN's FIRST MESSAGE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  alone_at            what «aloneAt p t = some true» gives at gpOf's D at the place's first stage
  accK_yes_real_own   accK_yes_real's premises (Johnson/Desc/K12/Law/AccKHas.lean) · p.nums.ownMask = true · ownTieOk p · t0.mask = none (the record in front names no mask) · THE BATCHING's RETURN ON r0 AS SHOWN (an equation: what a run computes) · AT THE RECORD tG BEHIND IT THE TWO TESTS THAT A PROGRAM OF THIS PROJECT THAT IS NOT IN THIS REPOSITORY PRINTS: lastOk p tG = true (Johnson/Desc/K12/Law/OwnSeat.lean: the mask's tree is the last of D.ts) · aloneAt p tG = some true (Johnson/Desc/K12/Law/AloneOk.lean: no member of the group shares it) ⇒ the place's chain c ∧ ∃ e row Ly S' D, gpL's yes ∧ FrontK … ∧ ∃ W0, DeepK D W0 (orc1 c) ∧ ∃ τ that shows just rs' (the sealed digests apart), accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t (orc1 c)) τ = true ∧ THE VIEW's COLUMNS, AS MANY AS THE STEP WANTS, ARE τ's OWN WRITTEN COLUMNS (cols.take … = colsOf … (srcK p c (blOf c τ) D.ts …))
BY: tables_of_view_own (Johnson/Desc/K12/Law/TabsView.lean) and accK_yes_bool (Johnson/Desc/K12/Law/CanonLaw.lean).
NO PROPOSITION IS LEFT AS A PREMISE: numbers of the place · Booleans with code · the step's yes · one equation that a run computes (bat … = .ok (row, Ly, S'): by bat_unique (Johnson/Desc/K12/Law/TopD.lean) there is one such return). AS REPORTED, NOT SHOWN HERE, lastOk AND aloneOk HAVE RUN true, their controls false, AT THE ONE PLACE OF THE FOUR WHERE ownMask IS true (a run's word, at both stored proofs: THAT RUN's BLOCK IS ANOTHER TEXT OF THE PARTS THAN THIS LIBRARY's, AND THESE TESTS READ IT: they are asked at the record tG that the ridden front and batching make, and where the record names no mask gpOf calls the ground's own text; no line prints that the run's tG is this theorem's).
ALL THAT Johnson/Desc/K12/Law/AccKHas.lean's HEAD SAYS AGAINST ITSELF UNDER (2)-(5) STANDS HERE TOO: one accepting transcript is not a prover that is not doomed · the bits of work are laid as zeros · the transcript is FITTED TO THE VIEW: its tables are made off the opened columns: nothing is said of what a prover committed to · the oracle model · no completeness · NO SENTENCE ON BITS TO A PERSON.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk ownTieOk aloneOk canonOk logOk lastOk aloneAt
  plainAt last_of_ok)

theorem alone_at (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (hD : gpOf p t a L = some D) (h : aloneAt p t = some true) :
    aloneOk D = true := by
  unfold aloneAt plainAt at h
  rw [hs, hp] at h
  dsimp only at h
  rw [hD] at h
  exact Option.some.inj h


theorem accK_yes_real_own (X : Letters) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (t0 : T12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hnz : nzOk p = true) (hdeal : dealOk p = true) (htie : tieOk p = true)
    (hlog : logOk p = true) (ho : p.nums.ownMask = true) (hown : ownTieOk p = true) (F : ℕ)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (hmask : t0.mask = none)
    (hlast : lastOk p { t0 with st := SB, pass := .claim rowB LB } = true)
    (halone : aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO), DeepK D W0 (orc1 c) ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t (orc1 c)) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t (orc1 c) (blOf c τ) z).1
                    (wAt c W0 D.fresh.t (orc1 c) (blOf c τ) z).2 x) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, _⟩ :=
    k12_step_accH X p he ha t0 hp F tE (r0 :: rs') cols n hstep
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, ?_⟩
  obtain ⟨hfit, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, hb, hg⟩ := k12_guards p he t0 tE _ _ hp hdec
  obtain rfl : noDigest r0 = r := (List.cons.inj hr).1
  obtain ⟨D, hD, hok⟩ := H2K.First.gpOk_inv p _ a rest row L e1 rfl hg
  have hfr : FrontK p t0 a r0 e row L S' D := ⟨hb, hg, hD⟩
  refine ⟨e, row, L, S', D, hok, hfr, ?_⟩
  cases bat_unique _ _ _ _ _ _ _ hbB hb
  have hl := last_of_ok p _ a rest rowB LB D e1 rfl hD hmask hlast
  have hal := alone_at p _ a rest rowB LB D e1 rfl hD halone
  obtain ⟨W0, τ₀, hdeep, htab⟩ :=
    H2K.First.tables_of_view_own p F a rest c w0 l _ rowB LB D hp hdeal htie e1 e5 e2 e4 hD hok ho
      hown hl hal r0 rs' cols hfit
  refine ⟨W0, hdeep, ?_⟩
  have hro := K12.k12_rounds (Cl := Unit) guardedProximityTestParts p hp
  cases hrd : (proximityTestKind guardedProximityTestParts p : Blk').rounds with
  | nil =>
    have h1 := hfit.1
    rw [hrd] at h1
    cases h1
  | cons d0 ds =>
    rw [hrd] at hro
    obtain ⟨τ, t1, _, t3, t4⟩ := accK_yes_bool p F t0 r0 c D.ts W0 D.fresh.t (orc1 c)
      (fun _ _ h => h) w0 l d0 ds hp hnz e2 e4 hro hlog rs' cols hcan tE n hstep τ₀ htab
    exact ⟨τ, t1, t3, by rw [← hrd]; exact t4⟩

end H2K.JointK

#print axioms H2K.JointK.accK_yes_real_own
