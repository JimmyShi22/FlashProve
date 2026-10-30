-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/AccKIff.lean: what the verifier `accK` of the lemma on the proximity test comes
down to.

At the written view the two tests on form of `Block.step` hold, whatever the transcript. So a yes of
`accK` (Johnson/Desc/K12/Law/K12Lemma.lean) is the decision's yes and the tests of work. Statements
and proofs.
Main names:
  `FormK`: the premises, named: four tests on the plan (the block's own, `nzOk`, `dealOk`, `tieOk`);
    the round "BAT" as shown fits its declared round; D is the value of `gpOf` at a record, with the
    yes of the clauses `gpL` there; `DeepK` (depths and widths of the written trees of the group);
    the chain is the place's.
  `fits_written`: under `FormK`, `Block.Fits` (Johnson/Top/H0/StepLaws/StepLaws.lean: the two tests
    of `Block.step`, on the rounds and on the columns) holds at the written view of every
    transcript, by `fit_of_ok` (Johnson/Desc/K12/Law/NzLaw.lean), `view_wide_deep`
    (Johnson/Desc/K12/Law/ViewWide.lean) and `kpw_colsOf` (Johnson/Desc/K12/Law/ViewK.lean).
  `accK_iff`: under `FormK`, `accK` says yes at τ if and only if the block's decision says yes at
    the written view of τ and all tests of work on τ pass.
Limits: It does not say that the decision says yes at any transcript: the lemma on the proximity
test is still not shown to have a yes. The record t at which D is made and the record t0 of
`accK_iff` are two letters that nothing ties here; whoever lays `accK_iff` beside `k12_lemma` takes
for t the record behind the batching (`FrontK.made`). Two premises are on letters: that r0 fits the
declared round "BAT", and `DeepK`. `nzOk`, `dealOk` and `tieOk` were evaluated at the four proximity
tests of the two stored example proofs, the full-size one and the smaller one: true at each, and
false at spoiled inputs [the prints are not in this library]. No statement and no proof of this file
reaches a routine that runs in a context of the program `verify-on-bytes` (`OnBytes.Ctx`,
`OnBytes.Blk`, `OnBytes.Chan`); plain functions of that program, some with names that begin with
`Blk.`, are reached. No soundness is claimed. Nothing here is about hiding.

-/
import Johnson.Desc.K12.Law.ViewWide
import Johnson.Desc.K12.Law.NzLaw
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk tied_of_ok view_wide_deep)
open H2K.Sw (kpw)

/-- The premises. The record t is the one at which D is made; beside `k12_lemma` it is the record
behind the batching. -/
structure FormK (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) {s : Sg} (c : Chain s)
    (w0 : WR) (ws : List WR) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound) (r0 : Fmt.RoundView) (t : T12)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO) :
    Prop where
  plan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true
  nz : nzOk p = true
  deal : dealOk p = true
  tie : tieOk p = true
  stages : p.nums.stages = a :: rest
  chain : stagesOf c = p.nums.stages
  written : writtenOf p.nums = some (w0 :: ws)
  rds : c.rds = ws.map WR.rd
  rounds : H2U.roundsOfNums p.nums = some (d0 :: ds)
  bat : roundsFit [d0] [r0] = true
  made : gpOf p t a L = some D
  gp : H2K.First.ok (gpL p a row D) = true
  deep : DeepK D W0 fM

theorem rvSL_cast {l l' : List PQ.RD} (h : l = l') (τ : Tr (PQ.uL (ckP .two) l)) :
    ∃ τ' : Tr (PQ.uL (ckP .two) l'), PQ.rvSL (ckP .two) l τ = PQ.rvSL (ckP .two) l' τ' := by
  subst h
  exact ⟨τ, rfl⟩

/-- The two tests of `Block.step` on form hold at the written view of every transcript. -/
theorem fits_written {p : P12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {s : Sg} {c : Chain s}
    {w0 : WR} {ws : List WR} {d0 : Fmt.DeclaredRound} {ds : List Fmt.DeclaredRound} {r0 : Fmt.RoundView} {t : T12}
    {row : GroupRow} {L : GroupLayout} {D : Plain} {W0 : ℕ → WO} {fM : H2K.Pub.Msg1 c → WO}
    (H : FormK p a rest c w0 ws d0 ds r0 t row L D W0 fM) (F : ℕ)
    (τ : Tr (PQ.uL (ckP .two) c.rds)) :
    (proximityTestKind guardedProximityTestParts p : Blk').Fits F (r0 :: PQ.rvSL (ckP .two) c.rds τ)
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
        (srcK p c (blOf c τ) D.ts fun z x =>
          colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1 (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x)) :=
              by
  have hr : (proximityTestKind guardedProximityTestParts p : Blk').rounds = d0 :: ds :=
    (Option.some.inj ((K12.k12_rounds guardedProximityTestParts p H.plan).symm.trans H.rounds))
  refine ⟨?_, ?_⟩
  · obtain ⟨τ', hτ⟩ := rvSL_cast H.rds τ
    rw [hr, hτ]
    exact H2K.Fit.fit_of_ok p d0 ds w0 ws H.rounds H.written H.nz r0 H.bat τ'
  · obtain ⟨w0', w', e1, _, e3, _⟩ := tied_of_ok p a rest H.stages H.tie
    obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (e1.symm.trans H.written))
    have hlen : (laidS p).length = ((PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)).length := by
      rw [List.length_map, rvSL_length, H.rds, List.length_map, e3]
    have hk : (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
      (srcK p c (blOf c τ) D.ts fun z x =>
        colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1
          (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x)).map kpw =
        (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
          ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn))).flatMap id :=
      kpw_colsOf _ _ fun i grp wt hg hwt =>
        view_wide_deep guardedProximityTestParts p H.plan F a rest H.stages H.deal H.tie c
          H.chain w0' w' H.written H.rds t row L D H.made H.gp W0 fM H.deep (blOf c τ) r0.drawn
          ((PQ.rvSL (ckP .two) c.rds τ).map fun x : Fmt.RoundView => x.drawn) hlen i grp wt hg hwt
    have hl : (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
      (srcK p c (blOf c τ) D.ts fun z x =>
        colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1
          (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x)).length =
        ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: PQ.rvSL (ckP .two) c.rds τ)).length := by
      have := congrArg List.length hk
      rwa [List.length_map] at this
    rw [← hl, List.take_length]
    exact beq_iff_eq.2 hk

/-- A yes of `accK` is the decision's yes at the written view, and the tests of work. -/
theorem accK_iff {p : P12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {s : Sg} {c : Chain s}
    {w0 : WR} {ws : List WR} {d0 : Fmt.DeclaredRound} {ds : List Fmt.DeclaredRound} {r0 : Fmt.RoundView} {t : T12}
    {row : GroupRow} {L : GroupLayout} {D : Plain} {W0 : ℕ → WO} {fM : H2K.Pub.Msg1 c → WO}
    (H : FormK p a rest c w0 ws d0 ds r0 t row L D W0 fM) (F : ℕ) (t0 : T12)
    (τ : Tr (PQ.uL (ckP .two) c.rds)) :
    accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = true ↔
      (∃ tE, (proximityTestKind guardedProximityTestParts p : Blk').decide t0 ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map noDigest)
        ((proximityTestKind guardedProximityTestParts p : Blk').shown F (r0 :: PQ.rvSL (ckP .two) c.rds τ)
          (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
            ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
            (srcK p c (blOf c τ) D.ts fun z x =>
              colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1
                (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x))) = .ok tE) ∧
      PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true := by
  unfold accK
  rw [Bool.and_eq_true]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h
    split at h
    · rename_i x hx
      exact ⟨x.1, ((step_iff F _ t0 x.1 _ _ x.2).1 hx).2.1⟩
    · cases h
  · rintro ⟨tE, hd⟩
    rw [(step_iff F (proximityTestKind guardedProximityTestParts p : Blk') t0 tE _ _ _).2 ⟨fits_written H F τ, hd, rfl⟩]

end H2K.JointK
