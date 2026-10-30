-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormAt.lean: one stage of a proximity test that is not the last, on the form's
side, at the very rounds, group and states of `bodyAll` (Johnson/Prover/Link/BodyAll.lean): the
form's half of the step of the induction over the stages (`body_yes_of`,
Johnson/Prover/Link/BodyYes.lean).

Main names (namespace `Johnson.Prover.Link`).
  `hread_of`   `read_of_inv` (Johnson/Prover/Link/FormClose.lean) at the fold's rounds as a list
  `form_at`   the plan from this stage on (`PlanFrom`) · the declared rounds ask the sorts that are
      shown (`SortsFrom`) · the samples fit (`FitFrom`) · the form's half of the invariant
      (`FormInv`): then the step's plan · `StageYes` · the states `sT1` and `sT3` are the written
      terms `foldT` and `stepT3` · `StepDone` at the shown rounds and the dealt group
  `formNext_at`, `formLast_at`   behind the stage: `FormInv` again, at `bodyAll`'s own column (with
      `LayAt` and `SeatP`); or `LastForm` in front of the last stage
  `formRides_at`   the three public clauses hold again behind the stage
  `formLeft_at`   nothing is left untested behind the stage, where nothing was in front

An assembly of calls. Limits. Every premise is asked. Nothing on soundness; nothing on what a value
that is sent discloses or does not disclose.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormLast
import Johnson.Prover.Link.BodyCuts
import Johnson.Prover.Link.BodySorts
import Johnson.Prover.Link.BodyHelps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- `read_of_inv` at the fold's rounds as a list. -/
theorem hread_of {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree}
    (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr) (rsF : List Fmt.RoundView)
    (fitF : roundsFit ((l.take (1 + cur.k)).map (·.1)) rsF = true) (rC : Fmt.RoundView)
    (hx : ∀ x ∈ rC.drawn.poss, x < 2 ^ (sgOf cur).C.a) (D : Taken) :
    ReadFront
      (swIn p n last dS dC (foldT t row L c (n.code, n.maskCode) id (rsF.map noDigest)) rC
        [(Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col x)]
        (foldOut t row L c id (rsF.map noDigest)) t.st.groups.size D)
      (Positions.ofDraws (sgOf cur).C.a rC.drawn.poss) tN tr := by
  have hlen : (rsF.map noDigest).length = 1 + c.k := by
    rw [List.length_map, Sound.roundsFit_len _ _ fitF, length_of_foldCut Pl.cutF]
  obtain ⟨rE, rR, hrs⟩ : ∃ rE rR, rsF.map noDigest = rE :: rR := by
    cases h : rsF.map noDigest with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons rE rR => exact ⟨rE, rR, rfl⟩
  have hR : rR.length = c.k := by
    rw [hrs, List.length_cons] at hlen
    omega
  rw [hrs]
  exact read_of_inv Pl I rE rR hR rC hx D

/-- **The form's half of the induction's step, at `bodyAll`'s own pieces.** -/
theorem form_at (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (P : PS) {next : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
    {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout} {c : IoppStage} {nn : ℕ × ℕ}
    {id tN : ℕ} {tr : Tree} (hP : PlanFrom p (next :: rest) j cur l t.st.codes)
    (hS : SortsFrom l cur (next :: rest)) (hF : FitFrom D l o)
    (I : FormInv p j cur l t col row L c nn id tN tr) :
    ∃ n dS dC Dk x row',
      StepPlan p t.st.codes j cur next rest.isEmpty l c n dS dC ∧ nn = (n.code, n.maskCode) ∧
      StageYes p K rest j cur next l o t P col D ∧
      sT1 p K j cur l o t P (rowOf t) D =
        foldT t row L c nn id ((sRF K j cur o P (rowOf t) D).map noDigest) ∧
      sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D =
        stepT3 p n rest.isEmpty dS dC
          (foldT t row L c nn id ((sRF K j cur o P (rowOf t) D).map noDigest))
          (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
            D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
          (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size Dk
          tN row' ∧
      StepDone (sgOf cur) (sgOf next) p n rest.isEmpty dS dC
        (foldT t row L c nn id ((sRF K j cur o P (rowOf t) D).map noDigest))
        (noDigest ⟨[], D (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩)
        (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
        (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size j cur
        next tN (ofE (sAns p K j cur next l o t P (rowOf t) D)) Dk x row' := by
  obtain ⟨⟨c', n, dS, dC, Pl⟩, -, -, -, -⟩ := hP
  obtain rfl : c = c' := Option.some.inj (I.front.stage.symm.trans Pl.stage)
  obtain rfl : nn = (n.code, n.maskCode) := Option.some.inj (I.front.next.symm.trans Pl.idx)
  have hrow : rowOf t = row := rowOf_claim I.front.pass
  have fitF := fitF_at K j cur next rest l o P (rowOf t) D hF hS Pl.hk
  have fitS := fitS_at p K j cur next rest l o t P (rowOf t) D hF hS Pl.hk
  rw [Pl.cutS, ← H2K.Onto.roundsFit_noDigest] at fitS
  have fitS' : roundsFit [dS, dC]
      [noDigest ⟨[], D (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩,
        noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩] = true := fitS
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -, -, c14, c15⟩ := switchCut_says Pl.cutSw
  obtain ⟨-, ⟨-, -, -, g5⟩, -⟩ := fit_says fitS'
  have hx : ∀ z ∈ (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
      D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩ : Fmt.RoundView).drawn.poss,
      z < 2 ^ (sgOf cur).C.a := by
    intro z hz
    have := List.all_eq_true.1 g5 z hz
    rw [c10] at this
    exact of_decide_eq_true this
  obtain ⟨h1, Dk, x, row', Dn⟩ := form_step Pl I (sRF K j cur o P (rowOf t) D) fitF _ _ fitS'
    (ofE (sAns p K j cur next l o t P (rowOf t) D)) rfl (sGS cur o col D)
    (hread_of Pl I _ fitF _ hx)
  have e1 : sT1 p K j cur l o t P (rowOf t) D =
      foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest) :=
    getD_of_ok h1
  have h2 : (guardedProximityTestParts.switch p j cur next rest.isEmpty
      (((l.drop (1 + cur.k)).take 2).map (·.1))).decide (sT1 p K j cur l o t P (rowOf t) D)
      ((sRS p K j cur next l o t P (rowOf t) D).map noDigest) (sGS cur o col D) =
      .ok (switchT p n rest.isEmpty
        (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
        (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) t.st.groups.size Dk
        (stepB p n rest.isEmpty dS dC
          (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
          (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
          (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size Dk
          tN) (E.ofTriple x)) := by
    rw [Pl.cutS, e1]
    exact Dn.switch
  have e2 : sT2 p K rest.isEmpty j cur next l o t P col (rowOf t) D =
      (switchT p n rest.isEmpty
        (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
        (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) t.st.groups.size Dk
        (stepB p n rest.isEmpty dS dC
          (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
          (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
          (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size Dk
          tN) (E.ofTriple x)) := getD_of_ok h2
  have h3 : (guardedProximityTestParts.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
      (sT2 p K rest.isEmpty j cur next l o t P col (rowOf t) D) [] [] =
      .ok (stepT3 p n rest.isEmpty dS dC
        (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
        (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
        (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size Dk tN
        row') := by
    rw [Pl.cutS, e2]
    exact Dn.behind
  have e3 : sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D =
      (stepT3 p n rest.isEmpty dS dC
        (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P (rowOf t) D).map noDigest))
        (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))],
          D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩) (sGS cur o col D)
        (foldOut t row L c id ((sRF K j cur o P (rowOf t) D).map noDigest)) t.st.groups.size Dk tN
        row') := getD_of_ok h3
  have hcutF : foldCut cur.k ((l.take (1 + cur.k)).map (·.1)) = true := by
    have ek : c.k = cur.k := Pl.codes.k.trans (kk_eq Pl.hk)
    have h := Pl.cutF
    rw [ek] at h
    exact h
  refine ⟨n, dS, dC, Dk, x, row', Pl, rfl,
    { fold := ⟨_, h1⟩, switch := ⟨_, h2⟩, behind := ⟨_, h3⟩
      came := by
        rw [e3]
        exact Dn.came
      nF := nF_of p j cur l hcutF Pl.hk, oF := oF_of p j cur l hcutF
      nS := nS_of p j cur next rest.isEmpty l dS dC Pl.cutS
      oS := oS_of p j cur next rest.isEmpty l dS dC Pl.cutS (List.isEmpty_iff.1 c14)
        (List.isEmpty_iff.1 c15) Pl.opensS Pl.opensC }, e1, e3, Dn⟩

/-- **Nothing is left untested behind the stage, where nothing was in front.** -/
theorem formLeft_at (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (P : PS) {next : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
    {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout} {c : IoppStage} {nn : ℕ × ℕ}
    {id tN : ℕ} {tr : Tree} (hP : PlanFrom p (next :: rest) j cur l t.st.codes)
    (hS : SortsFrom l cur (next :: rest)) (hF : FitFrom D l o)
    (I : FormInv p j cur l t col row L c nn id tN tr) (hl : ChainEnd.NothingLeft t.st) :
    ChainEnd.NothingLeft (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D).st := by
  obtain ⟨n, dS, dC, Dk, x, row', -, rfl, -, -, e3, Dn⟩ := form_at p K D P hP hS hF I
  rw [e3]
  have hm : Dk.G.members = #[] := by rw [Dn.G]
  cases rest with
  | nil => exact left_step id n.code n.maskCode hl Dn.did hm
  | cons _ _ => exact left_step id n.code n.maskCode hl Dn.did hm

section Behind
variable {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {c n : IoppStage}
  {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout}
  {id tN : ℕ} {tr : Tree} {rs : List Fmt.RoundView} {rS rC : Fmt.RoundView}
  {gs : List (List (ℕ × List UInt64))} {a x : Fmt.Ext} {Dk : Taken} {row' : GroupRow}

/-- **Behind a stage whose next stage is not the last**, at `bodyAll`'s own column. -/
theorem formNext_at {nx : Fmt.M1.Stage} {rest' : List Fmt.M1.Stage}
    (hP : PlanFrom p (next :: nx :: rest') j cur l t.st.codes)
    (Pl : StepPlan p t.st.codes j cur next false l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (Dn : StepDone (sgOf cur) (sgOf next) p n false dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a Dk x row') (K : BCoins) (o : ℕ) (P : PS) (r₀ : GroupRow)
    (D : ℕ → Fmt.Drawn) :
    ∃ (tr' : Tree) (n' : IoppStage), FormInv p (j + 1) next (l.drop (cur.k + 3))
        (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size Dk tN row')
        (sCol K false j cur next o P r₀ D) row'
        (stepL p n false (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size Dk) n
        (n'.code, n'.maskCode) ((foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1)
        t.book.trees.size tr' ∧
      LayAt [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size] #[some 0] #[some 0]
        (stepL p n false (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size Dk) ∧
      SeatP (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size Dk tN row').st
        (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size Dk tN row').book
        [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size,
          (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1]
        (p.nums.firstTree + (p.nums.free + j)) (sgOf next).C.a (stageShapes (sgOf next) n) := by
  obtain ⟨⟨c2, n', dS', dC', Pl'⟩, hD, hst, hown, -⟩ := hP.tail
  obtain rfl : n = c2 := Option.some.inj (Pl.stageN.symm.trans Pl'.stage)
  obtain ⟨tr', h⟩ := formInv_next Pl I Dn Pl' rest' hD hst hown
    (sNext K false j cur next o P r₀ D).tabM (sNext K false j cur next o P r₀ D).tabZ
    (sNext K false j cur next o P r₀ D).tM (sNext K false j cur next o P r₀ D).tZ
    (sNext K false j cur next o P r₀ D).fM (sNext K false j cur next o P r₀ D).fT
  exact ⟨tr', n', h⟩

/-- **Behind the stage in front of the last.** -/
theorem formLast_at (hP : PlanFrom p [next] j cur l t.st.codes)
    (Pl : StepPlan p t.st.codes j cur next true l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (Dn : StepDone (sgOf cur) (sgOf next) p n true dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a Dk x row') :
    LastForm p (j + 1) next
      (stepT3 p n true dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
        (foldOut t row L c id rs) t.st.groups.size Dk tN row') row'
      (stepL p n true (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size Dk) n
      ⟨dense (row'.c.fixLow [zeroE]) (ceilLog2 next.C.l), row'.d.map (·.triple),
        row'.target.triple⟩
      (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size
      ((foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1) t.book.trees.size := by
  obtain ⟨⟨c2, d₁, d₂, Lp⟩, -, -, -⟩ := hP.tail
  obtain rfl : n = c2 := Option.some.inj (Pl.stageN.symm.trans Lp.stage)
  exact lastForm_behind Pl I Dn Lp

/-- **The three public clauses ride**, in the letters of `body_yes_of`'s invariant. -/
theorem formRides_at {rest : List Fmt.M1.Stage} {last : Bool} {o : ℕ} {D : ℕ → Fmt.Drawn}
    (hP : PlanFrom p (next :: rest) j cur l t.st.codes) (hS : SortsFrom l cur (next :: rest))
    (hF : FitFrom D l o) (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (Dn : StepDone (sgOf cur) (sgOf next) p n last dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a Dk x row') :
    PlanFrom p rest (j + 1) next (l.drop (cur.k + 3))
        (stepT3 p n last dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size Dk tN row').st.codes ∧
      SortsFrom (l.drop (cur.k + 3)) next rest ∧
      FitFrom D (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3) := by
  refine ⟨?_, hS.drop Pl.hk, ?_⟩
  · rw [Dn.did.codes]
    exact hP.tail
  · rw [kk_eq Pl.hk, Nat.add_assoc]
    exact hF.drop _

end Behind

end Johnson.Prover.Link
