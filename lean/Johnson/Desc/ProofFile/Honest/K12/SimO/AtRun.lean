-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at a proximity test whose first fold sends its own fresh table: the condition at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/AtRun.lean: at a run of the frame's walking prover, at the stand in front of a called second part, behind the guard: at a table of codes K, that the stand's field holds columns and `OnEntryOwn` (at K = `codesFull` that is `OnOmega`, SimO/Top.lean), from three named parts: the door's equation, the clause on the first opening's columns and the clause `asks`. What is paid here: the field, le, leS, heardFit, heard, fold (SimO/FiveOwn.lean). The state that stands in is the job's own.

  `onOmega_at_run`   the statement
  `onOmega_first_at_run`   at a called part other than the second: the field holds columns, and nothing else is asked

Conditional. Nothing here shows that ready or runC returns, or that the part is called. The door's equation is paid at `jobAtOmega` by `door_at_omega` (SimO/DoorOmega.lean) under its two premises. The clauses on the columns and on asks are premises inside the conclusion: SimO/TreesOmega.lean has the first at a run; no file shows asks at a run. Premises of the statement: on the description: S, hlaid; on the book: hf, ho, hst, hmem, not evaluated on any real book; on the job's text: hrows; public: T, hk; on the challenges: hfit; on the prover: hg, which holds at the term only through `halfO_at_head`. The condition reads the input and the rows: no later law may take it as a hypothesis on a run and speak of the random values as sampled anew. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Top
import Johnson.Desc.ProofFile.Honest.K12.SimO.FiveOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (codesFull)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC midSharedAtW
  Before Placed Part carryE Ahead Addr Face)

/-- **The condition at a run.** -/
theorem onOmega_at_run {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (hfr : J.fresh = none) (Js : SimJob Pb)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Pb) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js : Member Empty _ _ _).guarded pre t (firstLen J.p.nums.stages))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (e₂ : Ahead) (hf : (carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ Rc Ky) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) (φ : Face Empty (Common W₀ Rc Ky) Pb) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (K : OnBytes.Codes) :
    ∃ (c : ProofFile.Honest.RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField,
              (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true ∧
      (J.rec₀ m.st.input (restFront J m) = Js.rec₀ (φ.pub m.st.input)
          ((r.run.beforeAt st ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages)) →
        ((J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)
            (rowsAt J (ProofFile.Honest.K12.stretches _ c.2.1.2.2) m)).map (·.1) = os.map (·.1.a) ∧
          ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T' : Tree), os[i]? = some o →
            (J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)
              (rowsAt J (ProofFile.Honest.K12.stretches _ c.2.1.2.2) m))[i]? = some T' →
            ∃ cols, (r.run.beforeAt st ⟨σ.block.place, 1⟩).treeCols (ProofFile.Honest.srcOf chain o.2).1
                (ProofFile.Honest.srcOf chain o.2).2 = some cols ∧ ∀ q ∈ cols, q.2 = T'.2 q.1) →
        (∃ (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (Rw : PlainRows),
          Dp.ts.length = os.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO J m.st.input (restFront J m)
            (carriedCoins J (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn J m) K Dp ∧
          DataAsks J m.st.input (restFront J m)
            (carriedCoins J (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn J m) Dp cc Rw) →
        (∃ cs, m.opened = some cs) ∧
          OnEntryOwn φ J Js K chain os (restMember J Js : Member Empty _ _ _).guarded c.2.1.2.2 m
            (r.run.beforeAt st ⟨σ.block.place, 1⟩)) := by
  obtain ⟨c, m, hm, hca, hin, h1, h2, h3, h4, h5⟩ := five_own_at_run hpl J hfr Js hR σ _ rfl pre t S hg hlaid
    e₂ hf ho hst hmem s next rest D T hk hrows hfit hrun hc st
  refine ⟨c, m, hm, hca, hin, h3, fun hdoor htr hasks => ?_⟩
  obtain ⟨m2, -, cs, hm2, hop, -, -⟩ := ProofFile.Honest.K12.Sim2.called_columns hpl hR hrun σ _ pre t _ S hc
  have emm : m2 = m := Option.some.inj (Except.ok.inj (hm2.symm.trans hm))
  rw [emm] at hop
  refine ⟨⟨cs, hop⟩, fun _ => ⟨J.rec₀, fun _ _ => rfl, ?_⟩⟩
  exact { le := h1, leS := h2, heardFit := h3, heard := h4, door := hdoor, fold := h5, trees := htr, asks := hasks }

/-- **The condition at a called part other than the second**: the field holds columns, and nothing else is asked. -/
theorem onOmega_first_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (hu : u.number ≠ 1)
    (φ : Face V (Common W₀ Rc Ky) Pb) (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) :
    ∃ m, midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      ∀ (ca : ProofFile.Honest.CsAll u.part.carries) (front : ProofFile.Honest.Before),
        (∃ cs, m.opened = some cs) ∧ OnEntryOwn φ J Js K chain os u ca m front := by
  obtain ⟨m, -, cs, hm, hop, -, -⟩ := ProofFile.Honest.K12.Sim2.called_columns hpl hR hrun σ u pre t i S hc
  exact ⟨m, hm, fun _ _ => ⟨⟨cs, hop⟩, fun h => absurd h hu⟩⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.onOmega_first_at_run
#print axioms ProofFile.Honest.K12.Light.onOmega_at_run
