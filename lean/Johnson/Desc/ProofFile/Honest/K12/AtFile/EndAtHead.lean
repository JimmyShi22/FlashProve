-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/EndAtHead.lean: NOT IN FRONT OF A LAW OVER COINS. Under the
head, at the proof file's shared thread: the end is accepted at every stand at 11, from the closed run
of the guards on the shape.

  ZP_alike             the guards read of the two tests what their written values say
  yes_head             the guards' run returns at the shared chain's own plan and seated tests
  end_member           the last member is the chain's end
  twelve_members       the thread has twelve members
  end_at_head          Accepted at 11

By what. shape_run_real (EndShapeRun.lean), accepted_at_end (EndAtProof.lean), testCore_alike,
alike_head_U, alike_head_O, qAt_written, chainAt_shared, shared_flat_at, plan2_at_head,
planOk_head_eight.

Limits. hk, that an input's key has sizes that fit, and hn, that no half stands at the end's place,
are premises. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.EndShapeRun
import Johnson.Desc.ProofFile.Honest.K12.FrontAtHead
import Johnson.Desc.ProofFile.Honest.K12.MarksAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanAtSeat
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Ground.Sh (tidy_mark)
open _root_.Desc.K14 (P14 St blocks blocksOr p14Of beforePointOf)
open _root_.Desc.K14.Honest (keyW)
open _root_.Desc.K14.Shape (sh2 first_shape marked_first)
open AtPublicFiles.AtFiles (Sh₂ sh₂ gTest₂ gEnd₂)
open H2K.Member (piUFull piOFull)
open H2K.JointK (guEntry omegaEntry pGu pGomega sharedPre shared_cut_omega)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (Alike testCore_alike alike_head_U written_at_head qAt_written)
open ProofFile.Honest.K14 (Plan2 chainAt_shared shared_flat_at plan2_at_head)
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (F0T)

/-- The guards read of a test what its alike parameters say. -/
theorem gTest_alike {p q : P12} (A : Alike p q) (grp : _root_.Desc.K14.Shape.LinSh → Nat)
    (mask : _root_.Desc.K14.Shape.LinSh → Option Nat) : gTest₂ p grp mask = gTest₂ q grp mask := by
  funext a
  unfold gTest₂
  rw [testCore_alike A]

theorem ZP_alike {pU qU pO qO : P12} (AU : Alike pU qU) (AO : Alike pO qO) (Q : P14)
    (sentU : Array OracleNotice)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a : Sh₂) (n : ℕ) :
    (ZP Q sentU pU pO v).yes a n = (ZP Q sentU qU qO v).yes a n := by
  have hg : (ZP Q sentU pU pO v).g = (ZP Q sentU qU qO v).g := by
    funext b
    show (if b < 9 then gKP Q sentU b else if b = 9 then gTest₂ pU _ _ else
        if b = 10 then gTest₂ pO _ _ else gEnd₂) =
      (if b < 9 then gKP Q sentU b else if b = 9 then gTest₂ qU _ _ else
        if b = 10 then gTest₂ qO _ _ else gEnd₂)
    rw [gTest_alike AU, gTest_alike AO]
  exact congrArg (fun g : ℕ → Sh₂ → Except String Sh₂ =>
    (⟨Sh₂, sh₂, g, v⟩ : Shape St).yes a n) hg

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {nO : H2U.PlaceNums}

/-- The test reads the codes and the shape alone. -/
theorem runOK_plan (A : ProofFile.Honest.K14.SendPub) (pU pO : P12) :
    runOK A.P pU pO = runOK (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S).P pU pO := rfl

/-- **The guards' run returns at the chain's own plan and the seated tests.** -/
theorem yes_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (AO : Alike (pGomega nO) piOFull)
    {sentU : Array OracleNotice} (hU : _root_.Desc.K14.withU (K1.qAt Zp Np).S = some sentU) :
    (ZP (K1.qAt Zp Np) sentU (pGu Np) (pGomega nO) (fun _ _ _ _ => true)).yes
      (sh2 (_root_.Desc.K14.first (K1.qAt Zp Np).codes (keyW (K1.qAt Zp Np).par.S.fold.index)), true) 12 =
      true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := shape_run_real
  rw [hx] at k
  have k' : runOK (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x.shape).P piUFull piOFull =
    true := k
  have e : runOK (K1.qAt Zp Np) piUFull piOFull = true := by
    have e₂ := runOK_plan ⟨K1.qAt Zp Np, 0⟩ piUFull piOFull
    rw [qAt_written Wr Np] at e₂ ⊢
    exact e₂.trans k'
  have AU : Alike (pGu Np) piUFull := alike_head_U h
  unfold runOK at e
  rw [hU] at e
  exact (ZP_alike AU AO _ _ _ _ _).trans e

section
variable {W₀ Rc Tr X₀ X P₁ Wt : Type} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {N : NumbersS}
  {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt} {shape : ℕ → St → Bool} {nothingLeft : St → Bool}
  {order : St → Prop} {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
  {table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → VerifiableInference.Desc.Place × Table}
  {fixed : Fmt.TreeSource → ℕ} {n₁ n₂ : ℕ} {Vd : Common W₀ Rc TableKey → Prop}
  {Rd : ℕ → Common W₀ Rc TableKey → St → Prop} {Kp : VerifiableInference.Desc.Place → St → St → Prop}
  {w : Common W₀ Rc TableKey} {x₀ : VerifiableInference.Desc.First.Look.Place}

local notation "𝐋" => lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w

/-- The last member of the thread is the chain's end. -/
theorem end_member (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : Np.O = some nO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) :
    (𝐋).thread.bs[11]? = some (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np) := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head hA
  obtain ⟨B⟩ := hQ.eight
  have hpre : (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np).length = 9 := by
    unfold sharedPre
    rw [AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : (𝐋).thread.bs = (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np ++ [guEntry ProofFile.Cl Np]) ++
      omegaEntry ProofFile.Cl nO :: [H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np] := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = _
    rw [shared_flat_at]
    exact shared_cut_omega ProofFile.Cl Zp.p.chains _ Np nO hO
  rw [hc]
  simp [List.getElem?_append, hpre]

/-- The thread has twelve members. -/
theorem twelve_members (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : Np.O = some nO) :
    (𝐋).thread.bs.length = 12 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head hA
  obtain ⟨B⟩ := hQ.eight
  have hpre : (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np).length = 9 := by
    unfold sharedPre
    rw [AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : (𝐋).thread.bs = (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np ++ [guEntry ProofFile.Cl Np]) ++
      omegaEntry ProofFile.Cl nO :: [H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np] := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = _
    rw [shared_flat_at]
    exact shared_cut_omega ProofFile.Cl Zp.p.chains _ Np nO hO
  rw [hc]
  simp [hpre]

/-- **The end is accepted at every stand at 11, under the head.** -/
theorem end_at_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : Np.O = some nO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs)
    (hk : ∀ v, (𝐋).thread.valid v → keyFits v.key (K1.qAt Zp Np).par.S.fold.index = true)
    (hn : ((𝐋).thread.hs.find? fun g => g.place ==
      (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np).place) = none)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : Accepted (𝐋).thread fall 11 := by
  have h := hA.toAtMg
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head hA
  have hT := chainAt_shared (Zp := Zp) (Np := Np) (cF := cF) (H := H) (N := N) (Mg := Mg)
    (shape := shape) (nothingLeft := nothingLeft) (order := order) (wit := wit) (table := table)
    (fixed := fixed) (n₁ := n₁) (n₂ := n₂) (Vd := Vd) (Rd := Rd) (Kp := Kp) (w := w)
  obtain ⟨B⟩ := hQ.eight
  have hplan : ∀ b ∈ blocksOr (K1.qAt Zp Np), b.planOk = true := by
    have e : blocksOr (K1.qAt Zp Np) = bs := by
      unfold blocksOr
      rw [hb]
      rfl
    rw [e]
    exact ProofFile.Honest.K12.Light.planOk_head_eight h bs hb
  have hpre : (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np).length = 9 := by
    unfold sharedPre
    rw [AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : (𝐋).thread.bs = (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np ++ [guEntry ProofFile.Cl Np]) ++
      omegaEntry ProofFile.Cl nO :: [H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np] := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = _
    rw [shared_flat_at]
    exact shared_cut_omega ProofFile.Cl Zp.p.chains _ Np nO hO
  have gets : ∀ (pre : List (Block St ProofFile.Cl)) (a b c : Block St ProofFile.Cl), pre.length = 9 →
      ((pre ++ [a]) ++ b :: [c])[9]? = some a ∧ ((pre ++ [a]) ++ b :: [c])[10]? = some b ∧
      ((pre ++ [a]) ++ b :: [c])[11]? = some c ∧ ((pre ++ [a]) ++ b :: [c]).length = 12 := by
    intro pre a b c hl
    simp [List.getElem?_append, hl]
  obtain ⟨g9, g10, g11, gl⟩ := gets _ (guEntry ProofFile.Cl Np) (omegaEntry ProofFile.Cl nO)
    (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np) hpre
  have he := H2K.JointK.early_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_U h)
  have ha := H2K.JointK.answers_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_U h)
  have hOf : (fourOf Np).O = some (pGomega nO) := by
    show Np.O.map _ = _
    rw [hO]
    rfl
  have AO := alike_head_O h hOf
  have he' := H2K.JointK.early_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_O h hOf)
  have ha' := H2K.JointK.answers_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_O h hOf)
  refine accepted_at_end hQ hT hplan (by rw [hc]; exact g9) (by rw [hc]; exact g10)
    (by rw [hc]; exact g11) (by rw [hc]; exact gl) he ha he' ha'
    (yes_head h AO hQ.facts.goes) (fun k v hh s₀ hv hbg => ?_) hn fall
  obtain rfl := hT.begun k v hh s₀ hbg
  exact Prod.ext (first_shape (K1.qAt Zp Np) v.key (hk v hv))
    (tidy_mark (marked_first (K1.qAt Zp Np).codes v.key).1)

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.gTest_alike
#print axioms ProofFile.Honest.K12.AtFile.ZP_alike
#print axioms ProofFile.Honest.K12.AtFile.yes_head
#print axioms ProofFile.Honest.K12.AtFile.end_member
#print axioms ProofFile.Honest.K12.AtFile.twelve_members
#print axioms ProofFile.Honest.K12.AtFile.end_at_head
