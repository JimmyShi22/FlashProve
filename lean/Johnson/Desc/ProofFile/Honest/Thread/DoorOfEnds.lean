-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/DoorOfEnds.lean: THE DOOR AT THE THREE TERMS, WHERE THE LETTER ends
IS GIVEN BY WHAT IT SAYS AT THIS RUN. door_heads_walk (EndsAtHeads.lean of this folder) lays ends as
the function endsBy. A letter that reads the threads at each input is another function that agrees
with it at the run's own input, and the door reads it there alone.

  door_of_ends   DoorBehindS at lettersHead, lettersShared and lettersLast, from the two ends

What this is. A conditional lemma on our own definitions. It is none of the library's goals. Its
proof is door_heads_walk's behind the equation on ends.

Limits.
  * hends is a premise: at two stands of one run, ends at this run's input and the challenges heard
    names the two states.
  * All limits of EndsAtHeads.lean on Mg₃, ML and PL stand.
  * None of the hypotheses is shown here of any run.
-/
import Johnson.Desc.ProofFile.Honest.Thread.EndsAtHeads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {p₀ : VerifiableInference.Desc.First.Look.Place}

local notation "𝔽" => F0T OnBytes.secondHashFunction Zp Np cF

/-- **`DoorBehindS` at the three terms, from the two ends as the letter `ends` names them at this run.** -/
theorem door_of_ends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF p₀) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X Wt₂ Wt₃ : Type} [Inhabited TS] [Inhabited Desc.K14.St]
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop)
    (N : NumbersS)
    (Mg₂ : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt₂)
    (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
    (order₂ : Desc.K14.St → Prop)
    (wit₂ : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt₂)
    (table₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      Place × Table)
    (fixed₂ : Fmt.TreeSource → Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
    (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
    (Kp₂ : Place → Desc.K14.St → Desc.K14.St → Prop)
    (Mg₃ : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt₃)
    (ML : MeaningL VerifiableInference.Desc.Third.S₃ Wt₃)
    (PL : PromMeaningL Desc.K14.St VerifiableInference.Desc.Third.S₃ (ProofFile.InstPub × TS))
    (order₃ : VerifiableInference.Desc.Third.S₃ → Prop) (taken : List Fmt.TreeSource)
    (wit₃ : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt₃)
    (table₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
    (fixed₃ : Fmt.TreeSource → Nat) (Vd₃ : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd₃ : Nat → Local W₀ Rc ProofFile.Inst Tr → VerifiableInference.Desc.Third.S₃ → Prop)
    (Kp₃ : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop)
    {m₀₁ : Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {m₀₂ : Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀}
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
    {T₁ : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {T₂ : Thread Bk Desc.K14.St ProofFile.Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey}
    {T₃ : Thread Bk VerifiableInference.Desc.Third.S₃ ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
      (ProofFile.InstPub × TS) × Desc.K14.St}
    (hR : ready (𝔽) Bk H w₀ rc ξ k = .ok R) (hkey : H.key ξ = ξ.pub.key)
    (t₁ : T₁ = (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread)
    (t₂ : T₂ = (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
      fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread)
    (t₃ : T₃ = (LastThread.lettersLast Zp Np cF H N Mg₃ ML PL order₃ taken ends wit₃ table₃ fixed₃
      item n₁ n₂ Vd₃ Rd₃ Kp₃ R.own).thread)
    (sits : Sits (𝔽) H T₁ T₂ T₃)
    (hends : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((ξ.pub, e₁), e₂))
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.Trees T₃.taken k (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hForm : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (𝔽).start₃ ξ.pub e₁ e₂ = .ok s₃ → T₃.Form 0 k s₃ (R.start₃ H m₁ m₂))
    (hItems : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (𝔽).start₃ ξ.pub e₁ e₂ = .ok s₃ →
      T₃.Items (T₃.opened 0) k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (𝔽).start₃ ξ.pub e₁ e₂ = .ok s₃ → Rd₃ 0 R.own s₃)
    (hV : Vd₃ R.own) :
    DoorBehindS (𝔽) H T₁ T₂ T₃ (SaidWalk T₁ BaseNil m₀₁) (SaidWalk T₂ BaseNil m₀₂)
      (SaidField T₃ (BaseTied (𝔽) T₃)) ξ k R := by
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok hR
  have hξ : R.own.x = ξ := by rw [hown]
  have hc : R.common = ⟨R.own.w₀, R.own.rc, H.key R.own.x⟩ := by rw [hcom, hown]
  have hS₁ : ∀ k m, SaidWalk T₁ BaseNil m₀₁ (𝔽).first.blocksInOrder.length k m →
      SaidField T₁ BaseNil (𝔽).first.blocksInOrder.length k m := fun _ _ a => a.1
  have hS₂ : ∀ k m, SaidWalk T₂ BaseNil m₀₂ (𝔽).shared.blocksInOrder.length k m →
      SaidField T₂ BaseNil (𝔽).shared.blocksInOrder.length k m := fun _ _ a => a.1
  have hfront : T₃.front = ((𝔽).first.blocksInOrder.flatMap (·.rounds)).length +
      ((𝔽).shared.blocksInOrder.flatMap (·.rounds)).length := by
    have e : T₃.ahead = declsTo (𝔽).first.blocksInOrder (𝔽).first.blocksInOrder.length ++
        declsTo (𝔽).shared.blocksInOrder (𝔽).shared.blocksInOrder.length := by
      rw [t₃]
      rfl
    unfold Thread.front
    rw [e, List.length_append]
    simp only [declsTo, List.take_length]
  have htie : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₀,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₀ → (𝔽).start₃ ((𝔽).pub ξ) e₁ e₂ = .ok s₀ := by
    intro e₁ m₁ E₁ e₂ m₂ E₂ s₀ u₁ u₂ g
    subst t₃
    have g' : (𝔽).start₃ (ends k R.own (m₁.st.heard ++ m₂.st.heard)).1.1
        (ends k R.own (m₁.st.heard ++ m₂.st.heard)).1.2
        (ends k R.own (m₁.st.heard ++ m₂.st.heard)).2 = .ok s₀ := g
    rw [hends e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂] at g'
    exact g'
  have hb₁ : ∀ e m E s₀, Thr T₁ (𝔽).first.blocksInOrder.length k e m E → T₁.begun k m.st.input [] s₀ →
      s₀ = (𝔽).start₁ ((𝔽).pub ξ) := by
    subst t₁
    exact fun _ _ _ _ u g =>
      Letters.begun_of_valid (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own) (x := ξ)
        (fun v hv => by
          have e : v = R.own ∧ Vd v := hv
          rw [e.1]
          exact hξ)
        u.2.2.2.2.2.2 g
  have hb₂ : ∀ e m E s₀, Thr T₂ (𝔽).shared.blocksInOrder.length k e m E → T₂.begun k m.st.input [] s₀ →
      s₀ = (𝔽).start₂ ((𝔽).pub ξ) := by
    subst t₂
    exact fun _ _ _ _ u g =>
      SharedThread.Letters.begun_of_valid
        (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂ fixed₂ n₁
          n₂ Vd₂ Rd₂ Kp₂ R.common) (y := ξ.pub.key)
        (fun v hv => by
          have e : v = R.common ∧ Vd₂ v := hv
          rw [e.1, hc]
          show H.key R.own.x = _
          rw [hξ]
          exact hkey)
        u.2.2.2.2.2.2 g
  have hah₁ : T₁.ahead = [] := by
    rw [t₁]
    rfl
  have hah₂ : T₂.ahead = [] := by
    rw [t₂]
    rfl
  have e₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (𝔽).start₃ ((𝔽).pub ξ) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      SaidField T₃ (BaseTied (𝔽) T₃) 0 k
        { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } :=
    fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs g₁ g₂ =>
      said₃_tied H k R hS₁ hS₂ u₁ u₂
        (baseTied_at_door sits hah₁ hah₂ hξ hS₁ hS₂ hfront hb₁ hb₂ htie e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂
          u₁ u₂ hs g₁ g₂)
  subst t₃ t₂ t₁
  refine doorBehindS_cut_field rfl rfl rfl rfl rfl ?_ htrees ?_ hForm hItems hr ⟨rfl, hV⟩ e₃
  · intro v hv i p
    have e : v = R.own := hv.1
    show H.storedWords v.w₀ v.rc i p = H.storedWords R.own.w₀ R.own.rc i p
    rw [e]
  · intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs
    show (𝔽).start₃ (ends k R.own (m₁.st.heard ++ m₂.st.heard)).1.1
      (ends k R.own (m₁.st.heard ++ m₂.st.heard)).1.2
      (ends k R.own (m₁.st.heard ++ m₂.st.heard)).2 = .ok s₃
    rw [hends e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂]
    exact hs

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.door_of_ends
