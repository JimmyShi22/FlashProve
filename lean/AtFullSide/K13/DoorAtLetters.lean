-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/DoorAtLetters.lean: THE FORM AT THE LAST CHAIN's FIRST BORDER. door_heads_walk
(Honest/Thread/EndsAtHeads.lean) asks of that border its form. Here it is laid from the conditions
of the library's door_fillZ.

  inOrder_at_door  the last chain's start is in order
  form_at_door     the clause (F) of the last thread at its first border, where its promise is
    filled by fillZ

What these are. Conditional lemmas under the library's one hypothesis at the full size, h. None is
one of the library's goals. They say nothing of soundness, completeness or hiding.

Limits.
  * hfirst and hshared are the two tests on the two ends that the library's DoorOwed names. They are
    premises, and neither is shown here.
-/
import AtFullSide.K13.DotAtTheDoor
import Johnson.Desc.ProofFile.Honest.Thread.EndsAtHeads
import Johnson.Desc.Means.TestsBack
import Johnson.Desc.Last.ShapeDoor
import Johnson.Desc.Plain.StartThreeAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL fillZ firstDoorB sharedDoorB door_fillZ
  lastPlaces)
open VerifiableInference.Desc.Third (firstOfS sharedOfEnd)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead Letters)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The last chain's start is in order**, where the test on the first chain's end says yes: the
first of that test's clauses is that the statement is tidy, and the start hands it on. -/
theorem inOrder_at_door {ξ : ProofFile.InstPub} {e₁ : TS} {e₂ : Desc.K14.St}
    {s₃ : VerifiableInference.Desc.Third.S₃}
    (hs : (F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ e₁ e₂ = .ok s₃)
    (hfirst : ∀ f, firstOfS e₁ = some f → firstDoorB f = true) :
    OnBytes.Means.InOrder s₃.st := by
  obtain ⟨e, -, h₀⟩ := ProofFile.hstart_at OnBytes.secondHashFunction Zp Np cF (fun q => q) (fun _ _ => rfl) ξ e₁ e₂ s₃
    (by
      show ((F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ e₁ e₂).toOption = some s₃
      rw [hs]
      rfl)
  unfold VerifiableInference.Desc.Third.startAtEnds VerifiableInference.Desc.Third.start₃F at h₀
  cases hf : firstOfS e₁ with
  | none =>
    have h₁ := h₀
    simp only [hf] at h₁
    cases h₁
  | some f =>
    have h₁ := h₀
    simp only [hf] at h₁
    obtain ⟨e1, -, -⟩ := VerifiableInference.Desc.Last.start_parts h₁
    have ht := hfirst f hf
    unfold firstDoorB VerifiableInference.Desc.Last.firstDoorClauses at ht
    rw [List.all_cons, Bool.and_eq_true] at ht
    rw [e1]
    exact (OnBytes.Means.tidy4B_iff.1 ht.1).inOrder

/-- **(F) of the last thread at its first border.** -/
theorem form_at_door {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Cells Tok M Wt₂ Wt₃ : Type}
    {H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
    {ξ : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
    (L₁ : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub Cells Tok M)
    (L₂ : SharedThread.Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀
      (ProofFile.InstPub × TS) Wt₂)
    (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
      Tr X (ProofFile.InstPub × TS) Wt₃)
    {c₁ c₂ : Nat} (Rr : List Fmt.DeclaredRound)
    (hPL : L₃.PL = fillZ (ProofFile.pAt Zp) Rr fun q => q.2)
    (hah₁ : L₁.thread.ahead = []) (hah₂ : L₂.thread.ahead = [])
    (hah : L₃.ahead = declsTo L₁.thread.bs c₁ ++ declsTo L₂.thread.bs c₂)
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr L₁.thread c₁ k e₁ m₁ E₁) (u₂ : Thr L₂.thread c₂ k e₂ m₂ E₂)
    (hends : L₃.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((ξ.pub, e₁), e₂))
    {s₃ : VerifiableInference.Desc.Third.S₃}
    (hs : (F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ.pub e₁ e₂ = .ok s₃)
    (hfirst : ∀ f, firstOfS e₁ = some f → firstDoorB f = true)
    (hshared : ∀ e, Desc.K14.ended e₂ = some e →
      sharedDoorB (ProofFile.pAt Zp) (sharedOfEnd e) = true)
    (hord : ∀ s, OnBytes.Means.InOrder s.st → L₃.order s) :
    L₃.thread.Form 0 k s₃ (R.start₃ H m₁ m₂) := by
  have hseat := ProofFile.Honest.FirstThread.seat_at_door L₁ L₂ L₃ (H := H) hah₁ hah₂ hah u₁ u₂ hends s₃
  have hz : (fillZ (ProofFile.pAt Zp) Rr fun q : ProofFile.InstPub × TS => q.2).shape 0 (ξ.pub, e₁) e₂ s₃ =
      true := by
    refine door_fillZ (Str := Unit) (R := Rr)
      (On₂ := fun b => b.1.1 = (ξ.pub, e₁) ∧ b.1.2 = e₂)
      (start₃ := fun q a d => ((F0T OnBytes.secondHashFunction Zp Np cF).start₃ q a d).toOption)
      ⟨?_, ?_, ?_⟩ (((ξ.pub, e₁), e₂), ()) s₃ ⟨rfl, rfl⟩ ?_
    · rintro ⟨⟨⟨q, a⟩, d⟩, u⟩ s ⟨c₁', c₂'⟩ _ f hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj c₁'
      exact hfirst f hf
    · rintro ⟨⟨⟨q, a⟩, d⟩, u⟩ s ⟨c₁', c₂'⟩ _ e he
      obtain rfl : d = e₂ := c₂'
      exact hshared e he
    · intro q a d s hy
      exact ProofFile.hstart_at OnBytes.secondHashFunction Zp Np cF (fun q => q) (fun _ _ => rfl) q a d s hy
    · show ((F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ.pub e₁ e₂).toOption = some s₃
      rw [hs]
      rfl
  refine ⟨?_, ?_⟩
  · rw [hseat]
    show (L₃.PL.shape 0 (ξ.pub, e₁) e₂ s₃ &&
      (!decide (lastPlaces.length ≤ 0) || L₃.PL.nothingLeft s₃)) = true
    rw [hPL, hz]
    have hl : ¬ lastPlaces.length ≤ 0 := by decide
    simp [hl]
  · rw [hseat]
    exact hord _ (inOrder_at_door hs hfirst)

end AtFullSide.K13

#print axioms AtFullSide.K13.form_at_door
#print axioms AtFullSide.K13.inOrder_at_door
