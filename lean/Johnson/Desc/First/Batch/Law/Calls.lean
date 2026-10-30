-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Calls.lean
(kind K9's small law on the call): THEOREMS: THE BATCHING's LAW "Calls R Q batch"
(Johnson/Desc/Sound/FoldSteps.lean): where the batching's decision goes on, it HAS
CALLED the one function of claims that it was handed, R holds around the call, and Q holds of the
six things (the record in front, the rounds, the record at the call, the claims, the record that the
call left, the record behind): AT THE REAL BLOCK K9.batch X p.
  drawAlone_decide, adds_decide   the inversions of the two halves' decisions.
  batch_calls      Calls R Q (K9.batch X p), for every relation R that holds across the draw's
                   writing (hdraw) and across the adding's writing (hadd), and every Q that holds
                   wherever the draw's tests pass, the record at the call is the draw's writing, and
                   the record behind is the adding's writing (hQ).
  batch_calls_carries   the case R := Carries fork heard later sized ("what is heard stays heard; a
                   ledger with its sizes is followed by a later one with its sizes"), from: the
                   lens's law; fork reads the lens's ledger; the lens's writing leaves heard; and
                   "later" and "sized" across the draw and across the adding (two hypotheses on
                   these two letters).

-/
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.First.Batch.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where drawAlone adds batch drawnClean)

variable {T : Type}

theorem drawAlone_decide {Cl : Type} (X : Lens T) (p : Where) (s : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : T)
    (h : (drawAlone (Cl := Cl) X p).decide s rs gs = .ok s') :
    ∃ a chi o, X.get? s = some a ∧ drawnClean p.rows chi a.owed a.used a.L a.F = .ok o ∧
      s' = X.set s { a with owed := o.owed, L := o.L, F := o.F } := by
  simp only [drawAlone] at h
  match rs, h with
  | [r], h =>
    obtain ⟨a, ha, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    exact ⟨a, _, o, there_ok ha, ho, (Except.ok.inj h).symm⟩

theorem adds_decide {Cl : Type} (X : Lens T) (p : Where) (piece : Nat) (what : String)
    (f : T → Except String (List Claim × T)) (s : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : T)
    (h : (adds (Cl := Cl) X p piece what f).decide s rs gs = .ok s') :
    ∃ cls e b G, f s = .ok (cls, e) ∧ X.get? e = some b ∧ addAll b.F cls = some G ∧
      s' = X.set e { b with F := G } := by
  simp only [adds] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨b, hb, h⟩ := ok_bind h
  obtain ⟨G, hG, h⟩ := ok_bind h
  exact ⟨x.1, x.2, b, G, hx, there_ok hb, addList_older _ _ _ hG, (Except.ok.inj h).symm⟩

/-- **The batching has called the function that it was handed.** -/
theorem batch_calls (X : Lens T) (p : Where) (R : T → T → Prop)
    (hdraw : ∀ s a chi o, X.get? s = some a →
      drawnClean p.rows chi a.owed a.used a.L a.F = .ok o →
      R s (X.set s { a with owed := o.owed, L := o.L, F := o.F }))
    (hadd : ∀ e b cls G, X.get? e = some b → addAll b.F cls = some G →
      R e (X.set e { b with F := G }))
    (Q : T → List Fmt.RoundView → T → List Claim → T → T → Prop)
    (hQ : ∀ s rs a chi o cls e b G, X.get? s = some a →
      drawnClean p.rows chi a.owed a.used a.L a.F = .ok o → X.get? e = some b →
      addAll b.F cls = some G →
      Q s rs (X.set s { a with owed := o.owed, L := o.L, F := o.F }) cls e
        (X.set e { b with F := G })) : Calls R Q (batch X p) := by
  intro f s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h2⟩ := ok_bind h
  obtain ⟨a, chi, o, ha, ho, rfl⟩ := drawAlone_decide X p s rs gs t₁ h1
  obtain ⟨cls, e, b, G, hf, hb, hG, rfl⟩ := adds_decide X p _ _ f _ [] [] s' h2
  exact ⟨_, cls, e, hdraw s a chi o ha ho, hf, hadd e b cls G hb hG,
    hQ s rs a chi o cls e b G ha ho hb hG⟩

/-- **The case of Carries.** -/
theorem batch_calls_carries {Γ : Type} (X : Lens T) (p : Where) (fork : T → Option Fork)
    (heard : T → Option Γ) (later : Fork → Fork → Prop) (sized : Fork → Prop)
    (lens : ∀ s a, (X.get? s).isSome = true → ∃ a', X.get? (X.set s a) = some a' ∧ a'.F = a.F)
    (hfork : ∀ s a, X.get? s = some a → fork s = some a.F)
    (hheard : ∀ s a, heard (X.set s a) = heard s)
    (hl1 : ∀ (a : K9.Part) chi o, drawnClean p.rows chi a.owed a.used a.L a.F = .ok o →
      sized a.F → later a.F o.F ∧ sized o.F)
    (hl2 : ∀ (F G : Fork) cls, addAll F cls = some G → sized F → later F G ∧ sized G)
    (Q : T → List Fmt.RoundView → T → List Claim → T → T → Prop)
    (hQ : ∀ s rs a chi o cls e b G, X.get? s = some a →
      drawnClean p.rows chi a.owed a.used a.L a.F = .ok o → X.get? e = some b →
      addAll b.F cls = some G →
      Q s rs (X.set s { a with owed := o.owed, L := o.L, F := o.F }) cls e
        (X.set e { b with F := G })) :
    Calls (Carries fork heard later sized) Q (batch X p) := by
  refine batch_calls X p _ (fun s a chi o ha ho => ⟨fun g hg => ?_, fun F hF hs => ?_⟩)
    (fun e b cls G hb hG => ⟨fun g hg => ?_, fun F hF hs => ?_⟩) Q hQ
  · rw [hheard]
    exact hg
  · obtain ⟨a', h1, h2⟩ :=
      lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
    have e : F = a.F := Option.some.inj (hF.symm.trans (hfork s a ha))
    have h2' : a'.F = o.F := h2
    rw [e] at hs ⊢
    exact ⟨o.F, by rw [hfork _ a' h1, h2'], hl1 a chi o ho hs⟩
  · rw [hheard]
    exact hg
  · obtain ⟨b', h1, h2⟩ := lens e { b with F := G } (by simp [hb])
    have e1 : F = b.F := Option.some.inj (hF.symm.trans (hfork e b hb))
    have h2' : b'.F = G := h2
    rw [e1] at hs ⊢
    exact ⟨G, by rw [hfork _ b' h1, h2'], hl2 b.F G cls hG hs⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.batch_calls
#print axioms VerifiableInference.Desc.K9L.batch_calls_carries
