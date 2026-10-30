-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/Third.lean: the third chain's start and its first two blocks keep the four
invariants on a statement (`Tidy`, Johnson/Desc/Means/Walk.lean): a yes of "K14, second part" gives
a walk of quiet steps from the statement in front to the statement behind, where the shared chain's
last statement, from which Omega's sample rows are copied, is in order. Statements with their
proofs. They stand over the inversions of Johnson/Desc/Third/Law/Keeps.lean, Start.lean and
AtDoor.lean.
Main names:
  `takeOver_walk`, `k14Second_walk`: the walks: the tree comes in, the sample rows are copied, Omega
    joins the own group; the row (Dot) is added.
  `start₃E_border`: the start lays the shared chain's end that it was handed into the record.
  `k14Second_tidy`, `takenSources_tidy`.
  `tidy_border2`: **in front of the request's own proximity test the statement is tidy**, if the
    first chain's last statement is tidy and the shared chain's last statement is in order.
  `tidy_border2_at`: the same at `startAtEnds` (Johnson/Desc/Third/Border.lean): of the first
    chain's last record and the program's record of the shared chain's end.
  `not_tidy_start`: a try: the start hands on an untidy statement as it is.

What is not claimed. That the two chains' last statements are so: each chain's walk from its empty
statement says that. Nothing on the own test's block. Nothing on soundness.

-/
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.Third.Law.Start
import Johnson.Desc.Third.Law.AtDoor
import Johnson.Desc.Third.Chain
import Johnson.Desc.Third.Border
import Johnson.Desc.Means.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes
open Desc.Plain (DState)
open OnBytes.Means (Tidy Walk InOrder quiet_adoptP quiet_elsewhereP quiet_joinP quiet_addRowP)

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **Omega is taken over: a walk**, where the shared chain's last statement is in order. -/
theorem takeOver_walk (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) (hO : InOrder o.st) :
    Walk ρ d.st r.2.st := by
  obtain ⟨_, _, _, a, d₁, _, _, _, ha, _, h1, h2⟩ := takeOver_inv S own o d r h
  exact Walk.quiet (quiet_adoptP ρ ha) (Walk.quiet (quiet_elsewhereP ρ h1 hO)
    (Walk.quiet (quiet_joinP ρ h2) (Walk.nil _)))

variable {Cl : Type}

/-- **"K14, second part": a walk.** -/
theorem k14Second_walk (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hO : ∀ x, s.loc.border = some x → InOrder x.shared.st) : Walk ρ s.st s'.st := by
  obtain ⟨x, a, dot, b, hx, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  exact (takeOver_walk ρ _ _ _ _ _ ha (hO x hx)).trans
    (Walk.quiet (quiet_addRowP ρ hb) (Walk.nil _))

/-- The start lays the shared chain's end that it was handed into the record. -/
theorem start₃E_border (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    ∃ g, s₀.loc.border = some ⟨g, o⟩ := by
  obtain ⟨f, _, hs⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, e⟩ := start₃_inv _ _ _ _ hs
  rw [e]
  exact ⟨_, rfl⟩

theorem k14Second_tidy (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hO : ∀ x, s.loc.border = some x → InOrder x.shared.st) (hT : Tidy s.st) : Tidy s'.st :=
  (k14Second_walk OnBytes.Model.Reading.gl p s s' rs gs h hO).tidy hT

theorem takenSources_tidy (own : Block S₃ Cl) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (takenSources own).decide s rs gs = .ok s')
    (hT : Tidy s.st) : Tidy s'.st := by
  rw [takenSources_same own s s' rs gs h]
  exact hT

/-- **In front of the request's own proximity test the statement is tidy.** -/
theorem tidy_border2 (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut)
    (s₀ s₁ s₂ : S₃)
    (h0 : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) (p : P₁₄)
    (own : Block S₃ Cl)
    (rs rs' : List Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64)))
    (h1 : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s₁)
    (h2 : (takenSources own).decide s₁ rs' gs' = .ok s₂) (hT : Tidy st₁) (hO : InOrder o.st) :
    Tidy s₂.st := by
  obtain ⟨g, hb⟩ := start₃E_border codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s₀ h0
  refine takenSources_tidy own s₁ s₂ rs' gs' h2
    (k14Second_tidy p s₀ s₁ rs gs h1 (fun x hx => ?_) ?_)
  · rw [hb] at hx
    rw [← Option.some.inj hx]
    exact hO
  · rw [start₃E_st codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s₀ h0]
    exact hT

/-- **The same at the start of the first chain's last record and the shared chain's end.** -/
theorem tidy_border2_at {XiPub : Type} (p : P₁₄) (x : XiPub) (e₁ : First.S)
    (e₂ : Proof.SharedEnd) (s₀ s₁ s₂ : S₃) (h0 : startAtEnds p x e₁ e₂ = .ok s₀)
    (own : Block S₃ Cl) (rs rs' : List Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64)))
    (h1 : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s₁)
    (h2 : (takenSources own).decide s₁ rs' gs' = .ok s₂) (hT : Tidy e₁.st) (hO : InOrder e₂.st) :
    Tidy s₂.st := by
  have h0' : (match firstOfS e₁ with
      | none => Except.error "the first chain's end names no W"
      | some f => start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending
          (sharedOfEnd e₂)) = .ok s₀ := h0
  split at h0'
  · cases h0'
  · rename_i f hf
    have hst : f.st = e₁.st := by
      unfold firstOfS at hf
      cases he : e₁.firstEnd? with
      | none =>
        rw [he] at hf
        cases hf
      | some e =>
        rw [he] at hf
        rw [← Option.some.inj hf]
    exact tidy_border2 p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (sharedOfEnd e₂)
      s₀ s₁ s₂ h0' p own rs rs' gs gs' h1 h2 (hst ▸ hT) hO

/-- **A try**: the start hands on an untidy statement as it is. -/
theorem not_tidy_start (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h0 : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) (hT : ¬ Tidy st₁) :
    ¬ Tidy s₀.st := by
  rw [start₃E_st codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s₀ h0]
  exact hT

end VerifiableInference.Desc.Third.Law
