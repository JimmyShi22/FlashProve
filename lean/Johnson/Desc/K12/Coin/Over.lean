-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Over.lean: FROM A BLOCK's PLAIN LAW AT ITS OWN RECORD TO ANY BLOCK THAT STANDS
OVER IT: a seat of whatever make, over another state and another type of claims. Statements and
proofs.

`leads_seated` (Inside.lean) serves a seat made by `Block.inside`. A description may seat a kind's
block otherwise (asks in front of it; its own two halves; another type of claims). What the law's
way over needs of the seat is one sentence on its STEP:

  `Over p B' R R'`: B' declares as many rounds as p's block; where B'.step goes from s to s', on
    whatever rounds and columns, taking k columns: there are t with R s t and t' with R' s t' s'
    such that p's block's step goes from t to t' on the same rounds and columns, taking k; and R
    names at most one t for an s.
  `over`: the piece with B' in the block's place: the same stretch, the same errors.
  `over_out`, `leads_over`: **the law goes over**, at the same errors: the promise is asked at the t
    that R names; the relation holds at (t, t').
  `over_inside`: `Block.inside enter leave` is such a seat.
A rule for every block: a tool.
-/
import Johnson.Desc.K12.Coin.Inside

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {S T Cl Cl' W : Type} {C : CK} {F : Frame}

/-- What the law's way over asks of a seat. -/
structure Over (p : Piece C F T Cl W) (B' : Block S Cl') (R : S → T → Prop)
    (R' : S → T → S → Prop) : Prop where
  rounds : B'.rounds.length = p.b.rounds.length
  step : ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ),
    B'.step F.ft s rs cols = .ok (s', k) →
    ∃ t t', R s t ∧ p.b.step F.ft t rs cols = .ok (t', k) ∧ R' s t' s'
  one : ∀ s t₁ t₂, R s t₁ → R s t₂ → t₁ = t₂

/-- The piece with B' in the block's place. -/
def over (p : Piece C F T Cl W) (B' : Block S Cl') : Piece C F S Cl' W :=
  ⟨B', p.base, p.ds, p.back, fun _ _ w => w, p.err⟩

theorem over_out (p : Piece C F T Cl W) (B' : Block S Cl') (R : S → T → Prop)
    (R' : S → T → S → Prop) (hO : Over p B' R R') (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : (over p B').ior.red.out a τ = some b) :
    ∃ t t', R a.1 t ∧ p.ior.red.out (t, a.2) τ = some (t', b.2) ∧ R' a.1 t' b.1 := by
  obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
  have hs' : (if sTests C p.stage a.2 τ then
      (over p B').run a.1 (sView C p.stage a.2 τ) else none) = some s' := hs
  split at hs'
  · rename_i ht
    have hc := (chainOne _ _ _ _ _ _).1 (toOptionOk hs')
    obtain ⟨hl, s₁, k, hst, he⟩ := (foldOne _ _ _ _ _ _).1 hc
    have hl' : (((sView C p.stage a.2 τ).rounds ++ p.back).take B'.rounds.length).length =
        B'.rounds.length := hl
    have hst' : B'.step F.ft a.1 (((sView C p.stage a.2 τ).rounds ++ p.back).take B'.rounds.length)
        (sView C p.stage a.2 τ).opened = .ok (s₁, k) := hst
    have e₂ : ([] : List Fmt.RoundView) =
        ((sView C p.stage a.2 τ).rounds ++ p.back).drop B'.rounds.length :=
      congrArg (fun x => x.2.1) he
    have e₃ : ([] : List OpenedColumn) = (sView C p.stage a.2 τ).opened.drop k :=
      congrArg (fun x => x.2.2) he
    rw [hO.rounds] at hl' hst' e₂
    obtain ⟨t, t', h1, h2, h3⟩ := hO.step a.1 _ _ s₁ k hst'
    have e₁ : s' = s₁ := congrArg Prod.fst he
    refine ⟨t, t', h1, ?_, e₁ ▸ h3⟩
    have hf : foldBlocks F.ft [p.b] t ((sView C p.stage a.2 τ).rounds ++ p.back)
        (sView C p.stage a.2 τ).opened = .ok (t', [], []) :=
      (foldOne _ _ _ _ _ _).2 ⟨hl', t', k, h2, Prod.ext rfl (Prod.ext e₂ e₃)⟩
    have hr : p.run t (sView C p.stage a.2 τ) = some t' := by
      show (chainAt p.b.name F.ft [p.b] t
        ⟨(sView C p.stage a.2 τ).rounds ++ p.back, (sView C p.stage a.2 τ).opened⟩).toOption = _
      rw [(chainOne _ _ _ _ _ _).2 hf]
      rfl
    show ((if sTests C p.stage a.2 τ then p.run t (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some _
    rw [if_pos ht, hr]
    rfl
  · cases hs'

/-- **The law goes over to whatever block stands over the kind's.** -/
theorem leads_over (p : Piece C F T Cl W) (B' : Block S Cl') (R : S → T → Prop)
    (R' : S → T → S → Prop) (hO : Over p B' R R') (on : T × F.E.Str → Prop)
    (Q : T × F.E.Str → T × F.E.Str → Prop) (h : p.ior.red.Leads on Q p.err) :
    (over p B').ior.red.Leads (fun a => ∀ t, R a.1 t → on (t, a.2))
      (fun a b => ∃ t t', R a.1 t ∧ R' a.1 t' b.1 ∧ Q (t, a.2) (t', b.2)) (over p B').err := by
  intro a ha
  by_cases he : ∃ t, R a.1 t
  · obtain ⟨t, ht⟩ := he
    refine Doomed.mono _ _ ?_ (h (t, a.2) (ha t ht))
    intro τ hτ b hb
    obtain ⟨t₁, t', h1, h2, h3⟩ := over_out p B' R R' hO a τ b hb
    obtain rfl := hO.one a.1 t t₁ ht h1
    exact ⟨t, t', ht, h3, hτ _ h2⟩
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨t, _, h1, _⟩ := over_out p B' R R' hO a τ b hb
    exact absurd ⟨t, h1⟩ he

/-- A seat made by `Block.inside` is such a seat. -/
theorem over_inside (p : Piece C F T Cl W) (enter : S → Except String T)
    (leave : S → T → Except String S) :
    Over p (p.b.inside enter leave) (fun s t => enter s = .ok t)
      (fun s t' s' => leave s t' = .ok s') where
  rounds := rfl
  step := fun s rs cols s' k h => (Seat.step_inside F.ft enter p.b leave s s' rs cols k).1 h
  one := fun _ _ _ h₁ h₂ => Except.ok.inj (h₁.symm.trans h₂)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.over_out
#print axioms VerifiableInference.Desc.K12.Coin.leads_over
#print axioms VerifiableInference.Desc.K12.Coin.over_inside
