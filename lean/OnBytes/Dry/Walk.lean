-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/Walk.lean: THE WALK: the prover's chain (chainO, OnBytes/Prover/Defs.lean) at two
strategies, side by side. The head of OnBytes/Dry/Side.lean says what is shown and how; that file
has the parts, this one the chain.

General lemma. This file states no goal of the release. It serves OnBytes/Dry/View.lean.

Main name.
  tied_chainO   for a test m on names that defers leaves, the request tree's leaves, this chain's
      Fiat-Shamir oracle and its g; a test "keep" on entries of a log that keeps no leaf; coins that
      are alike, and the same if G has a member; two strategies that agree along every ρ in G; two
      logs with the same kept entries if G has a member: the two chains go side by side, and end in
      the relation RG.

Limits. One slot, one chain. G and rd are letters.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.Side

set_option autoImplicit false

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable (m : ON₂ → Bool) (t : Tag) (hm : RunMarks m t) (keep : QA (typedOracleFamily lam K L) → Bool)
  (hkeep : ∀ (q : LeafIn L) (r : Dig lam), keep (⟨OracleName.leaf, q, r⟩ : QA (typedOracleFamily lam K L)) = false)
  (cms : List (Dig lam)) (x : Option X) (co co' : Coins lam L) (cap : ℕ → ℕ) (hco : Alike co co')
include hm hkeep hco

/-- **The chain at two strategies, side by side.** -/
theorem tied_chainO : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ σ' : Strat s Unit) (G : Rho s → Prop) (rd : OPos s → Bool),
    (∀ ρ, G ρ → AgreeAt s rd ρ σ σ') → ((∃ ρ, G ρ) → co' = co) →
    ∀ l l' : Trace (typedOracleFamily lam K L), Lg (∃ ρ, G ρ) keep l l' →
    TL m (RG s A W G rd σ keep) l l' (chainO t cms x co cap s A W embS embP i ph σ)
      (chainO t cms x co' cap s A W embS embP i ph σ')
  | [], _, _, _, _, _, _, _, _, G, _, _, _, l, l', hl =>
    .done ⟨⟨rfl, rfl⟩, fun z z' hz hz' => by
      obtain rfl := Res.ok.inj hz
      obtain rfl := Res.ok.inj hz'
      exact ⟨trivial, fun hG => ⟨hl ⟨_, hG⟩, trivial, rfl⟩⟩⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m₁, k), (m₂, k'), G, rd, hA, hc, l, l', hl => by
    have hA' : ∀ (c : r.Chal) (ρ' : Rho s), G ((c, ρ') : Rho (r :: s)) →
        m₁.2 = m₂.2 ∧ (∀ p, rd (.inl p) = true → r.rd m₁.1 p = r.rd m₂.1 p) ∧
          AgreeAt s (fun p => rd (.inr p)) ρ' (k c) (k' c) := fun c ρ' h => hA (c, ρ') h
    have hpl : (∃ ρ, G ρ) → m₁.2 = m₂.2 := fun ⟨⟨c₀, ρ₁⟩, h⟩ => (hA' c₀ ρ₁ h).1
    have hsy : (∃ ρ, G ρ) → ∀ p, rd (.inl p) = true → r.rd m₁.1 p = r.rd m₂.1 p :=
      fun ⟨⟨c₀, ρ₁⟩, h⟩ => (hA' c₀ ρ₁ h).2.1
    have tail : ∀ (c : r.Chal) (ph' : Phase lam)
        (kp kp' : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq rq' : Option (Dig lam))
        (l₁ l₁' : Trace (typedOracleFamily lam K L)), Lg (∃ ρ, G ρ) keep l₁ l₁' → kp.1.1 = m₁.1 →
        (kp.1.2 = m₁.2 ∨
          (∃ g n, a.kind = .lo ∧ w.grJ = some g ∧
            kp.1.2 = a.plain.symm ((a.plain m₁.2).1, g.put n (a.plain m₁.2).2)) ∨
          (∃ g n, a.kind = .sh ∧ w.gr0 = some g ∧
            kp.1.2 = a.plain.symm (g.put n (a.plain m₁.2).1, (a.plain m₁.2).2))) →
        ((∃ ρ, G ρ) → kp.1.2 = kp'.1.2 ∧
          (∀ p, rd (.inl p) = true → r.rd kp.1.1 p = r.rd kp'.1.1 p) ∧
          TreesSame w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 kp'.2.1 ∧
          TreesSame w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 kp'.2.2 ∧ rq = rq') →
        TL m (RG (r :: s) (a, A) (w, W) G rd ((m₁, k) : Strat (r :: s) Unit) keep) l₁ l₁'
          ((chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph' (k c)).bind fun u => .pure (u.map (consP c kp rq)))
          ((chainO t cms x co' cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph' (k' c)).bind fun u => .pure (u.map (consP c kp' rq'))) :=
      fun c ph' kp kp' rq rq' l₁ l₁' h₁ hP1 hP2 hK =>
        TiedL.bind (tied_chainO s A W _ _ (i + 1) ph' (k c) (k' c)
          (fun ρ' => G ((c, ρ') : Rho (r :: s))) (fun p => rd (.inr p))
          (fun ρ' h => (hA' c ρ' h).2.2) (fun ⟨_, h⟩ => hc ⟨_, h⟩) l₁ l₁'
          (fun ⟨_, h⟩ => h₁ ⟨_, h⟩)) fun u l₂ v l₂' hR =>
          .done (RG.cons G rd m₁ k keep c kp kp' rq rq' hP1 hP2 hK u l₂ v l₂' hR)
    simp only [chainO, hco.salt, hco.slot, hco.path]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none => exact .done (RG.noFormat _ _ _ _ _ _ _ _ _)
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hk := (act_own e).1
          refine TiedL.bind (tl_treesO m _ keep hm.leaf hkeep co.pad co'.pad (co.leaf i true)
            (co'.leaf i true) w.posAtJ (fun p => embS (.inl p)) m₁.1 m₂.1 0 w.depthJ l l' hl)
            fun TJ l₁ TJ' l₁' hT => ?_
          have hroot := TreesAt.roots _ _ _ hT.1
          refine TiedL.bind (tl_fsO m _ keep w.chal t hm.fb
            (fun β => (⟨i, h.withLate (lateInstancePart L i x), TJ.map TreeK.root, embP (.inl (.inr β))⟩ :
              FbIn lam L t))
            (fun β => (⟨i, h.withLate (lateInstancePart L i x), TJ'.map TreeK.root, embP (.inl (.inr β))⟩ :
              FbIn lam L t))
            (a.plain m₁.2).2 (a.plain m₂.2).2 (fun _ => by rw [hroot]) (fun ho => by rw [hpl ho])
            w.grJ (cap i) l₁ l₁' hT.2)
            (tl_onFs m _ keep w.grJ (a.plain m₁.2).2 (a.plain m₂.2).2 i _ _
              (fun _ _ _ => RG.ranOut _ _ _ _ _ _ _ _ _ _) fun β β' ans l₂ l₂' hp h₂ => ?_)
          refine tail (w.chal ans.1) (next (List.ofFn ans.2))
            ((m₁.1, a.plain.symm ((a.plain m₁.2).1, β)), [], TJ)
            ((m₂.1, a.plain.symm ((a.plain m₂.2).1, β')), [], TJ') none none l₂ l₂' h₂ rfl
            (puts_lo hk m₁.2 hp) fun ho => ⟨?_, hsy ho, trivial, ?_, rfl⟩
          · show a.plain.symm ((a.plain m₁.2).1, β) = a.plain.symm ((a.plain m₂.2).1, β')
            rw [PutRel.eq (by rw [hpl ho]) hp, hpl ho]
          · have h' := hT.1
            rw [hc ho] at h'
            exact TreesAt.same (fun p => rd (.inl p)) (hsy ho) 0 TJ TJ' h'
        | false =>
          have hk := (act_shared e).1
          refine TiedL.bind (tl_treesO m _ keep hm.leaf hkeep co.pad co'.pad (co.leaf i false)
            (co'.leaf i false) w.posAt0 (fun p => embS (.inl p)) m₁.1 m₂.1 0 w.depth0 l l' hl)
            fun T0 l₁ T0' l₁' hT => ?_
          have hroot := TreesAt.roots _ _ _ hT.1
          refine TiedL.bind (tl_fsO m _ keep w.chal t hm.fb
            (fun β => (⟨i, h, T0.map TreeK.root, embP (.inl (.inl β))⟩ : FbIn lam L t))
            (fun β => (⟨i, h, T0'.map TreeK.root, embP (.inl (.inl β))⟩ : FbIn lam L t))
            (a.plain m₁.2).1 (a.plain m₂.2).1 (fun _ => by rw [hroot]) (fun ho => by rw [hpl ho])
            w.gr0 (cap i) l₁ l₁' hT.2)
            (tl_onFs m _ keep w.gr0 (a.plain m₁.2).1 (a.plain m₂.2).1 i _ _
              (fun _ _ _ => RG.ranOut _ _ _ _ _ _ _ _ _ _) fun β β' ans l₂ l₂' hp h₂ => ?_)
          refine tail (w.chal ans.1) (next (List.ofFn ans.2))
            ((m₁.1, a.plain.symm (β, (a.plain m₁.2).2)), T0, [])
            ((m₂.1, a.plain.symm (β', (a.plain m₂.2).2)), T0', []) none none l₂ l₂' h₂ rfl
            (puts_sh hk m₁.2 hp) fun ho => ⟨?_, hsy ho, ?_, trivial, rfl⟩
          · show a.plain.symm (β, (a.plain m₁.2).2) = a.plain.symm (β', (a.plain m₂.2).2)
            rw [PutRel.eq (by rw [hpl ho]) hp, hpl ho]
          · have h' := hT.1
            rw [hc ho] at h'
            exact TreesAt.same (fun p => rd (.inl p)) (hsy ho) 0 T0 T0' h'
      | join ρ₀ =>
        have hk := (act_join e).1
        refine TiedL.bind (tl_treesO m _ keep hm.leaf hkeep co.pad co'.pad (co.leaf i true)
          (co'.leaf i true) w.posAtJ (fun p => embS (.inl p)) m₁.1 m₂.1 0 w.depthJ l l' hl)
          fun TJ l₁ TJ' l₁' hTJ => ?_
        refine TiedL.bind (tl_treesO m _ keep hm.leaf hkeep co.pad co'.pad (co.leaf i false)
          (co'.leaf i false) w.posAt0 (fun p => embS (.inl p)) m₁.1 m₂.1 0 w.depth0 l₁ l₁' hTJ.2)
          fun T0 l₂ T0' l₂' hT0 => ?_
        have hrJ := TreesAt.roots _ _ _ hTJ.1
        have hr0 := TreesAt.roots _ _ _ hT0.1
        refine TiedL.bind (tl_ask m _ keep (OracleName.g t) hm.g
          (⟨i, ρ₀, TJ.map TreeK.root, embP (.inl (.inr (a.plain m₁.2).2))⟩ : JoiningRoundQuery lam L t)
          (⟨i, ρ₀, TJ'.map TreeK.root, embP (.inl (.inr (a.plain m₂.2).2))⟩ : JoiningRoundQuery lam L t)
          fun _ => Lg.same (fun ho => by rw [hrJ, hpl ho]) hT0.2) fun c l₃ c' l₃' hcc => ?_
        obtain ⟨rfl, h₃⟩ := hcc
        refine TiedL.bind (tl_ask m _ keep OracleName.rleaf hm.rleaf (List.ofFn c ++ co.rsalt)
          (List.ofFn c ++ co'.rsalt) fun _ => Lg.same (fun ho => by rw [hc ho]) h₃)
          fun d l₄ d' l₄' hdd => ?_
        obtain ⟨rfl, h₄⟩ := hdd
        refine TiedL.bind (tl_refl m _ keep _ l₄ l₄' h₄) fun rq l₅ rq' l₅' hrq => ?_
        obtain ⟨rfl, h₅⟩ := hrq
        refine TiedL.bind (tl_fsO m _ keep w.chal t hm.fb
          (fun β => (⟨i, .f4 cms (List.ofFn rq), T0.map TreeK.root, embP (.inl (.inl β))⟩ :
            FbIn lam L t))
          (fun β => (⟨i, .f4 cms (List.ofFn rq), T0'.map TreeK.root, embP (.inl (.inl β))⟩ :
            FbIn lam L t))
          (a.plain m₁.2).1 (a.plain m₂.2).1 (fun _ => by rw [hr0]) (fun ho => by rw [hpl ho])
          w.gr0 (cap i) l₅ l₅' h₅)
          (tl_onFs m _ keep w.gr0 (a.plain m₁.2).1 (a.plain m₂.2).1 i _ _
            (fun _ _ _ => RG.ranOut _ _ _ _ _ _ _ _ _ _) fun β β' ans l₆ l₆' hp h₆ => ?_)
        refine tail (w.chal ans.1) (.shr (List.ofFn ans.2) c)
          ((m₁.1, a.plain.symm (β, (a.plain m₁.2).2)), T0, TJ)
          ((m₂.1, a.plain.symm (β', (a.plain m₂.2).2)), T0', TJ') (some rq) (some rq) l₆ l₆' h₆ rfl
          (puts_sh hk m₁.2 hp) fun ho => ⟨?_, hsy ho, ?_, ?_, rfl⟩
        · show a.plain.symm (β, (a.plain m₁.2).2) = a.plain.symm (β', (a.plain m₂.2).2)
          rw [PutRel.eq (by rw [hpl ho]) hp, hpl ho]
        · have h' := hT0.1
          rw [hc ho] at h'
          exact TreesAt.same (fun p => rd (.inl p)) (hsy ho) 0 T0 T0' h'
        · have h' := hTJ.1
          rw [hc ho] at h'
          exact TreesAt.same (fun p => rd (.inl p)) (hsy ho) 0 TJ TJ' h'

end OnBytes.Dry

#print axioms OnBytes.Dry.tied_chainO
