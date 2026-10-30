-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ThruYesBase.lean: YesAt (E2E/BridgeLink.lean) from the run, and from the run at the prover that
the family's prover reads through. What the decision accepts is a sentence on runC's value, so it
crosses by runC_rows_thru (Johnson/Desc/ProofFile/Honest/ThruRows.lean) as it stands: acceptance
may be proved at the filling's prover, by either rule, and the family's strategies get it by
views_of_stratC.

  yesAt_of_runs        YesAt, from that at every tied input, coin and list of challenges outside
                       the abort set and the fall
  yesAt_of_base        YesAt at the rows' prover, from the run at the prover read through: the
                       premises speak at that prover, at its silent set and its falls
  honestBC_bad_rows, honestBC_hid_rows, honestBC_stop0_rows   the record's abort sets, at the rows'
                       prover, written at the prover read through: the form in which they are
                       bounded

Limits.
  * hrows, hk, hcols and the trace are premises.
  * Nothing on how likely a stop or a fall is; nothing on completeness, soundness or hiding.
-/
import E2E.BridgeLink
import Johnson.Desc.ProofFile.Honest.ThruRowsMore

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD chainsOf wiresOf view₁ view₂ view₃)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides fallAt drawsAt drawsLo drawsSh runC
  viewsFall silentAt Tied DataFits halvedAll Committer CommittedColumns trAtC views_of_stratC
  badB hidB stop0B)

section BC
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (G : Sides F B W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂]
  [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **YesAt, from the run.** At every tied input and coin and every list of challenges outside the
abort set and the fall: the run returns, and the description accepts its views. -/
theorem yesAt_of_runs (hp : F.planOk = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover H) = true)
    {pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀ → Rc → Xi → Prop}
    {TiedX : ℕ → W₀ × Rc × Sd → Xi → Prop} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hT : ∀ n w x, TiedX n w x → Tied D F (G.prover H) (J n) ext (pubJ n) sh Rel w x)
    (hdebt : ∀ n w x (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) ρ,
      TiedX n w x →
      ρ ∉ ((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).at n).withheld w x ∪
        fallBC C D tF tJ t3 F silent B G H J sh ext n w x c →
      ∃ r, runC F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
          (drawsAt C D tF tJ t3 ρ) = .ok r ∧
        F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true) :
    YesAt C D tF tJ t3 F silent B G H J sh ext K chal TiedX := by
  intro n w x c hx ρ _ hρ
  have ht := hT n w x hx
  obtain ⟨r, hr, hyes⟩ := hdebt n w x c ρ hx hρ
  obtain ⟨v1, v2, v3, -, -, -⟩ := views_of_stratC C D tF tJ t3 F B (G.prover H)
    (J n c.1.2 default) (J n c.1.2 c.2.2) sh w c.1.1 x c.2.1 (ext w) ρ hr hp hD h4
    (ht.key _ _) (ht.key _ _) ht.start.symm ht.table
  have e : (((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).strat n w x c).run ρ).1 =
      trAtC C D tF tJ t3 F B (G.prover H) (J n c.1.2 default) (J n c.1.2 c.2.2) sh w c.1.1 x
        c.2.1 ρ := rfl
  rw [e, v1, v2, v3]
  exact hyes

end BC

section Base
variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Sc Xc TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD)
  (tF : TF) (tJ : TJ) (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (G : Sides F B W₀' Rc' Ky Tr X₀ X)
  (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (Cm : Committer W₀' Rc' Sc Xc Xi Ky) (item₀ : ℕ)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀' Rc' Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀' × Rc' × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **YesAt at the rows' prover, from the run at the prover read through.** -/
theorem yesAt_of_base (hp : F.planOk = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = true)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    {pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀' → Rc' → Xi → Prop}
    {TiedX : ℕ → W₀' × Rc' × Sd → Xi → Prop} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hT : ∀ n w x, TiedX n w x →
      Tied D F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J n) ext (pubJ n) sh Rel w x)
    (hcols : ∀ n w x, TiedX n w x → CommittedColumns Cm item₀ H g rd w.1 w.2.1)
    (htr : ∀ n w x, TiedX n w x → (H.trace (g w.1) x).isSome = true)
    (hdebt : ∀ n w x (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) ρ,
      TiedX n w x → silentAt F H (g w.1) (rd w.2.1) x (drawsAt C D tF tJ t3 ρ) = none →
      (∀ r, runC F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
          (drawsAt C D tF tJ t3 ρ) = .ok r →
        viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views = none) →
      ∃ r, runC F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
          (drawsAt C D tF tJ t3 ρ) = .ok r ∧
        F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true) :
    YesAt C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh ext K chal TiedX := by
  refine yesAt_of_runs C D tF tJ t3 F silent B G _ J sh ext hp hD h4 K chal hT ?_
  intro n w x c ρ hx hρ
  have hk' : Cm.key = H.key := hk
  have e := ProofFile.Honest.runC_rows_thru (ρ := drawsAt C D tF tJ t3 ρ)
    (c := ⟨c.2.1.1, c.1.1, c.2.1.2⟩) g rd d G Cm item₀ H w.1 w.2.1 x hd hrows hk' (hcols n w x hx)
  have htr' : ((G.prover (Cm.proverAt item₀ (H.thru g rd d))).trace w.1 x).isSome = true :=
    htr n w x hx
  have h1 := (ProofFile.Honest.withheldC_iff C D tF tJ t3 F silent B
    (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J n) sh ext w x htr' ρ).not.1
    (fun a => hρ (Or.inl a))
  have hsil : silentAt F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w.1 w.2.1 x
      (drawsAt C D tF tJ t3 ρ) = none := by
    cases hs : silentAt F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w.1 w.2.1 x
        (drawsAt C D tF tJ t3 ρ) with
    | none => rfl
    | some z =>
      rw [hs] at h1
      exact absurd rfl h1
  rw [ProofFile.Honest.silentAt_rows_thru g rd d G Cm item₀ H w.1 w.2.1 x _ hrows hk'] at hsil
  have hf := no_fall_of_not_mem C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh
    ext n w x c ρ (fun a => hρ (Or.inr a))
  obtain ⟨r, hr, hy⟩ := hdebt n w x c ρ hx hsil fun r hr => hf r (e.trans hr)
  exact ⟨r, e.trans hr, hy⟩

variable (J₁ : R₂ → R₃ → KeyAndJoiningRoundMessages W₀' Rc' Sd Xi Ky TF TJ T3)
  (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
include hrows hk

/-- The record's public abort set at the rows' prover, written at the prover read through. -/
theorem honestBC_bad_rows :
    (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) J₁ sh ext).Bad =
      {ρ | badB F H (drawsLo C D tF tJ t3 ρ) = true} := by
  show {ρ | badB F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (drawsLo C D tF tJ t3 ρ) = true} = _
  rw [ProofFile.Honest.badB_rows g rd d G Cm item₀ H hrows hk]

/-- The abort set that reads the input. -/
theorem honestBC_hid_rows (w : W₀' × Rc' × Sd) (x : Xi) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) J₁ sh ext).Hid
        w x = {ρ | hidB F H (g w.1) (rd w.2.1) x (drawsLo C D tF tJ t3 ρ) = true} := by
  show {ρ | hidB F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w.1 w.2.1 x
    (drawsLo C D tF tJ t3 ρ) = true} = _
  rw [ProofFile.Honest.hidB_rows g rd d G Cm item₀ H hrows hk]

/-- The shared chain's stop. -/
theorem honestBC_stop0_rows (ρ) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) J₁ sh
      ext).stop0 ρ = stop0B F H (drawsSh C D tF tJ t3 ρ) := by
  show stop0B F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (drawsSh C D tF tJ t3 ρ) = _
  rw [ProofFile.Honest.stop0B_rows g rd d G Cm item₀ H hrows hk]

end Base

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.yesAt_of_runs
#print axioms AtPublicFiles.Bridge.yesAt_of_base
#print axioms AtPublicFiles.Bridge.honestBC_bad_rows
#print axioms AtPublicFiles.Bridge.honestBC_hid_rows
#print axioms AtPublicFiles.Bridge.honestBC_stop0_rows
