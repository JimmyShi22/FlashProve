-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVBelow.lean: the round-by-round errors of the batching with a value shown, as
probabilities, are at most a bound, from four inequalities on numbers; and countability.

The error that is listed for each round of a batching step of an interactive oracle proof (`B.nums`,
Cb/Ld/LdBattV.lean) is, as a probability, at most κ, given four inequalities between numbers
(knowledge soundness at these errors, for each fixed tuple of messages: `Spec.battV_goodAt`,
Cb/Ld/LdBattV.lean, under its hypotheses); and a side condition of countability on positions,
symbols and plain parts (`CtbSh`, CompileK/ImplCountable.lean). Definitions, statements and proofs.
The analogue of the batching's parts of Cb/Ld/LdKappaList.lean, Cb/Req1/LdSegRefBelow.lean,
Cb/Req1/LdReqRefCtb.lean. The batching with a value shown is the block `B.battV` of
Cb/Ld/LdBattV.lean; its three moves are the list `X.prog` of Cb/Ld/LdBattVSeg.lean.

Main names:
  `B.Kap κ`: the four inequalities: the evader's number is at most κ times the number of its seeds;
    1 ≤ κ |E|; n ≤ κ |E| (asked only if there is a column variable); 1 ≤ κ (|E| - 1). The last round
    has the error 0.
  `Spec.battV_kap`: `B.Kap κ` ⇒ every round's error, as a probability, is at most κ (`Err.Below`).
  `Spec.ldBattVSeg_below`: if the block's list of errors has `Err.Below` at κ, the list of the three
    moves has `LdProg.Below` at κ.
  `Spec.battV_ctb`, `Spec.ldBattVSeg_ctb`: positions, symbols and plain parts are countable, of the
    block (`CtbSh`) and of the three moves (`LdProg.Ctb`).

Limits: this file says nothing on the value of any number. κ is a bound for each round; the sum of
the k + 4 errors is not spoken of.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSegProofs
import Cb.Ld.LdKappaList
import Cb.Req1.LdSegRefBelow
import Cb.Req1.LdReqRefCtb

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

/-- The batching with a value shown: its numbers. -/
structure BattVPar.Kap {E : Type} [Field E] [Fintype E] (B : BattVPar E) (κ : ℝ≥0∞) : Prop where
  ev   : (B.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card B.Z.D : ℝ≥0∞)
  coef : ((1 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  col  : 0 < B.k → (B.n : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  dum  : ((1 : ℕ) : ℝ≥0∞) ≤ κ * ((Fintype.card E - 1 : ℕ) : ℝ≥0∞)

namespace Spec

def battV_kap : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattVPar E) (Ex : ExtSpec) (Kc : Type) (κ : ℝ≥0∞),
    B.Kap κ → Err.Below (B.nums Ex Kc).err κ

def ldBattVSeg_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (κ : ℝ≥0∞),
    Err.Below (X.bt.nums X.C.E0 Kc).err κ → (X.prog St₁ fz Az).Below κ

def battV_ctb : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BattVPar E) (Ex : ExtSpec), CtbSh (B.battV Ex).shape

def ldBattVSeg_ctb : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).Ctb

end Spec

theorem battV_kap : Spec.battV_kap := by
  intro E _ _ B Ex Kc κ h
  have hp : B.our.par.Kap κ :=
    ⟨h.coef, fun f hf => by
      rcases List.mem_append.1 hf with h1 | h1
      · have hk : 0 < B.k := by
          by_contra h0
          have : B.k = 0 := by omega
          rw [show B.our.fmt = List.replicate B.k (pfCube E B.n) from rfl, this] at h1
          exact absurd h1 (by simp)
        rw [List.eq_of_mem_replicate h1]
        exact h.col hk
      · rw [List.mem_singleton.1 h1]
        show ((1 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card (pDummy E 1).Ch : ℝ≥0∞)
        rw [psc_our_card E 1]
        exact h.dum⟩
  exact Err.Below.app (⟨h.ev, trivial⟩ : Err.Below (IOR.Nums.draw Kc B.Z.D B.nx Ex B.Z.err).err κ)
    (ldKappa_psc B.our.par Ex κ hp)

theorem ldBattVSeg_below : Spec.ldBattVSeg_below := by
  intro E Kc _ _ X St₁ fz Az κ h
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.sub X.m0 X.m1 (.one X.link)).chain = .one X.link := by rw [LdMv.chain]
  unfold LdTenVD.prog LdTenVD.stepIn LdTenVD.stepOut
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, c2, errBelow_one]
  exact ⟨⟨⟨LdProg.below_nil _ κ, hp _ _ _ _ _ _⟩, h⟩, hp _ _ _ _ _ _⟩

theorem battV_ctb : Spec.battV_ctb := fun _ _ _ B Ex =>
  ctbSh_append (ctb_drawR _ _ Ex) (ctb_pscP B.our.par Ex)

theorem ldBattVSeg_ctb : Spec.ldBattVSeg_ctb := fun E _ _ _ X _ _ _ =>
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩,
          ctb_subOne _ (battV_ctb E X.bt X.C.E0)⟩,
      trivial⟩

end Cb
