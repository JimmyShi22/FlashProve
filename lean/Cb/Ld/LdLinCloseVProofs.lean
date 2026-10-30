-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVProofs.lean: proofs of four statements of Cb/Ld/LdLinCloseV.lean (whole tests on
groups in a batch: the honest side): `ldRunV_run`, `ldRunV_congr`, `ldRunV_local`, `ldRunV_shared`.
(`ldRunV_given`: Cb/Ld/LdLinCloseVRun.lean.)

A whole test beside what is carried is the bridge, then the test kept beside the carried part, then
a step that drops the trivial statement (`ldRunEH`, Cb/Ld/LdLinCloseRun.lean). The honest run is
unfolded once (`ldRunEH_run`; `G.P` nonempty): its transcript is the seed, then the test's
transcript on (the members' pairs; the rows taken in, batched at the seed); its result is a part of
its input.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseV.lean):
  `ldRunV_run`: what a whole test leaves, which does not depend on its transcript.
  `ldRunV_congr`: what the honest prover sends, as a function of the acting part, of its coins and
    of the verifier's messages.
  `ldRunV_local`, `ldRunV_shared`: the test in every slot (`D.loV`), and once by the shared part
    (`D.shV`), as a piece (`PV`).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseVRun

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- three in a row -/
theorem run_three {X₁ X₂ X₃ X₄ : Type} {E₁ E₂ E₃ E₄ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂}
    {R₂ : IOR X₂ E₂ X₃ E₃} {R₃ : IOR X₃ E₃ X₄ E₄} {W₁ W₂ W₃ W₄ : Type} (H₁ : R₁.Honest W₁ W₂)
    (H₂ : R₂.Honest W₂ W₃) (H₃ : R₃.Honest W₃ W₄) (w : W₁) (x : X₁)
    (c : H₁.Coin × (H₂.Coin × H₃.Coin)) (ρ : Rho (R₁.shape ++ (R₂.shape ++ R₃.shape))) :
    ((H₁.seq (H₂.seq H₃)).strat w x c).run ρ =
      (Tr.app ((H₁.strat w x c.1).run (Rho.fst ρ)).1
          (Tr.app ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
                ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2.1).run
              (Rho.fst (Rho.snd (s := R₁.shape) ρ))).1
            ((H₃.strat ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
                    ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2.1).run
                  (Rho.fst (Rho.snd (s := R₁.shape) ρ))).2.2
                ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
                    ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2.1).run
                  (Rho.fst (Rho.snd (s := R₁.shape) ρ))).2.1 c.2.2).run
              (Rho.snd (s := R₂.shape) (Rho.snd (s := R₁.shape) ρ))).1),
        ((H₃.strat ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
                ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2.1).run
              (Rho.fst (Rho.snd (s := R₁.shape) ρ))).2.2
            ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
                ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2.1).run
              (Rho.fst (Rho.snd (s := R₁.shape) ρ))).2.1 c.2.2).run
          (Rho.snd (s := R₂.shape) (Rho.snd (s := R₁.shape) ρ))).2) := by
  rw [Honest.run_seq, Honest.run_seq]
  rfl

/-- a block kept beside an explicit part, oracles and a part of the witness -/
theorem run_keep_carry {Xi Xo Zx Wi Wo Wz : Type} {Ei Eo F : ExtSpec} {R : IOR Xi Ei Xo Eo}
    (H : R.Honest Wi Wo) (w : Wi × Wz) (a : Xi × Zx) (c : H.Coin) (ρ : Rho R.shape) :
    (((H.keep Zx F).carry Wz).strat w a c).run ρ =
      (((H.strat w.1 a.1 c).run ρ).1,
        ((((H.strat w.1 a.1 c).run ρ).2.1, a.2), (((H.strat w.1 a.1 c).run ρ).2.2, w.2))) := by
  have k : ((H.keep Zx F).strat w.1 a c).run ρ =
      (((H.strat w.1 a.1 c).run ρ).1,
        ((((H.strat w.1 a.1 c).run ρ).2.1, a.2), ((H.strat w.1 a.1 c).run ρ).2.2)) :=
    Honest.keepX_run H Zx w.1 a c ρ
  rw [Honest.carry_run, k]
  rfl

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) [Nonempty G.P]
  (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
  (Z : Evader E (G.Row B)) (St₀ Wp : Type) (E₀ : ExtSpec) (T : LdEnd (G.joint Sb sl Z))

/-- The honest run of a whole test beside what is carried, unfolded. -/
theorem ldRunEH_run (w : S.Wit × Wp) (x : (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp)
    (c : Unit × (T.H.Coin × Unit))
    (ρ : Rho ((ldBridge G kp Sb Z St₀ E₀).shape ++ (T.R.shape ++ []))) :
    Strat.run (s := (ldBridge G kp Sb Z St₀ E₀).shape ++ (T.R.shape ++ []))
        ((ldRunEH G kp Sb sl Z St₀ Wp E₀ T).strat w x c) ρ =
      (Tr.app (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := T.R.shape ++ [])
          ((((), ()),
            (Rho.fst (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := T.R.shape ++ []) ρ).1,
            ()) : Tr (ldBridge G kp Sb Z St₀ E₀).shape)
          (Tr.app (s := T.R.shape) (t := [])
            ((T.H.strat (G.wit w.1)
                (batNx Z.ze (G.claims x.1.1 x.2)
                  (Rho.fst (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := T.R.shape ++ []) ρ).1)
                c.2.1).run
              (Rho.fst (s := T.R.shape) (t := [])
                (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := T.R.shape ++ []) ρ))).1 ()),
        ((x.1.2, S.res (T := OMsg.Smp) kp x.2), (S.res (T := OMsg.Wit) kp w.1, w.2))) := by
  refine (run_three (ldBridgeH G kp Sb Z St₀ Wp E₀)
    ((T.H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry (LdCarW kp Wp))
    (ldDropTH kp St₀ Wp E₀) w x c ρ).trans ?_
  rw [run_keep_carry]
  rfl

end

theorem ldRunV_run : Spec.ldRunV_run := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d'
  refine ⟨fun w x c ρ => ?_, fun y τ => rfl⟩
  exact congrArg Prod.snd (ldRunEH_run D.G D.kp D.Sb D.sl D.Z St₀ Wp E₀ D.T w x c ρ)

theorem ldRunV_congr : Spec.ldRunV_congr := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' x x' w w' c ρ hx hw
  refine (congrArg Prod.fst (ldRunEH_run D.G D.kp D.Sb D.sl D.Z St₀ Wp E₀ D.T w x c ρ)).trans
    (Eq.trans ?_
      (congrArg Prod.fst (ldRunEH_run D.G D.kp D.Sb D.sl D.Z St₀ Wp E₀ D.T w' x' c ρ)).symm)
  dsimp only
  rw [hx, hw]

theorem ldRunV_local : Spec.ldRunV_local := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N VA tieB qB hD htie hB hHer
  obtain ⟨g, s⟩ :=
    ldChain_link E S D St₀ Wp E₀ A₀ d d' (fun _ => True) (fun _ => True) hD fun _ _ => trivial
  obtain ⟨hrun, himp⟩ := ldRunV_run E S D St₀ Wp E₀ A₀ d d'
  refine ⟨pieceV_local _ _ _ _ (D.link A₀ d d').R _ _ VA.W0 (D.link A₀ d d').H
      (S.jointCf (D.pre A₀)).rels.rel ((S.sub D.kp).jointCf A₀).rels.rel VA.rel
      (JV.rel (⟨VA.W0, tieB, qB⟩ : JV N ((S.sub D.kp).jointCf A₀))) (D.link A₀ d d').P.bud
      N VA.q qB g.isLocal g.acc g.exact s.noHid (fun _ _ _ h => h.1) ?_ hB,
    hHer⟩
  intro x y w c ρ hR _ hRo
  refine ⟨hRo, ?_⟩
  show tieB w.1 _ _ _
  rw [himp, hrun]
  exact htie x y w hR

theorem ldRunV_shared : Spec.ldRunV_shared := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N VA W0' tieB qB rep yrep nx y₀ hD hact htie hB hHer
  obtain ⟨g, s⟩ :=
    ldChain_link E S D St₀ Wp E₀ A₀ d d' (fun _ => True) (fun _ => True) hD fun _ _ => trivial
  obtain ⟨hrun, himp⟩ := ldRunV_run E S D St₀ Wp E₀ A₀ d d'
  refine ⟨pieceV_shared _ _ _ _ (D.link A₀ d d').R _ _ VA.W0 W0' (D.link A₀ d d').H
      (D.s0 A₀ d d' N VA rep nx) (S.jointCf (D.pre A₀)).rels.rel ((S.sub D.kp).jointCf A₀).rels.rel
      VA.rel (JV.rel (⟨W0', tieB, qB⟩ : JV N ((S.sub D.kp).jointCf A₀))) (D.link A₀ d d').P.bud N
      (fun w0 p => (E₀.prod S.ext).rd (y₀, yrep w0) p) VA.q qB g.isLocal g.acc g.exact s.noHid
      (fun _ _ _ h => h.1) ?_ ?_ ?_ hB,
    hHer⟩
  · intro x y w c ρ hR
    obtain ⟨h1, h2, -⟩ := hact x y w hR
    refine (ldRunV_congr E S D St₀ Wp E₀ A₀ d d' x (rep w.1).1 w.2 (rep w.1).2 c ρ h1 h2).trans ?_
    exact (congrArg Prod.fst
      (Strat.run_map (fun _ => nx w.1) ((D.link A₀ d d').H.strat (rep w.1).2 (rep w.1).1 c) ρ)).symm
  · intro x y w c ρ hR _ hRo
    refine ⟨hRo, ?_⟩
    have e : ((D.s0 A₀ d d' N VA rep nx w.1 c).run ρ).2 = nx w.1 :=
      congrArg Prod.snd
        (Strat.run_map (fun _ => nx w.1) ((D.link A₀ d d').H.strat (rep w.1).2 (rep w.1).1 c) ρ)
    show tieB _ _ _ _
    rw [e, himp, hrun]
    exact htie x y w hR
  · intro x y w ρ T p hR hp
    obtain ⟨a, q, rfl⟩ := ldRunV_given E S D St₀ Wp E₀ A₀ d d' ρ T p hp
    have e := (hact x y w hR).2.2 a
    show (Sum.inr
        (⟨a.1, (S.om a.1).C.T ((S.om a.1).upW (y.2 a.1))
            q⟩ : Σ a, ((S.om a).C.Aa → E)) : E₀.Sym ⊕ Σ a, ((S.om a).C.Aa → E)) =
      Sum.inr ⟨a.1, (S.om a.1).C.T ((S.om a.1).upW (yrep w.1 a.1)) q⟩
    rw [e]

end Cb
