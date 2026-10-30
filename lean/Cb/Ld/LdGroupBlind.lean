-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupBlind.lean: the honest prover of the first part of a run on a group hands the kept
pairs and the further witness on unchanged; for all else that it puts out it looks, of its witness,
at the members' pairs alone.

In standard terms: a run on a group (`ldRunG`, with the honest side `ldRunGH`, Cb/Ld/LdGroup.lean;
in which sense it is "the first part of a run": that head's limits) is a batching round on the
linear claims on several oracle messages, followed by an interactive oracle reduction on these
messages' words, taken as one word.

Statements (in `Cb.Spec`) and proofs. Facts on the term `ldRunGH` of Cb/Ld/LdGroup.lean, for any
block of a proximity test in it; nothing is assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.
The term itself needs the group's set of common long positions, `G.P`, to be nonempty.

Main names:
  `Spec.ldGroup_blind_run`: for two witnesses whose members of the group have the same (message,
    randomness), at the same explicit part, coins and verifier messages the two runs have the same
    transcript, the same new explicit part, and end with the same witness of the test.
  `Spec.ldGroup_blind_carry`: the kept pairs and the further witness are handed on unchanged.

So, at the same explicit part, coins and verifier messages, what stands in oracle messages outside
the group (masks of later blocks, their pads, the randomness of those messages) is neither read nor
changed.
The link of Cb/Ld/LdGroupSeg.lean (`GHeld.link`) has this honest side, at the block of
Cb/Ld/LdGroupFold.lean: the two facts apply to it as they are.

Limits: this file says nothing on laws of distributions.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

namespace Spec

def ldGroup_blind_run : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (b : LdJoint E)
      (Bk : LdBlock (G.joint Sb sl Z) b) (w w' : S.Wit × Wp) x c ρ,
    G.wit w'.1 = G.wit w.1 →
    (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w' x c).run ρ).1 =
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w x c).run ρ).1 ∧
    (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w' x c).run ρ).2.1 =
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w x c).run ρ).2.1 ∧
    (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w' x c).run ρ).2.2.1 =
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w x c).run ρ).2.2.1

def ldGroup_blind_carry : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (b : LdJoint E)
      (Bk : LdBlock (G.joint Sb sl Z) b) (w : S.Wit × Wp) x c ρ,
    (((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w x c).run ρ).2.2.2 =
      (S.res (T := OMsg.Wit) kp w.1, w.2)

end Spec

/-- a run of the honest prover, written out: the block's run on the members' pairs; the carried part
beside it -/
theorem ldRunGH_run {E B St₀ Wp : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S)
    [Nonempty G.P] (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
    (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) {b : LdJoint E}
    (Bk : LdBlock (G.joint Sb sl Z) b) (w : S.Wit × Wp) x c ρ :
    ((ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).strat w x c).run ρ =
      (Tr.app (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).1
          ((Bk.H.strat (G.wit w.1)
              (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1.1 c.2).run
            (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) ρ)).1,
        ((((Bk.H.strat (G.wit w.1)
                (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1.1 c.2).run
              (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) ρ)).2.1,
            (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1.2),
          (((Bk.H.strat (G.wit w.1)
                (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1.1 c.2).run
              (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) ρ)).2.2,
            (S.res (T := OMsg.Wit) kp w.1, w.2)))) := by
  have h1 := Honest.run_seq (ldBridgeH G kp Sb Z St₀ Wp E₀)
    ((Bk.H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry (LdCarW kp Wp)) w x c ρ
  refine h1.trans ?_
  rw [Honest.carry_run]
  have h2 := Honest.keepX_run Bk.H (LdCarX kp St₀) (G.wit w.1)
    (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1 c.2
    (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) ρ)
  exact congrArg
    (fun r =>
      (Tr.app (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).1 r.1,
        (r.2.1, (r.2.2, (S.res (T := OMsg.Wit) kp w.1, w.2))))) h2

theorem ldGroup_blind_carry : Spec.ldGroup_blind_carry := by
  intro E B St₀ Wp _ _ _ S G _ kp _ Sb sl Z E₀ b Bk w x c ρ
  rw [ldRunGH_run]

theorem ldGroup_blind_run : Spec.ldGroup_blind_run := by
  intro E B St₀ Wp _ _ _ S G _ kp _ Sb sl Z E₀ b Bk w w' x c ρ h
  have hb : (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w' x c.1).run (Rho.fst ρ)).1 =
        (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).1 ∧
      (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w' x c.1).run (Rho.fst ρ)).2.1 =
        (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1 := ⟨rfl, rfl⟩
  rw [ldRunGH_run, ldRunGH_run, h, hb.1, hb.2]
  exact ⟨rfl, rfl, rfl⟩

end Cb
