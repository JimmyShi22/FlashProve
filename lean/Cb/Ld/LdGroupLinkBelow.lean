-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupLinkBelow.lean: every round-by-round error of the link bridge-to-fold of a group, as a
probability, is at most one number, from numbers.

In the words of lean/GLOSSARY.md: bridge: the bridge is the one-round step at the head of a run on a
group, be it a whole test or a segment's closing. arrangement: how the rows of a group's words are
laid onto a cube before the fold, and which of them are kept beside it. fold: a step, of several
rounds, that combines the rows of a table of words into one word, under coefficients that the
verifier's point gives, and carries the claim along (the map on vectors: `foldV`, Cb/Ld/LdRel.lean).

Statements as theorems, proofs. Rules of the framework and the definitions of the errors only;
nothing of a text is rendered here.
`Err.Below ε κ` (Iop/InteractiveOracleProof.lean): in every round, the count of bad verifier messages is at most κ
times the number of verifier messages. No sum of errors is formed.
In `ldGroup_link_below` the group's set of common long positions, `G.P`, is nonempty, and every
oracle message is a member of the group or kept (hc) (the link needs both).

Main names:
  `ld_sum_below`: the zero-knowledge sumcheck that folds (Cb/Ld/LdSum.lean: `Y.err Lst mC mS mW`),
    k + 1 rounds, every verifier message a challenge in `Y.Ch`. Each of its errors, as a
    probability, is at most κ if, in the first round, Lst 0 ≤ κ · |Ch|, and in round i + 1 (i < k),
    mC (i + 1) + [if i + 1 ≤ h: mS (i + 1) + mW (i + 1)] + Lst i · n ≤ κ · |Ch|.
  `ldGroup_link_below`: the link `Hd.link ..` (Cb/Ld/LdGroupSeg.lean). Each of its errors, as a
    probability, is at most κ if, in the bridge's round, L · Z.err ≤ κ · |Z.D|; the arrangement has
    no round; then the fold's conditions, at k = h + g, Ch = Sh.Ch, n = Sh.n.

Notation: `κ`: the one number of the title, of type `ℝ≥0∞`; `Lst`, `mC`, `mS`, `mW`: functions ℕ →
ℕ, the arguments of the fold's errors `Y.err`; `L`: a natural number, the factor of `Z.err` in the
bridge's error; `Z`: an `Evader` (Cb/Gen/BatEvader.lean): a zero-evader: the data; `Z.D`: a type:
the seeds; `Z.err`: a natural number, a field of `Evader`; and, fields of `SumPar`
(Cb/Ld/LdSum.lean): `Ch`: a type: the challenge set; `n`: a natural number: the largest degree of a
round polynomial; `h`, `g`: natural numbers: the mask tables have rows on the cube of the first h
variables; g further variables.

Limits: this file does not say that the numbers Lst, mC, mS, mW, L bound lists and correlated
agreement of the codes (hypotheses of Cb/Ld/LdGroupFold.lean's theorems), or that the inequalities
hold at parameters of a protocol.


Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupSegProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood
open scoped ENNReal

theorem sErr_below {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (n : ℕ) (κ : ℝ≥0∞) :
    ∀ (k : ℕ) (f : ℕ → ℕ), (∀ i, i < k → (f i : ℝ≥0∞) ≤ κ * (Fintype.card Ch : ℝ≥0∞)) →
      Err.Below (sErr (E := E) (Ch := Ch) n k f) κ
  | 0, _, _ => trivial
  | k + 1, f, h =>
    ⟨h 0 (Nat.succ_pos k),
      sErr_below n κ k (fun j => f (j + 1)) fun i hi => h (i + 1) (Nat.succ_lt_succ hi)⟩

/-- Every error of the fold, as a probability, is at most κ, from numbers (`h0`, `hi`). -/
theorem ld_sum_below {E P : Type} [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
    (Lst mC mS mW : ℕ → ℕ) (κ : ℝ≥0∞) (h0 : (Lst 0 : ℝ≥0∞) ≤ κ * (Fintype.card Y.Ch : ℝ≥0∞))
    (hi : ∀ i, i < Y.k →
      ((mC (i + 1) + (if i + 1 ≤ Y.h then mS (i + 1) + mW (i + 1) else 0) +
          Lst i * Y.n : ℕ) : ℝ≥0∞) ≤
        κ * (Fintype.card Y.Ch : ℝ≥0∞)) :
    Err.Below (Y.err Lst mC mS mW) κ :=
  ⟨h0, sErr_below Y.n κ Y.k _ hi⟩

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp) (d t : ℕ)
  (Lst mC mS mW : ℕ → ℕ) (L : ℕ)

theorem ldGroup_link_below (κ : ℝ≥0∞)
    (hb : ((L * Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card Z.D : ℝ≥0∞))
    (h0 : (Lst 0 : ℝ≥0∞) ≤ κ * (Fintype.card Sh.Ch : ℝ≥0∞))
    (hi : ∀ i, i < Sh.h + Sh.g →
      ((mC (i + 1) + (if i + 1 ≤ Sh.h then mS (i + 1) + mW (i + 1) else 0) +
          Lst i * Sh.n : ℕ) : ℝ≥0∞) ≤
        κ * (Fintype.card Sh.Ch : ℝ≥0∞)) :
    Err.Below (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).P.err κ := by
  have h1 : Err.Below (ldBridgeN G kp Sb Z St₀ E₀ Kc (L * Z.err)).err κ := ⟨hb, trivial⟩
  have h2 : Err.Below
      ((Sh.block Sb sl Z d t Lst mC mS mW).N.beside Kc (LdCarX kp St₀) (LdCarE kp E₀)).err κ :=
    ld_sum_below (Sh.fold Sb sl Z) Lst mC mS mW κ h0 hi
  exact Err.Below.app h1 h2

end
end Cb
