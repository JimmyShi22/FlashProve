-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/One.lean: from the rule that joins lists of parts
(Honest/Law/Rule/Row.lean) to one slot of `honestBatchProverOfFile` (Honest/StratC.lean): the skeleton of the step,
under the rule's own hypotheses (`Owed` among them) and with one more hypothesis left open
(`one_exact_of`). At a verifier's message outside the abort set (`withheld`): the library's output
of one slot (`Iop.Honest.output`: over the coins of `honestBatchProverOfFile`, the disclosed view of the transcript
that the two strategies write) has the distribution of: what the session produces (`simActs`), two
coins more for the three rounds without a challenge, and a function bk of these. The abort set is,
for each private input and instance, the set `Bad ∪ Hid w x` of verifier's messages.

The hypothesis that is left open, `hback`: at each value of the coins of `honestBatchProverOfFile` the disclosed
view of the strategies' transcript is bk of what the three rounds without a challenge send and of
what the run of `runC` at these coins has produced. bk is a parameter here. Until `hback` is proved
of an explicit bk that reads nothing but the instance, the verifier's message and the external
answers, this lemma says little: at bk := a function that holds the private input it is met too.

  1  `coinsEq`   the coins of `honestBatchProverOfFile` are a run's coins and two more
  2  `silent_of`   a message outside the abort set gives a list of challenges outside the one silent
     set (`silentAt`, Honest/Rule.lean)
  3  `one_exact_of`   the lemma

Limits.
  * One slot, one verifier's message, outside the abort set.
  * bk is a parameter.
  * All limits of the head of Honest/Law/Rule/Row.lean.
  * Hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
    description's rounds can draw; the first chain's last challenge is the empty one):
    `one_exact_of`; `Sides.owns` (every entry's owner is a part of some side): `one_exact_of`;
    `Rel`: `one_exact_of`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.Desc.ProofFile.Honest.Law.Rule.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-- The coins of `honestBatchProverOfFile`: a run's coins, and the two coins of the rounds without a challenge. -/
def coinsEq (Bk : ProverCoinCounts) (R2 R3 : Type) :
    ((Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3)) ≃
      Coins Bk × (R2 × R3) where
  toFun c := (⟨c.2.1.1, c.1.1, c.2.1.2⟩, (c.1.2, c.2.2))
  invFun p := ((p.1.shared, p.2.1), ((p.1.first, p.1.second), p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3]
  (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

theorem silent_of (w : W₀ × Rc × Sd) (x : Xi) (htr : (H.trace w.1 x).isSome = true)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hw : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover
                       H) J sh ext).one.withheld w x) :
    silentAt F (G.prover H) w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) = none := by
  have h := (withheldC_iff C D tF tJ t3 F silent Bk (G.prover H) J sh ext w x htr ρ).not.1 hw
  cases hs : silentAt F (G.prover H) w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) with
  | none => rfl
  | some y =>
    rw [hs] at h
    exact absurd rfl h

/-- **The skeleton of the step from the rule to one slot of `honestBatchProverOfFile`.** -/
theorem one_exact_of {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel) (hE : G.owns = true)
    (pubJ : R2 → R3 → Xi → TF × TJ × T3) (w : W₀ × Rc × Sd) (x : Xi) (hrel : Rel w.1 w.2.1 x)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hw : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.withheld w x)
    (bk : TF × TJ × T3 → Laid → Iop.DView (batchOf C D tF tJ t3 F silent).loc)
    (hback : ∀ (c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3)) (r : RunC
        F),
      runC F Bk (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r
          →
      (batchOf C D tF tJ t3 F silent).loc.dview x (ext w) (((honestBatchProverOfFile C D tF tJ t3 F silent Bk
          (G.prover H) J sh ext).one.strat w x c).run ρ).1 =
        bk (pubJ c.1.2 c.2.2 x) r.run.laid) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.output w x ρ =
      ((simActs x (storedShown (H.storedWords w.1 w.2.1) (storedAsks F (drawsAt C D tF tJ t3 ρ)))
        (theActs F Bk G.sims H.key x (drawsAt C D tF tJ t3 ρ)) (Stand.start F x)).map fun o => o.map
            (·.laid)).bind
        fun o => (unif (R2 × R3)).map fun r => o.map fun L => bk (pubJ r.1 r.2 x) L := by
  have hsil := silent_of C D tF tJ t3 F silent Bk H G J sh ext w x (hO.input w.1 w.2.1 x hrel).2 ρ
      hw
  rw [← rule_laid hO hE w.1 w.2.1 x hrel (drawsAt C D tF tJ t3 ρ) hdue hsil, PMF.bind_map]
  unfold Iop.Honest.output
  split
  · rename_i h
    exact absurd h hw
  show (unif ((Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3))).map
    (fun c => some ((batchOf C D tF tJ t3 F silent).loc.dview x (ext w)
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.strat w x c).run ρ).1)) = _
  have hf : (fun c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3) =>
      some ((batchOf C D tF tJ t3 F silent).loc.dview x (ext w)
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.strat w x c).run ρ).1)) =
      (fun p : Coins Bk × (R2 × R3) =>
        ((runC F Bk (G.prover H) w.1 w.2.1 x p.1 (drawsAt C D tF tJ t3 ρ)).toOption.map
            (·.run.laid)).map
          fun L => bk (pubJ p.2.1 p.2.2 x) L) ∘ coinsEq Bk R2 R3 := by
    funext c
    obtain ⟨r, hr⟩ := hO.runs w.1 w.2.1 x hrel ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ)
        hdue hsil
    show _ = ((runC F Bk (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
      (drawsAt C D tF tJ t3 ρ)).toOption.map (·.run.laid)).map fun L => bk (pubJ c.1.2 c.2.2 x) L
    rw [hr, hback c r hr]
    rfl
  refine (congrArg (fun f => PMF.map f
    (unif ((Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3)))) hf).trans ?_
  show PMF.map (_ ∘ coinsEq Bk R2 R3) _ = _
  rw [← PMF.map_comp, map_unif_equiv, map_unif_prod]
  rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.silent_of
#print axioms ProofFile.Honest.one_exact_of
