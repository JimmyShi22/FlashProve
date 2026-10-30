-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeRunVals.lean: in every run of the honest prover of one request, the plain parts of the
three rounds without a challenge are the values that the prover's `KeyAndJoiningRoundMessages` structure names for them;
so, where these values hold the coin's two run values, the pair that is read off the plain parts is
the pair that is read off the coin. The three rounds are the front round, the joining round and the
seam of a file's three chains (`Chains`, Compile/Joined/Types.lean). The prover is `honestProversByCopyNumber`
(E2E/BridgeAlong.lean): the family of one request's honest provers of `ProofFile.Honest.honestBatchProverOfFile`, one for
each number n of a stored copy (the copy's number). Its parameter J gives, for each n and each pair
of run values r₂ and r₃, a `KeyAndJoiningRoundMessages` (Johnson/Desc/ProofFile/Honest/Strat.lean): a structure whose
fields `front`, `join` and `seam` are what the three rounds send. `runVals_famBC` has the form of
the hypothesis h of `runValsB_of` (E2E/BridgePrivacy.lean: from h, the equation of the clause on the
session's prover of `RunVals`), for this family, and is proved from two hypotheses on J. General in
all parameters of `honestProversByCopyNumber`. Statements and proofs; nothing is defined.

  `runVals_famBC`: where pj of `(J n r2 default).join …` is v₂ r2 and p3 of `(J n r2 r3).seam …` is
    v₃ r3 (hJ, h3): at every n, private input w, instance x, coin κ and verifier randomness ρ, the
    pair of pj of the joining round's plain part and p3 of the seam's plain part is the pair of v₂
    and v₃ at the coin's two run values, κ.1.2 and κ.2.2. The four maps are free parameters
  `plains3_famBC`: at every n, w, x, κ and ρ, with no hypothesis: the plain parts of the front
    round, the joining round and the seam are `(J n r₂ r₃).front …`, `(J n r₂ default).join …` and
    `(J n r₂ r₃).seam …`, at w, and for the first and the third at x; r₂ and r₃ are the coin's two
    run values
  `front_famBC`: where pf of `(J n r2 r3).front …` is the number n (hF), so is pf of the front
    round's plain part
  `plF_plains`, `plJ_plains`, `pl3_plains`: for any `Chains` G and any transcript τ: the plain part
    of the front round, of the joining round and of the seam, read off τ's plain parts (`G.plF`,
    `G.plJ`, `G.pl3`), is the plain part of that round's message in τ (`G.msgF`, `G.msgJ`,
    `G.msg3`)
  `plJ'_plains`: the same for all rounds from the joining round on: `G.plJ'` of τ's plain parts is
    the plain parts of `G.trJ τ`

By what. `zip_partsC` (Johnson/Desc/ProofFile/Honest/Law/StratFormC.lean): at every verifier
randomness, private input, coin and instance, in the run of the shared part's strategy and the
slot's together, the front round and the seam send the fields `front` and `seam` of the slot's
`KeyAndJoiningRoundMessages`, and the joining round sends the field `join` of the shared part's. In `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) the slot's `KeyAndJoiningRoundMessages` is at r₂ and r₃ and the shared part's
is at r₂ and `default`: the shared part's coin has no r₃. The strategy of `honestProversByCopyNumber` is the two
together (`BatchHonestProver.one`, Iop/Batch.lean), by unfolding. `Tr.plains_snd` (Iop/ShapeKit.lean) carries
`plJ'_plains` and `pl3_plains`; `plF_plains` holds by unfolding.

Limits. The statements are on what the three rounds without a challenge send, and on nothing else of
a run. They hold after a stop of the prover's and after a rejection by the verifier too: these
rounds belong to no sub-protocol. hJ, h3 and hF are hypotheses on J; none is proved here. hJ and h3
hold by unfolding at the `KeyAndJoiningRoundMessages` that is built from `frontAt`, `joinAt` and `seamAt` of
E2E/TiedAtFiles.lean (`runVals_tied`, E2E/BridgeTied.lean). No property of a protocol is stated:
nothing on completeness, soundness or hiding.
-/
import E2E.BridgeAlong
import Johnson.Desc.ProofFile.Honest.Law.StratFormC

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Bridge
open Iop
open Compile.Joined (Chains)

section Three
variable (G : Chains)

theorem plF_plains (τ : Tr G.sh) : G.plF τ.plains = (G.msgF τ).2 := rfl

theorem plJ'_plains (τ : Tr G.sh) : G.plJ' τ.plains = (G.trJ τ).plains :=
  (Tr.plains_snd (s := G.s₁) τ.2.2).symm

theorem plJ_plains (τ : Tr G.sh) : G.plJ τ.plains = (G.msgJ τ).2 :=
  congrArg Prod.fst (plJ'_plains G τ)

theorem pl3_plains (τ : Tr G.sh) : G.pl3 τ.plains = (G.msg3 τ).2 := by
  unfold Chains.pl3
  rw [plJ'_plains G τ]
  exact congrArg Prod.fst (Tr.plains_snd (s := G.s₂) (G.trJ τ).2.2).symm

end Three

open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse zip_partsC)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃]
  [Inhabited R₃] (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **In the run of the strategy of `honestProversByCopyNumber`, the plain parts of the front round, the joining round
and the seam are the fields `front`, `join` and `seam` of J**, at every verifier randomness. The
field `join` is read at `default` in place of the coin's second run value. -/
theorem plains3_famBC (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (κ : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (chainsOf C D tF tJ t3).plF
        (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains =
      (J n κ.1.2 κ.2.2).front w.1 w.2.1 w.2.2 x ∧
    (chainsOf C D tF tJ t3).plJ
        (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains =
      (J n κ.1.2 default).join w.1 w.2.1 w.2.2 ∧
    (chainsOf C D tF tJ t3).pl3
        (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains =
      (J n κ.1.2 κ.2.2).seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨m1, -, m3, -, m5, -⟩ := zip_partsC C D tF tJ t3 F B H (J n κ.1.2 default)
    (J n κ.1.2 κ.2.2) sh w κ.1.1 x κ.2.1 ρ
  exact ⟨(plF_plains _ _).trans (congrArg Prod.snd m1),
    (plJ_plains _ _).trans (congrArg Prod.snd m3), (pl3_plains _ _).trans (congrArg Prod.snd m5)⟩

/-- **The run values read off the plain parts are those read off the coin**, at every verifier
randomness. hJ, h3: pj of the field `join` is v₂ of the first run value, and p3 of the field `seam`
is v₃ of the second. -/
theorem runVals_famBC {V₂ V₃ : Type} (pj : TJ → V₂) (p3 : T3 → V₃) (v₂ : R₂ → V₂) (v₃ : R₃ → V₃)
    (hJ : ∀ n r2 w₀ rc sd, pj ((J n r2 default).join w₀ rc sd) = v₂ r2)
    (h3 : ∀ n r2 r3 w₀ rc sd x, p3 ((J n r2 r3).seam w₀ rc sd x) = v₃ r3) (n : ℕ)
    (w : W₀ × Rc × Sd) (x : Xi)
    (κ : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (pj ((chainsOf C D tF tJ t3).plJ
        (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains),
      p3 ((chainsOf C D tF tJ t3).pl3
        (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains)) =
      (v₂ κ.1.2, v₃ κ.2.2) := by
  obtain ⟨-, a, b⟩ := plains3_famBC C D tF tJ t3 F silent B H J sh ext n w x κ ρ
  rw [a, b, hJ, h3]

/-- Where pf of the field `front` of `J n r2 r3` is n (hF), pf of the front round's plain part is n.
-/
theorem front_famBC (pf : TF → ℕ) (hF : ∀ n r2 r3 w₀ rc sd x, pf ((J n r2 r3).front w₀ rc sd x) = n)
    (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (κ : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    pf ((chainsOf C D tF tJ t3).plF
      (((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ).run ρ).1.plains) = n := by
  rw [(plains3_famBC C D tF tJ t3 F silent B H J sh ext n w x κ ρ).1, hF]

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.plF_plains
#print axioms AtPublicFiles.Bridge.plJ_plains
#print axioms AtPublicFiles.Bridge.pl3_plains
#print axioms AtPublicFiles.Bridge.plains3_famBC
#print axioms AtPublicFiles.Bridge.runVals_famBC
#print axioms AtPublicFiles.Bridge.front_famBC
#print axioms AtPublicFiles.Bridge.plJ'_plains
