-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbAccLaw.lean: the form in which the compiled prover's accept law is spent (`AccLaw`,
Johnson/Prover/Law/Defs.lean), tied to the protocol without proof of work along a pair with bits.

`AccLaw Q wq x y σ B` speaks through a wire: at every transcript that is the run of σ but for
nonces, with all the wire's tests passed, and whose verifier randomness lies outside B, the
interactive verifier accepts. `AccPassAt` (E2E/ClimbRun.lean) says the like through a pair with
bits. Where the wire says the pair's words (`Fits`, E2E/ClimbFits.lean) the two are one.

In section 1 the two protocols are letters, Q₀ and Q, joined by a pair (in section 3: P₀ and P;
section 2 has rounds alone): "the verifier without proof of work" in the docstrings there is a gloss
on Q₀, which is whatever the pair's first protocol is.

  `accLaw_iff`: `AccLaw` if and only if `AccPassAt`, at one strategy and one set.
  `accLaw_up_iff`: the verifier without proof of work accepts a strategy's runs outside B₀ if and
    only if the strategy carried up has `AccLaw` at the set of verifier randomness whose old part
    lies in B₀.
  `accLaw_dn_iff`: a strategy of the protocol with proof of work has `AccLaw` at B if and only if
    the verifier without proof of work accepts the runs of the strategy carried down, at verifier
    randomness whose image lies outside B.
  `Fits.prRho_zero`: THE NUMBER THAT GOES BESIDE IT. For every set B, where the pair keeps
    probabilities (`Pair.Unif`, E2E/ClimbUnif.lean): the probability that ρ' with all the wire's
    test bits set to 0 lies in B, which is what the compiled prover's law measures
    (`Spec.prove_law`, Johnson/Prover/Law/Defs.lean), is the probability of {ρ | zeroR ρ ∈ B} over
    the verifier randomness of Q₀, the set outside which `accLaw_dn_iff` speaks. So a bound on that
    probability at Q₀ is a bound on what the compiled prover's law measures, with no clause on
    blindness.
  `Fits.blindSet_zero`, `Blind.wh_zero`: a blind set, and so the abort set of a prover that is
    `Blind`, holds ρ if it holds ρ with all the wire's test bits set to 0.
  `BlindUp.wh_zero`, `BlindUp.run_zero`: of a prover that is `BlindUp`, the abort set, the plain
    parts and the answers at every position are the same at ρ and at ρ with all the wire's test bits
    set to 0.
  `fits_whole`, `fits_link`; `accLaw_iff_whole`, `accLaw_iff_link`: `Fits` and `accLaw_iff` at the
    wire of a whole written file and of the written link, at every kit that does not read an entry's
    proof of work and at all rounds' data.

One strategy and one set: no coins, no private input, no validity. So `accLaw_iff`,
`accLaw_up_iff`, `accLaw_dn_iff`, `Fits.prRho_zero`, `Fits.blindSet_zero` and the two at the written
wires take any set, also one that is handed the coin or the private input. `Blind.wh_zero`,
`BlindUp.wh_zero` and `BlindUp.run_zero` read the abort set of the library's `Honest`, which is
handed no coin. `accLaw_up_iff` wants its set pulled back along `oldR`; `accLaw_dn_iff` wants no
form.

Limits.
  * No strategy is shown to have `AccLaw`, and no verifier is shown to accept anything.
  * `AccLaw` at a set B says nothing at verifier randomness in B, and nothing where a test fails.
    The set of all verifier randomness that passes gives it to every strategy, and where rounds
    have bits of proof of work that set is small under the protocol's own verifier randomness. So
    the number beside `AccLaw Q wq x y σ B` is never the probability of B alone. It is that of
    `Fits.prRho_zero`, under which the set just named has probability 1. (For a blind set the
    probability of B is an upper bound of it: `Pair.prRho_zeroR_le`, E2E/ClimbUnif.lean.)
  * A STRATEGY CARRIED DOWN IS ANOTHER STRATEGY, OF ANOTHER PROTOCOL: it is σ where every test is
    passed, with what `strip` drops dropped. `AccLaw` reads σ there alone, so `accLaw_dn_iff` holds
    of every σ; but the strategy carried down is "the same prover without proof of work" only where
    σ is itself carried down and up again (`BlindUp`, E2E/ClimbRun.lean).
  * The statements on `Blind` and `BlindUp` are modelled on the clauses `wh` and `run` of the
    library's `GrFitP` (Compile/Batch/SpecFit.lean), which is typed over the first form's wire. No
    statement here names `GrFitP`.
  * That the wiring of the three files' protocols of the full size is made of these wires is not
    said here: E2E/ClimbAccLawAtD.lean.
  * Probability of sets of one run's verifier randomness alone. Nothing on a batch's joint
    randomness, on views or on zero knowledge.
  * Johnson/Prover/Law/Defs.lean, with `AccLaw` and `Spec.prove_law`, is not reviewed.


What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbFits
import E2E.ClimbUnif

set_option autoImplicit false

namespace AtPublicFiles.Climb
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Prover OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Prob
open _root_.Run.PQ (CK View XO SgX)
open TypedOracleCompiler.Run.PQ (RD)

variable {lam K : ℕ}

/-! ## 1. One strategy, one set -/

section
variable {Y : Type} {E : ExtSpec} {Q₀ Q : BatchInteractiveOracleProof Y E} (S : BatchPair Q₀ Q) (wq : ProtocolQueryLayout lam K Q)
  (hF : Fits S.pair.toPair Q.ann wq.sh) (x : Y) (y : E.Str)
include hF

/-- **Where the wire says the pair's words, `AccLaw` is `AccPassAt`.** -/
theorem accLaw_iff (σ : Strat Q.loc.shape Unit) (B : Set (Rho Q.loc.shape)) :
    AccLaw Q wq x y σ B ↔ AccPassAt S.loc x y σ B := by
  constructor
  · intro h
    rw [S.loc.accPassAt_iff_run]
    intro ρ' hp hB
    have hr : (σ.run ρ').1.rho = ρ' := Strat.rho_run σ ρ'
    refine h (σ.run ρ').1 ?_ ?_ ?_
    · rw [hr, hF.pass]
      exact hp
    · rw [hr]
      exact puts_refl _ _ _ _
    · rw [hr]
      exact hB
  · intro h τ hp hP hB
    exact h τ ((hF.pass τ.rho).symm.trans hp) hB (hF.puts _ _ hP)

/-- **The verifier without proof of work accepts a strategy's runs outside B₀ if and only if the
strategy carried up has `AccLaw` at the set of verifier randomness whose old part lies in B₀.** -/
theorem accLaw_up_iff (σ₀ : Strat Q₀.loc.shape Unit) (B₀ : Set (Rho Q₀.loc.shape)) :
    (∀ ρ, ρ ∉ B₀ → Q₀.loc.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw Q wq x y (S.pair.toPair.up σ₀) {ρ' | S.pair.toPair.oldR ρ' ∈ B₀} :=
  (S.loc.accPassAt_up_iff x y σ₀ B₀).trans (accLaw_iff S wq hF x y _ _).symm

/-- **A strategy of the protocol with proof of work has `AccLaw` at B if and only if the verifier
without proof of work accepts the runs of the strategy carried down, at verifier randomness whose
image lies outside B.** It holds of every σ. The strategy carried down is another strategy, of
another protocol (this file's head, Limits). -/
theorem accLaw_dn_iff (σ : Strat Q.loc.shape Unit) (B : Set (Rho Q.loc.shape)) :
    AccLaw Q wq x y σ B ↔
      ∀ ρ, S.pair.toPair.zeroR ρ ∉ B → Q₀.loc.accept x y ((S.pair.toPair.dn σ).run ρ).1 = true :=
  (accLaw_iff S wq hF x y σ B).trans (S.loc.accPassAt_dn_iff x y σ B)

end

/-! ## 2. The number that goes beside it -/

section
variable {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'}

/-- **For every set B: the verifier randomness that lies in B once all the wire's test bits are set
to 0 has the probability of the verifier randomness of s whose image lies in B.** The left side is
what the compiled prover's law measures (`Spec.prove_law`, Johnson/Prover/Law/Defs.lean); the right
side is the set outside which `accLaw_dn_iff` speaks. No blindness is asked of B. -/
theorem Fits.prRho_zero (hF : Fits p A' W) (h : p.Unif) (B : Set (Rho t)) :
    prRho {ρ' : Rho t | RoundsQueryLayout.zero t A' W ρ' ∈ B} = prRho {ρ : Rho s | p.zeroR ρ ∈ B} := by
  have e : {ρ' : Rho t | RoundsQueryLayout.zero t A' W ρ' ∈ B} = {ρ' : Rho t | p.zeroR (p.oldR ρ') ∈ B} :=
    Set.ext fun ρ' => by
      show RoundsQueryLayout.zero t A' W ρ' ∈ B ↔ p.zeroR (p.oldR ρ') ∈ B
      rw [hF.zero_eq]
  rw [e]
  exact Pair.prRho_zeroR p h B

/-- A blind set holds ρ' if it holds ρ' with all the wire's test bits set to 0. -/
theorem Fits.blindSet_zero (hF : Fits p A' W) {B : Set (Rho t)} (hb : p.BlindSet B) (ρ' : Rho t)
    (h : RoundsQueryLayout.zero t A' W ρ' ∈ B) : ρ' ∈ B := by
  rw [hF.zero_eq] at h
  exact hb ρ' h

end

/-! ## 3. Blind to the wire's test bits -/

section
variable {X : Type} {E : ExtSpec} {P₀ P : InteractiveOracleProof X E} {S : ProtoPair P₀ P} {Wt : Type}
  {H' : Honest P Wt} {A' : RoundSplits P.shape} {W : RoundsQueryLayout lam K P.shape A'}

/-- Of a prover that is `Blind`: the abort set holds ρ if it holds ρ with all the wire's test bits
set to 0. -/
theorem Blind.wh_zero (h : Blind S H') (hF : Fits S.pair A' W) (w : Wt) (x : X) (ρ : Rho P.shape)
    (hm : RoundsQueryLayout.zero P.shape A' W ρ ∈ H'.withheld w x) : ρ ∈ H'.withheld w x :=
  hF.blindSet_zero (h w x) ρ hm

/-- The abort set holds ρ exactly if it holds ρ with all the wire's test bits set to 0. -/
theorem BlindUp.wh_zero (h : BlindUp S H') (hF : Fits S.pair A' W) (w : Wt) (x : X)
    (ρ : Rho P.shape) :
    ρ ∈ H'.withheld w x ↔ RoundsQueryLayout.zero P.shape A' W ρ ∈ H'.withheld w x :=
  h.wh_congr w x (hF.zero ρ).symm

/-- The honest run has the same plain parts and the same answers at every position at ρ and at ρ
with all the wire's test bits set to 0. -/
theorem BlindUp.run_zero (h : BlindUp S H') (hF : Fits S.pair A' W) (w : Wt) (x : X) (c : H'.Coin)
    (ρ : Rho P.shape) :
    ((H'.strat w x c).run ρ).1.plains =
        ((H'.strat w x c).run (RoundsQueryLayout.zero P.shape A' W ρ)).1.plains ∧
      ∀ q, ((H'.strat w x c).run ρ).1.read q =
        ((H'.strat w x c).run (RoundsQueryLayout.zero P.shape A' W ρ)).1.read q :=
  h.msgs w x c (hF.zero ρ).symm

end

/-! ## 4. At the wire of a whole written file, and of the written link -/

section
variable (C : CK) (Kf : KitFree C) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem fits_whole :
    Fits (wholeBatchPair C Kf silent run D tF tJ t3).pair.toPair _
      (wqWhole C K chal D tF tJ t3 silent run).sh := by
  rw [wholeBatchPair_toPair]
  exact fits_wqWhole C Kf K chal D tF tJ t3 silent run

/-- `accLaw_iff` at the wire of a whole written file. -/
theorem accLaw_iff_whole (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (σ : Strat (chainsOf C D tF tJ t3).sh Unit) (B : Set (Rho (chainsOf C D tF tJ t3).sh)) :
    AccLaw _ (wqWhole C K chal D tF tJ t3 silent run) x y σ B ↔
      AccPassAt (wholeBatchPair C Kf silent run D tF tJ t3).loc x y σ B :=
  accLaw_iff (wholeBatchPair C Kf silent run D tF tJ t3) (wqWhole C K chal D tF tJ t3 silent run)
    (fits_whole C Kf K chal D tF tJ t3 silent run) x y σ B

variable (ds : List RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)

theorem fits_link :
    Fits (linkBatchPair C Kf ds a xs dec).pair.toPair _
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh := by
  rw [linkBatchPair_toPair]
  exact fits_wqW C Kf K chal ds a xs dec

/-- `accLaw_iff` at the wire of the written link. -/
theorem accLaw_iff_link (x : Y) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (σ : Strat (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf C ds)) Unit)
    (B : Set (Rho (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf C ds)))) :
    AccLaw _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal) x y σ B ↔
      AccPassAt (linkBatchPair C Kf ds a xs dec).loc x y σ B :=
  accLaw_iff (linkBatchPair C Kf ds a xs dec) (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal)
    (fits_link C Kf K chal ds a xs dec) x y σ B

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.accLaw_iff
#print axioms AtPublicFiles.Climb.accLaw_up_iff
#print axioms AtPublicFiles.Climb.accLaw_dn_iff
#print axioms AtPublicFiles.Climb.Fits.prRho_zero
#print axioms AtPublicFiles.Climb.Fits.blindSet_zero
#print axioms AtPublicFiles.Climb.Blind.wh_zero
#print axioms AtPublicFiles.Climb.BlindUp.wh_zero
#print axioms AtPublicFiles.Climb.BlindUp.run_zero
#print axioms AtPublicFiles.Climb.fits_whole
#print axioms AtPublicFiles.Climb.accLaw_iff_whole
#print axioms AtPublicFiles.Climb.fits_link
#print axioms AtPublicFiles.Climb.accLaw_iff_link
