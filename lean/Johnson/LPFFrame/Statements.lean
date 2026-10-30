-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFFrame/Statements.lean: THE FRAME's ACCEPT: from a law on a whole file's decision `run`
alone to the accept law in the form in which the compiled prover's theorems spend it (`AccLaw`).
STATEMENTS FIRST: definitions, and statements as `def … : Prop`; no theorem yet.


Why. The interactive verifier of a whole file accepts exactly where nine tests say yes
(`wholeIOR_out_iff`, OnBytes/Maker/WholeViews.lean): the three chains' tests of work, three tests
that the draws are complete, one that the stored table's symbols carry their positions, one on the
silent rounds, and `run` at the three views. A law on the honest steps of a description speaks of
`run`. The law of the compiled prover's outcome spends `AccLaw Q wq x y σ B`: at every transcript
that is σ's own run but for nonces, with all tests of work passed, and whose verifier messages lie
outside B, the verifier accepts. Between the two stand the other eight tests and the nonces.

Over what it is built. An earlier set of this project's Lean files, and another group's files
Johnson/Prover/Law/Defs.lean (`AccLaw`) and OnBytes/Prover/Inv.lean (`Puts`), with what they import,
as they lie in a pack of that group's files, which is not in this repository.

Main names. The first six are general in the way of drawing C, the data D, the silent rounds' test
and the decision; so they serve the key file and the proof file alike.
* `FullAt C D`: at every verifier message of each chain the draws are complete.
* `Carries y`: every symbol of the stored table carries its position.
* `Spec.pass_whole`: the wire record's test over the whole shape is the three chains' tests.
* `Spec.puts_same`: a transcript that is another's but for nonces has the same three views, the
  same silent parts and the same verifier messages.
* `Spec.accept_iff_run`: under `FullAt` and `Carries`: the verifier accepts exactly if the tests of
  work pass, the silent rounds' test says yes and `run` says yes at the three views.
* `Spec.frame_accLaw`: THE LINK.
* `Spec.fullAt_bare`: `FullAt`, at the programs' way of drawing, where the first and the third chain
  open no stored table and the second chain's stored parts lie within its draws.
* `Spec.fullAt_written`, `Spec.fullAt_writtenK`: at the proof file's and the key file's written
  data.
* `Spec.fullAt_live`, `Spec.fullAt_liveK`: at the description's own data as they stand in the
  verifier's slots, in scope and live.
* `Spec.carries_honestTab`: the format's own encoder lays a table that carries its positions.
* `Spec.frame_at_slot`, `Spec.frame_at_slotK`: THE LINK AT THE LETTERS OF THE COMPILED VERIFIERS: it
  ends in `AccLaw (innerCompilerInputAtFullSize T).protocol.onlineBatch (wBC (innerCompilerInputAtFullSize T).queryLayout) …` (the session) and in
  `AccLaw (batTC …) (wTC …) …` (the key's test), at every set of letters T of the full size. So Lean
  checks that `AccLaw` types at these terms with the link's σ, B and y. That the other group's law
  of a whole request takes these very terms is read in a snapshot of its files, which are not
  imported.
* `Spec.gate_of_run`: in the verifier's slot stands not the description's decision `theProofRun` but
  `theProofGate`, which is that decision behind the entry tests. Where these say yes the two are one
  (`theProofGate_live`, Johnson/Goal/Description/Gates.lean): the link's premise at the gate follows
  from the same at the decision.

Limits.
1. The premise of the link, that `run` says yes at the views of σ's run outside B, is shown of no σ.
   No accept of anything follows from this file alone. No probability: B is a letter.
2. `Carries y` is asked of the table. The description's coding is made of the format's own encoder
   (by reading: `theCoding`, `codingCells`, `codingHonest`, `honestTab`); here that is stated of
   `honestTab` alone.
3. B is any set: that it does not hang on the test bits is the caller's to show.
4. Of the four clauses that the other group's law of a whole request asks (the key's test, the link
   between two tables, the session, the stored copy's number) this link serves the first and the
   third. The link between two tables is no whole file: nothing is said of it. Of the number:
   `Spec.puts_same` keeps the front round's plain part; no more is said: at every T the test on the
   number is a letter of T.
5. "Live": that the entry tests say yes is shown here of no files. At the stored public files (the
   term `VerifierAndGoals.storedPublicFiles`) another file proves it: `theLive_zFull` (AtFullSide/Top/LiveAtFull.lean),
   with that file's limits. `Spec.fullAt_written` and `Spec.fullAt_writtenK` stand without it; but
   at the description's own letters all of the link hangs on it: where the entry tests say no, the
   gates say no to all (Johnson/LPFFrame/AtVerifyStatements.lean [not in this library]).
6. Nothing on soundness, binding or hiding. No goal of the release is named.

-/
import Johnson.Prover.Law.Defs
import OnBytes.Maker.Wire
import OnBytes.Maker.WholeViews
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Flat.Dec.DataAtWritten
import Johnson.Goal.Description.Gates
import Johnson.Goal.Numbers.KeySeatLaidAt
import Johnson.Flat.Dec.TwoSizesAt
import OnBytes.Slice.Honest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFFrame

open OnBytes OnBytes.Maker TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open OnBytes.Prover (AccLaw Puts)

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- At every verifier message of each chain, every stored table's part of a round's draws has as
many draws as it says. -/
def FullAt : Prop :=
  (∀ ρ, fullOf D.ds₁ (drawnT C D.ds₁ ρ) = true) ∧ (∀ ρ, fullOf D.ds₂ (drawnT C D.ds₂ ρ) = true) ∧
    ∀ ρ, fullOf D.ds₃ (drawnT C D.ds₃ ρ) = true

/-- Every symbol of the stored table carries its position. -/
def Carries {a : ℕ} (y : (oneExternalString (2 ^ a) SgX).Str) : Prop := ∀ p, (y p).1 = p.val

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The wire record's test over the whole shape is the three chains' tests of work: the front, the
joining round and the seam have none. -/
def Spec.pass_whole : Prop :=
  ∀ τ : Tr (chainsOf C D tF tJ t3).sh,
    RoundsQueryLayout.pass _ _ (wqWhole C K chal D tF tJ t3 silent run).sh τ.rho =
      (passT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) &&
        passT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) &&
        passT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)))

/-- A transcript that is another's but for nonces has the same verifier messages, the same three
views at every table, and the same silent parts. -/
def Spec.puts_same : Prop :=
  ∀ τ τ' : Tr (chainsOf C D tF tJ t3).sh,
    Puts _ _ (wqWhole C K chal D tF tJ t3 silent run).sh τ τ' →
    τ'.rho = τ.rho ∧
      (∀ y, view₁ C D tF tJ t3 y τ' = view₁ C D tF tJ t3 y τ ∧
        view₂ C D tF tJ t3 y τ' = view₂ C D tF tJ t3 y τ ∧
        view₃ C D tF tJ t3 y τ' = view₃ C D tF tJ t3 y τ) ∧
      ((chainsOf C D tF tJ t3).msgF τ').2 = ((chainsOf C D tF tJ t3).msgF τ).2 ∧
      ((chainsOf C D tF tJ t3).msgJ τ').2 = ((chainsOf C D tF tJ t3).msgJ τ).2 ∧
      ((chainsOf C D tF tJ t3).msg3 τ').2 = ((chainsOf C D tF tJ t3).msg3 τ).2

/-- Where the draws are always complete and the table carries its positions, four tests of the nine
are idle: the verifier accepts exactly if the tests of work pass, the silent rounds' test says yes
and the decision says yes at the three views. -/
def Spec.accept_iff_run : Prop :=
  FullAt C D → ∀ (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str), Carries y →
    ∀ τ : Tr (chainsOf C D tF tJ t3).sh,
      (wholeDesc C D tF tJ t3 silent run).batch.loc.accept x y τ = true ↔
        (RoundsQueryLayout.pass _ _ (wqWhole C K chal D tF tJ t3 silent run).sh τ.rho = true ∧
          silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
            ((chainsOf C D tF tJ t3).msg3 τ).2 = true ∧
          run x (view₁ C D tF tJ t3 y τ) (view₂ C D tF tJ t3 y τ) (view₃ C D tF tJ t3 y τ) = true)

/-- **THE LINK.** Let the draws be always complete and the table carry its positions. If at every
verifier message ρ outside B at which all tests of work pass, σ's own run sends silent parts that
pass their test and has views at which the decision says yes, then the accept law holds of σ and B
in the form in which the compiled prover's theorems spend it. -/
def Spec.frame_accLaw : Prop :=
  FullAt C D → ∀ (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str), Carries y →
    ∀ (σ : Strat (chainsOf C D tF tJ t3).sh Unit) (B : Set (Rho (chainsOf C D tF tJ t3).sh)),
      (∀ ρ, RoundsQueryLayout.pass _ _ (wqWhole C K chal D tF tJ t3 silent run).sh ρ = true → ρ ∉ B →
        silent x ((chainsOf C D tF tJ t3).msgF (σ.run ρ).1).2
            ((chainsOf C D tF tJ t3).msgJ (σ.run ρ).1).2
            ((chainsOf C D tF tJ t3).msg3 (σ.run ρ).1).2 = true ∧
          run x (view₁ C D tF tJ t3 y (σ.run ρ).1) (view₂ C D tF tJ t3 y (σ.run ρ).1)
            (view₃ C D tF tJ t3 y (σ.run ρ).1) = true) →
      AccLaw (wholeDesc C D tF tJ t3 silent run).batch (wqWhole C K chal D tF tJ t3 silent run)
        x y σ B

end

/-- `FullAt` where the first and the third chain open no stored table, and in the second every
stored part lies within the round's declared number of positions. At the programs' way of drawing
(`ckP`), where a typed verifier message bears the declared number (`Run.planPull_fits`). -/
def Spec.fullAt_bare : Prop :=
  ∀ D : WholeD, (∀ d ∈ D.ds₁, d.stored = []) → (∀ d ∈ D.ds₃, d.stored = []) →
    (∀ d ∈ D.ds₂, ∀ s ∈ d.stored, s.lo + s.count ≤ d.entry.poss) → FullAt (ckP .two) D

/-- At the proof file's written data. -/
def Spec.fullAt_written : Prop := FullAt (ckP .two) Johnson.G.writtenPFull

/-- At the key file's written data. -/
def Spec.fullAt_writtenK : Prop := FullAt (ckP .two) Johnson.G.writtenKFull

/-- In scope and live, at the description's own data for the proof file, as they stand in the
verifier's slot. -/
def Spec.fullAt_live : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true →
    FullAt (ckP .two) ((FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles Z)).at OnBytes.Slice.frS.P.T.a)

/-- The same for the key file. -/
def Spec.fullAt_liveK : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true →
    FullAt (ckP .two) ((FlashProve.theKeyData (VerifierAndGoals.asDescriptionFiles Z)).at OnBytes.Slice.frS.P.T.a)

/-- The format's own encoder lays a table that carries its positions. -/
def Spec.carries_honestTab : Prop :=
  ∀ (S : OnBytes.Slice.Sz) (msg tl : ℕ → List UInt64) (x : S.Pos),
    (OnBytes.Slice.honestTab S msg tl x).1 = x.val

/-- Where the entry tests say yes, what holds of the description's decision at three views holds of
what stands in the verifier's slot. -/
def Spec.gate_of_run : Prop :=
  ∀ Zk : OnBytes.K.Pub, FlashProve.protocolDataWellFormed Zk = true → ∀ z v₁ v₂ v₃,
    FlashProve.theProofRun Zk z v₁ v₂ v₃ = true → FlashProve.theProofGate Zk z v₁ v₂ v₃ = true

/-! ## At the letters of the compiled verifiers -/

section Slot
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.RunA
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- **THE LINK AT THE SESSION's LETTERS**: the protocol and the wire record of the compiled verifier
of the proof file, at any letters of the full size. -/
def Spec.frame_at_slot : Prop :=
  FullAt (ckP .two) (DP.at frS.P.T.a) →
    ∀ (x : X) (rec : RecFull) (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), Carries y →
    ∀ (σ : Strat (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty).sh Unit)
      (B : Set (Rho (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty).sh)),
      (∀ ρ, RoundsQueryLayout.pass _ _ (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP)
                       (join₀ rP) ByteArray.empty silP runP).sh ρ = true → ρ ∉ B →
        silP (x, rec) ((chainsOf _ _ _ _ _).msgF (σ.run ρ).1).2
            ((chainsOf _ _ _ _ _).msgJ (σ.run ρ).1).2 ((chainsOf _ _ _ _ _).msg3 (σ.run ρ).1).2 =
            true ∧
          runP (x, rec) (view₁ _ _ _ _ _ y (σ.run ρ).1) (view₂ _ _ _ _ _ y (σ.run ρ).1)
            (view₃ _ _ _ _ _ y (σ.run ρ).1) = true) →
      AccLaw (innerCompilerInputAtFullSize T).protocol.onlineBatch (wBC (innerCompilerInputAtFullSize T).queryLayout) (x, rec) y σ B

/-- **THE LINK AT THE LETTERS OF THE KEY's TEST.** -/
def Spec.frame_at_slotK : Prop :=
  FullAt (ckP .two) (DK.at frS.P.T.a) →
    ∀ (rec : RecFull) (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), Carries y →
    ∀ (σ : Strat (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty).sh Unit)
      (B : Set (Rho (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty).sh)),
      (∀ ρ, RoundsQueryLayout.pass _ _ (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK)
                       (join₀ rK) ByteArray.empty silK runK).sh ρ = true → ρ ∉ B →
        silK rec ((chainsOf _ _ _ _ _).msgF (σ.run ρ).1).2
            ((chainsOf _ _ _ _ _).msgJ (σ.run ρ).1).2 ((chainsOf _ _ _ _ _).msg3 (σ.run ρ).1).2 =
            true ∧
          runK rec (view₁ _ _ _ _ _ y (σ.run ρ).1) (view₂ _ _ _ _ _ y (σ.run ρ).1)
            (view₃ _ _ _ _ _ y (σ.run ρ).1) = true) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout)
        rec y σ B

end Slot

end LPFFrame
