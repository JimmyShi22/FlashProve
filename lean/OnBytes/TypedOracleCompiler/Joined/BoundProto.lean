-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/BoundProto.lean: a written protocol whose verifier is round-by-round sound as a
plain protocol, under ANY annotation of its rounds: it has a lane, with the errors of its shared
rounds counted once for each slot. At one slot the errors are the protocol's own.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. A key file has three joined chains as a proof file has, so its protocol has a joining round and
shared rounds; but its request tree has depth 0: there is one slot. Then the law on the verifier's
messages of shared rounds says no more than the law for one transcript. So for such a file plain
round-by-round soundness (`InteractiveOracleProof.Sound`, Iop/InteractiveOracleProof.lean) is enough, and the interface's clause for
it need not become a clause on batches.

Main names:
  `timesShared_one`: `Err.timesShared 1 A ε = ε` (Iop/BatchSound.lean);
  `stOf_jointA`: `stOf_joint` (OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean) for every annotation A, with
    the errors `Err.timesShared N A ε`; it is the library's `BatchH4.jointLaw_of_verLaw` at `stOf`;
  `sndBL_of_sound`: `InteractiveOracleProof.Sound` gives (Snd-B) of the protocol with the annotation A, at early = id
    and late = none, with these errors;
  `laneFor_of_sound`, `soundLane_of_sound`: so a written protocol has a lane
    (OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean);
  `soundLane_of_sound_one`: at a tag whose request tree has depth 0: with the protocol's own errors.

Limits: early = id and late = none: the first query holds the whole instance, and the lemmas on a
lane ask that the interface has no round "late" at all. For a file in a world in which another
file's chain has such a round: OnBytes/TypedOracleCompiler/Joined/BoundNoInst.lean. With N slots every
shared round pays N times, also those in which only the shared part speaks; the finer count is in
CompileK/Joined/ExtractKnow.lean. As in OnBytes/TypedOracleCompiler/Joined/Bound.lean for the rest.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.BoundFiles

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- At one slot nothing is multiplied. -/
theorem timesShared_one : ∀ {s : Shape} (A : RoundSplits s) (ε : Err s), Err.timesShared 1 A ε = ε
  | [], _, () => rfl
  | _ :: _, (a, A), (e, ε) => by
    show ((match a.kind with | .lo => e | .sh => 1 * e), Err.timesShared 1 A ε) = (e, ε)
    rw [timesShared_one A ε]
    cases a.kind <;> simp

section Proto
variable {Y : Type} {E : ExtSpec}

/-- The law on verifier messages for the canonical state function of a protocol, under any
annotation of its rounds: a shared round pays once for each slot. -/
theorem stOf_jointA (Q : InteractiveOracleProof Y E) (A : RoundSplits Q.shape) (ε : Err Q.shape) (N : ℕ) (y : E.Str)
    (x : Fin N → Option Y) :
    JointLaw N Q.shape A (Err.timesShared N A ε) fun j => (x j).map (stOf Q ε y) :=
  BatchH4.jointLaw_of_verLaw N Q.shape A ε (fun j => (x j).map (stOf Q ε y)) fun j S hS => by
    obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
    exact stOf_ver y xj

/-- Round-by-round soundness of a protocol gives (Snd-B) of the batch protocol that it is under any
annotation of its rounds. -/
theorem sndBL_of_sound (Q : InteractiveOracleProof Y E) (A : RoundSplits Q.shape) (N : ℕ) {Lg : Y → E.Str → Prop}
    {ε : Err Q.shape} (h : Q.Sound Lg ε) :
    (⟨Q, A⟩ : BatchInteractiveOracleProof Y E).SndBL N id none Lg (Err.timesShared N A ε) :=
  ⟨fun n hn => (by cases hn), stOf Q ε, fun y x hL => stOf_start h y x hL,
    fun y x τ m hh => stOf_prover y x τ m hh, fun y x τ _ hn => (by cases hn),
    fun y x τ _ hh => stOf_full y x τ hh, fun y x => stOf_jointA Q A ε N y x⟩

variable (Z : Written W Y E) (R : ReadBack Z id) (hl : L.late = none) {Lg : Y → E.Str → Prop}
  {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞} (hsnd : Z.Q.loc.Sound Lg ε) (hOK : Z.wq.OKG)
  (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent) (okC : List (Dig lam) → Prop)
  (extY : Tc W → List (Dig lam) → E.Str)
  (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okC cms → ¬ EM tr →
    ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY)
include R hl hsnd hOK hloc hco hext

/-- A written protocol that is sound as a plain protocol has a lane, for any number N of slots. -/
theorem laneFor_of_sound {N : ℕ} (hε : Err.Below (Err.timesShared N Z.Q.ann ε) εs) :
    ∃ ℓ : Lane W, LaneFor W Z.t N Z.verifyLax okC Lg extY εs ℓ :=
  laneFor_of_snd Z R (by rw [hl]; exact sndBL_of_sound Z.Q.loc Z.Q.ann N hsnd) hε hOK hloc hco okC
    extY hext

/-- The same with as many slots as the tag's request tree has leaves. -/
theorem soundLane_of_sound
    (hε : Err.Below (Err.timesShared (2 ^ W.dReq Z.t) Z.Q.ann ε) εs) :
    SoundLane W Z.t Z.verifyLax okC Lg extY εs := by
  obtain ⟨ℓ, h⟩ := laneFor_of_sound Z R hl hsnd hOK hloc hco okC extY hext hε
  exact ⟨ℓ, _, rfl, h⟩

/-- **One slot**: at a tag whose request tree has depth 0 the joining round and the shared rounds
cost nothing: the errors are the protocol's own. -/
theorem soundLane_of_sound_one (h0 : W.dReq Z.t = 0) (hε : Err.Below ε εs) :
    SoundLane W Z.t Z.verifyLax okC Lg extY εs :=
  soundLane_of_sound Z R hl hsnd hOK hloc hco okC extY hext
    (by rw [h0, pow_zero, timesShared_one]; exact hε)

end Proto

end TypedOracleCompiler.Joined
