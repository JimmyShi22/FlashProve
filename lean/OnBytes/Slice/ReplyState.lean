-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ReplyState.lean: a state function for a protocol in which a part of the instance (the
reply) never enters the hash chain as a part of the instance.

The library compiles an interactive protocol into a proof string by a hash chain (Compile/Batch/).
Its theorem on one compiled protocol, `Compile.Batch.mem_of_accepted`, asks for a state function
with three laws along the sequence of instances that the chain has taken in. Under one hypothesis,
`ReplyLost`, this file gives such a state function for a chain that takes in only a part of the
instance, from first to last. It is meant (an intention, no theorem) for a chain that starts from a
request and receives the reply as a message of the prover, which the verifier compares with the
reply of its instance.

Write early x for the part of the instance x that the chain takes in (for example the request, with
the reply put to 0). The goal `replyGoal x₀ y` on full transcripts says: every instance with the
early part x₀ that the verifier accepts on this transcript is in the language. It names no reply.
The hypothesis `ReplyLost` says: for every early part and all external oracles the prover has lost
at the start towards that goal, with the errors ε (the library's `Doomed`, Iop/Rbr.lean). So in the
rounds before the transcript names a reply, one set of bad verifier messages serves all replies.
That is meant to be more than soundness for each instance by itself (that some protocol is sound for
each instance and, with the same errors, fails `ReplyLost` is not shown in this library). The state
function
`replySt`, at what the chain has taken in, is 0 where the prover has lost towards the goal there
(`Lost`, Iop/State.lean).

Main definitions: `replyGoal`, `ReplyLost`, `replySt`.
Main theorems.
 `replySt_start`, `replySt_prover`, `replySt_full`, `replySt_ver`   the state is 0 at the start; a
                prover message never changes 0 to 1; at the end, state 0 at early x and x outside
                the language give that x is rejected; the law on verifier messages.
 `replySt_joint`, `replySt_joint_times`   the law on verifier messages of a batch: for local rounds
                only; for any annotation, the shared rounds' errors times N.
 `replySt_laws`   the three hypotheses of `mem_of_accepted` on its state function, at the constant
                sequence of instances early x.
 `mem_of_accepted_reply`, `laneOf_reply_ok`   one call of that theorem, and one of the library's
                `laneOf_ok` (local rounds only).
 `sndBL_of_replyLost`   the library's `SndBL` at late = none, for a protocol with local rounds only.
 `replyLost_iff_range`   it is enough to ask `ReplyLost` at the early parts of instances.
 `ReplyLost.sound`, `replyLost_id_iff`   `ReplyLost` gives the library's `InteractiveOracleProof.Sound`, and with
                early the identity it is `InteractiveOracleProof.Sound`.
 `ReplyLost.lateSound`   `ReplyLost` gives the library's `LateSound` up to every round.

Not claimed. `ReplyLost` is a hypothesis: it is shown of no protocol in this library. Nothing on the
programs' chains, on files or on
BLAKE2b. On shared rounds `replySt_joint_times` alone: the law on verifier messages of a batch for
any annotation, with the shared rounds' errors multiplied by the number of slots (the library's
general lemma, Iop/BatchSound.lean). Without that factor the law is shown for local rounds only
(`replySt_joint`); `sndBL_of_replyLost` and `laneOf_reply_ok` are for local rounds only.
`mem_of_accepted_reply` carries over every other hypothesis of the library's theorem, and none of
them is shown here. No probability is stated.

Terms: lean/GLOSSARY.md.

-/
import Compile.Batch.Sound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob
open Iop.BatchH4 (ProverLaw VerLaw)

section
variable {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (ε : Err Q.shape) (early : Y → Y)
  (Lg : Y → E.Str → Prop)

/-- The goal on full transcripts, for an early part x₀ and external oracles y: every instance with
the early part x₀ that the verifier accepts on the transcript is in the language. -/
def replyGoal (x₀ : Y) (y : E.Str) (τ : Tr Q.shape) : Prop :=
  ∀ x, early x = x₀ → Q.accept x y τ = true → Lg x y

/-- The hypothesis: for every early part and all external oracles the prover has lost at the start
towards `replyGoal`, with the errors ε. -/
def ReplyLost : Prop := ∀ x₀ y, Doomed Q.shape ε (replyGoal Q early Lg x₀ y)

open Classical in
/-- The state function, at the external oracles y and at x₀, what the chain has taken in of the
instance: 0 where the prover has lost towards `replyGoal x₀ y`. Where x₀ is the early part of no
instance it is 0 throughout. -/
noncomputable def replySt : E.Str → Y → PTr Q.shape → Bool := fun y x₀ τ =>
  decide (¬ Lost Q.shape ε (replyGoal Q early Lg x₀ y) τ)

variable {Q ε early Lg}

theorem replySt_eq_false {y : E.Str} {x₀ : Y} {τ : PTr Q.shape} :
    replySt Q ε early Lg y x₀ τ = false ↔ Lost Q.shape ε (replyGoal Q early Lg x₀ y) τ := by
  simp [replySt]

theorem replySt_eq_true {y : E.Str} {x₀ : Y} {τ : PTr Q.shape} :
    replySt Q ε early Lg y x₀ τ = true ↔ ¬ Lost Q.shape ε (replyGoal Q early Lg x₀ y) τ := by
  simp [replySt]

/-- Under `ReplyLost` the state is 0 at the start, whatever the chain has taken in. -/
theorem replySt_start (h : ReplyLost Q ε early Lg) (y : E.Str) (x₀ : Y) :
    replySt Q ε early Lg y x₀ (PTr.empty Q.shape) = false :=
  replySt_eq_false.2 ((lost_empty _ _ _).2 (h x₀ y))

/-- A prover message never changes 0 to 1. -/
theorem replySt_prover (y : E.Str) (x₀ : Y) : ProverLaw Q.shape (replySt Q ε early Lg y x₀) :=
  fun τ m h => replySt_eq_false.2 (Lost.prover _ _ _ τ m (replySt_eq_false.1 h))

/-- At the end: if the state at the early part of x is 0 and x is not in the language, the verifier
rejects x. -/
theorem replySt_full (y : E.Str) (x : Y) (τ : Tr Q.shape) (hL : ¬ Lg x y)
    (h : replySt Q ε early Lg y (early x) (.full τ) = false) : Q.accept x y τ = false := by
  have h1 := (lost_full _ _ _ τ).1 (replySt_eq_false.1 h)
  cases ha : Q.accept x y τ with
  | false => rfl
  | true => exact absurd (h1 x rfl ha) hL

/-- The law on verifier messages. -/
theorem replySt_ver (y : E.Str) (x₀ : Y) : VerLaw Q.shape ε (replySt Q ε early Lg y x₀) :=
  fun τ h =>
    le_trans (cnt_mono fun _ hc => replySt_eq_true.1 hc)
      (Lost.verifier _ _ _ τ (replySt_eq_false.1 h))

/-- The law on verifier messages of a batch, for a protocol with local rounds only. -/
theorem replySt_joint (N : ℕ) (y : E.Str) (x : Fin N → Option Y) :
    JointLaw N Q.shape (RoundSplits.allLocal Q.shape) ε fun j => (x j).map (replySt Q ε early Lg y) := by
  have h := BatchH4.jointLaw_of_verLaw N Q.shape (RoundSplits.allLocal Q.shape) ε
    (fun j => (x j).map (replySt Q ε early Lg y)) (fun j S hS => by
      obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
      exact replySt_ver y xj)
  rwa [Compile.Batch.timesShared_allLocal] at h

/-- The law on verifier messages of a batch, for any annotation of the rounds: with the errors of
the shared rounds multiplied by the number N of slots (the library's `jointLaw_of_verLaw`). -/
theorem replySt_joint_times (N : ℕ) (A : RoundSplits Q.shape) (y : E.Str) (x : Fin N → Option Y) :
    JointLaw N Q.shape A (Err.timesShared N A ε) fun j => (x j).map (replySt Q ε early Lg y) :=
  BatchH4.jointLaw_of_verLaw N Q.shape A ε (fun j => (x j).map (replySt Q ε early Lg y))
    (fun j S hS => by
      obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
      exact replySt_ver y xj)

/-- Under `ReplyLost`: the three laws of a state function that `Compile.Batch.mem_of_accepted` asks
along the sequence of instances that the chain has taken in, at the constant sequence
`fun _ => early x`. -/
theorem replySt_laws (h : ReplyLost Q ε early Lg) (x : Y) :
    (∀ y, ¬ Lg x y →
      replySt Q ε early Lg y ((fun _ : ℕ => early x) 0) (PTr.empty Q.shape) = false) ∧
    (∀ y (τ : AtP Q.shape) (m : τ.round.Msg), ¬ Lg x y →
      replySt Q ε early Lg y ((fun _ : ℕ => early x) (τ.idx - 1)) (.atP τ) = false →
      replySt Q ε early Lg y ((fun _ : ℕ => early x) τ.idx) (.atV (τ.snoc m)) = false) ∧
    (∀ y τ, ¬ Lg x y →
      replySt Q ε early Lg y ((fun _ : ℕ => early x) (Q.shape.length - 1)) (.full τ) = false →
      Q.accept x y τ = false) :=
  ⟨fun y _ => replySt_start h y _, fun y τ m _ h0 => replySt_prover y _ τ m h0,
    fun y τ hL h0 => replySt_full y x τ hL h0⟩

/-- Under `ReplyLost`: the library's soundness of a batch protocol for an instance of which the
chain takes in the early part alone (`SndBL` at late = none), for a protocol with local rounds
only. -/
theorem sndBL_of_replyLost (h : ReplyLost Q ε early Lg) (N : ℕ) :
    (BatchInteractiveOracleProof.ofProto Q).SndBL N early none Lg ε :=
  ⟨fun n hn => (by cases hn), replySt Q ε early Lg,
    fun y x _ => replySt_start h y _,
    fun y x τ m h0 => replySt_prover y x τ m h0,
    fun y x τ _ hn => (by cases hn),
    fun y x τ hL h0 => replySt_full y x τ hL h0,
    fun y x => replySt_joint N y x⟩

/-! ## The hypothesis beside the library's notions -/

/-- It is enough to ask the hypothesis at the early parts of instances: where x₀ is the early part
of no instance, the goal holds of every transcript. -/
theorem replyLost_iff_range :
    ReplyLost Q ε early Lg ↔ ∀ x y, Doomed Q.shape ε (replyGoal Q early Lg (early x) y) := by
  refine ⟨fun h x y => h (early x) y, fun h x₀ y => ?_⟩
  by_cases hx : ∃ x, early x = x₀
  · obtain ⟨x, rfl⟩ := hx
    exact h x y
  · exact Doomed.of_forall _ _ fun τ x hx' _ => absurd ⟨x, hx'⟩ hx

/-- The hypothesis gives round-by-round soundness for each instance by itself, with the same
errors, whatever early is. -/
theorem ReplyLost.sound (h : ReplyLost Q ε early Lg) : Q.Sound Lg ε := by
  intro x y hL
  refine Doomed.mono _ _ (fun τ hτ => ?_) (h (early x) y)
  cases ha : Q.accept x y τ with
  | false => rfl
  | true => exact absurd (hτ x rfl ha) hL

/-- With nothing left out (early the identity) the hypothesis is the library's round-by-round
soundness. -/
theorem replyLost_id_iff : ReplyLost Q ε id Lg ↔ Q.Sound Lg ε := by
  refine ⟨ReplyLost.sound, fun h x₀ y => ?_⟩
  by_cases hL : Lg x₀ y
  · exact Doomed.of_forall _ _ fun τ x hx _ => by
      have hx' : x = x₀ := hx
      rw [hx']
      exact hL
  · refine Doomed.mono _ _ (fun τ hτ x hx ha => ?_) (h x₀ y hL)
    have hx' : x = x₀ := hx
    rw [hx', hτ] at ha
    cases ha

/-- The hypothesis gives the library's soundness for statements that are fixed late (`LateSound`,
Iop/Late.lean), jointly up to every round n. The converse is not shown. -/
theorem ReplyLost.lateSound (h : ReplyLost Q ε early Lg) (y : E.Str) (n : ℕ) :
    LateSound Q.shape n early ε (fun x => ¬ Lg x y) (fun x τ => Q.accept x y τ = false) := by
  intro x₀
  refine JDoomed.of_all n _ _ (Doomed.mono _ _ (fun τ hτ φ => ?_) (h x₀ y))
  cases ha : Q.accept φ.1 y τ with
  | false => exact ha
  | true => exact absurd (hτ φ.1 φ.2.1 ha) φ.2.2

end

/-! ## One call of the library's theorem on one compiled protocol, and one of `laneOf_ok` -/

section
open Rom Compile Compile.Batch
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

/-- `Compile.Batch.mem_of_accepted` at the state function `replySt` and the constant sequence of
instances `fun _ => early x`. Its three hypotheses on the state function are replaced by one,
`ReplyLost`. hS and hx are the library's at this state function and this sequence. The library's ε,
the lane's errors, is called εl here, and is free as there (the event does not read it); ε here is
the state function's. Every other argument is carried over to the letter.
hx ties early to the interface: where no later query holds the instance (L.late = none) the chain
has taken in (xin x).map L.early in every round (Compile/Batch/LateX.lean: `instX`), so with Y = X,
xin = some and xout = id, hx says that early x is L.early x. The theorem does not assume L.late =
none; where L.late = some n, hx says from round n on that xout (xin x) is some (early x): with xin =
some and xout = id, that x is its own early part. -/
theorem mem_of_accepted_reply (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop} (early : Y → Y)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε εl : Err Q.loc.shape)
    (hlost : ReplyLost Q.loc ε early Lg) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr)
    (hS : ¬ StepEvent
      (laneOf W t Q wq.sh prjS prjP εl (replySt Q.loc ε early Lg) xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (hx : ∀ i, xout (instX L (xin x) i) = some (early x))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE W.depthReq cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : Lg x (extY tr cms) :=
  mem_of_accepted t Q wq embS embP xin embE hOK hloc hco (replySt Q.loc ε early Lg) prjS hprjS prjP
    hprjP xout extY εl hM hF hS cms x π (fun _ => early x) hx hlate
    (replySt_laws hlost x).1 (replySt_laws hlost x).2.1 (replySt_laws hlost x).2.2
    hrun hstab hagree

/-- The library's `laneOf_ok` at the state function `replySt`, for a protocol with local rounds
only. Given the wire's law, the lane of the event in `mem_of_accepted_reply`, at εl = ε, has
`Lane.OK` (Compile/Batch/Facts.lean). The library's bound on that event (`Lane.pr_step_le`) asks
three things: `Lane.OK`, N = 2 ^ W.depthReq, and a bound on the errors. -/
theorem laneOf_reply_ok {t : Tag} {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E}
    {ws : RoundsQueryLayout lam W.K Q.shape (RoundSplits.allLocal Q.shape)}
    {prjS : (p : OPos Q.shape) → Body L → Option (OSym Q.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.shape (RoundSplits.allLocal Q.shape))}
    {ε : Err Q.shape} {early : Y → Y} {Lg : Y → E.Str → Prop} {xout : Option X → Option Y}
    {extY : Tc W → List (Dig lam) → E.Str} {N : ℕ}
    (hws : RoundsQueryLayout.OKG Q.shape (RoundSplits.allLocal Q.shape) ws) :
    (laneOf W t (BatchInteractiveOracleProof.ofProto Q) ws prjS prjP ε (replySt Q ε early Lg) xout extY).OK N :=
  laneOf_ok hws (replySt_joint N)

end

end OnBytes.Slice
