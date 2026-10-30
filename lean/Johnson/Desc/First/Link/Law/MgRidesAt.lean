-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/MgRidesAt.lean: THE SEVEN RIDERS ON THE TABLE's MEANING (`MgRides`,
QuietRides.lean) AT THE COMPOSED MEANING ITSELF, OVER THE CLOSED BASE (`mgAll 𝔇 mgBase`,
Johnson/Desc/Sound/MgAll.lean, MgBase.lean), AT A LINK's THREE QUIET SUB-PROTOCOLS OF THE BATCHING
KIND AND THE FRAME (our files call a sub-protocol a block): the batching, the frame's sub-protocol
behind it, the shutting. A theorem: the assembly of OracleRides.lean, PubStep.lean and
PubFitK9.lean.

What is said.
  `QuietAsks`: what is asked of the two states of the verifier in front of and behind the
    sub-protocol, and of the composed meaning's parameters: `Rb`; `rest9`; «the ledger is well laid»
    is kept; the oracles' strings behind are what a stage leaves; `OracleAsks` at the parameters
    𝔇.decT and 𝔇.smp; and, behind the frame's sub-protocol alone, «the one sum can be taken».
    `mgRides_at`: **`MgRides Nm (mgAll 𝔇 mgBase) links pl z k p a b` from `QuietAsks` and the yes
    of the Bool `pubFit9` at the composed filling's list of extra public tests.**

How each rider goes. «decodes», «shown», «no collision», «held»: OracleRides.lean, the composed
meaning's four fields being the library's notions by definition. «In order»: over the closed base it
is a test on the public part alone. The public items: PubStep.lean under `pubFit9`. What the public
items say beside their Bool: none of the two items that say something is open behind (`pubFit9`'s
second half); every other item that is open behind is «hasRow» or one to which `First.saysNone`
gives «no sentence is meant» (the same half): there the composed meaning's sentence holds over the
closed base as MgBase.lean has it (`mgAll_pubP_said`).

Limits. `QuietAsks` IS A LIST OF PREMISES: `Rb`, `rest9` and «the ledger is well laid» are paid at
the three sub-protocols under the runs' share (BkLink.lean, Rest9.lean, SizedRides.lean); the
strings by `out_strs`; `OracleAsks` (a fence on the plan's numbers; two sentences on parameters that
are letters) by nobody; «the one sum can be taken» behind the frame's sub-protocol by nobody. The
one equation's sub-protocol is not here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Desc.First.Link.Law.PubFitK9
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub Numbers)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **What is asked of the two states and of the parameters.** i: 1: the batching; 2: the frame's
sub-protocol behind it; 5: the shutting. -/
structure QuietAsks (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m i : ℕ)
    (a b : S × F.E.Str) : Prop where
  rb : Rb a.1 b.1
  rest : ∃ L₀ F₀ t₀, rest9 L₀ F₀ t₀ b.1 = rest9 L₀ F₀ t₀ a.1
  ledger : ledgerOk a.1 = true → ledgerOk b.1 = true
  strs : ∃ (base : ℕ) (ds : List RDT) (τ : Iop.Tr (uLT C ds)), b.2 = behind C F base ds a.2 τ ∧
    OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k base a.1 b.1
  total : i = 2 → K9.totalIn (𝔇.pubD.N.group m) b.1 = true

/-- **MgRides AT THE COMPOSED MEANING.** -/
theorem mgRides_at (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m i : ℕ)
    (p : Place) (hfit : pubFit9 true moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2 ∨ i = 5)
    (a b : S × F.E.Str) (A : QuietAsks (C := C) 𝔇 Nm links pl z k m i a b) :
    MgRides Nm (mgAll 𝔇 mgBase) links pl z k p a b := by
  obtain ⟨base, ds, τ, hb, O⟩ := A.strs
  obtain ⟨L₀, F₀, t₀, hrest⟩ := A.rest
  have hmore : (mgAll 𝔇 mgBase).more = moreAll := mgAll_more_base 𝔇
  obtain ⟨hB, hnl⟩ := fit9_at moreAll links pl hfit k m i p hp hl hpc hi
  refine mgRides_of 𝔇.cs 𝔇.G 𝔇.decT 𝔇.smp 𝔇.ms Nm (mgAll 𝔇 mgBase) links pl z k p
    (mgAll_decodes 𝔇 mgBase) (mgAll_shown 𝔇 mgBase) (mgAll_noColl 𝔇 mgBase)
    (mgAll_held 𝔇 mgBase) base ds a b τ hb A.rb O (fun h => h) ?_ ?_
  · rw [hmore]
    refine pubHeld_step (mgAll 𝔇 mgBase) 𝔇.pubD _ (mgAll_pub 𝔇 mgBase) _ _ _ _ _ z a.1 b.1 hB
      (sameOn_of 𝔇.pubD L₀ F₀ t₀ a.1 b.1 A.rb hrest) (fun _ => rfl) A.ledger fun q hq => ?_
    by_cases h2 : i = 2
    · rw [if_pos h2] at hq
      obtain rfl : q = .totalIn m := by simpa using hq
      exact A.total h2
    · rw [if_neg h2] at hq
      exact absurd hq (List.not_mem_nil)
  · rw [hmore]
    intro _ q hq
    have h1 := List.all_eq_true.1 hnl q hq
    cases q with
    | left _ => simp [notLeft] at h1
    | leftOn _ => simp [notLeft] at h1
    | hasRow _ => trivial
    | _ => exact mgAll_pubP_said 𝔇 _ _ h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mgRides_at
