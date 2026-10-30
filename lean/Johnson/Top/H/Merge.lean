-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Merge.lean: the kind "claims on committed weights are batched and merged by one
sumcheck" as values of `BaseKind`, with its hypothesis and the proof of it.

Nothing new is proved: the proofs are `WeightsL.knowAt` (Cb/Pv/Lay/Weights.lean) and
`WFirstL.knowAt` (Cb/Pv/Lay/WeightsFirst.lean). The rounds: one in which the verifier draws an
element, whose powers are the claims' coefficients; then a sumcheck over the column bits under the
plain sum g(0) + g(1). The short sumcheck is the named filling `MergeL.V1` (Cb/Pv/Lay/Merge.lean):
in a round of a column bit the LINEAR coefficient is left out, in the round of the further variable
the constant one.

Main names:
  `MergeCaller E`: who calls the merge: the record G of the claims (their number, which may be 1;
    the summands; the masks' names and factors; the sent scalars), the further oracles, a signature
    `Sg` whose messages are the committed ones, the joint before it, the reading of the entries off
    the messages.
  `kMerge L`: the kind at a written list L of callers, with an empty message in the round of the
    draw.
  `merge_knowAt`, `merge_good`: all four facts; every block of the lifted kind has `KObj.BK.Good`.
  `HMerge`, `hMerge`: closed, at the field `Cb.Gl.E`: for every list of callers the kind is
    knowledge sound; its proof.
  `MergeSentCaller E`, `kMergeSent L`, `mergeSent_knowAt`, `mergeSent_good`, `HMergeSent`,
    `hMergeSent`: the same with one scalar sent in the round of the draw, which splits one more
    identity.
  `merge_errs`, `mergeSent_errs`: the errors, round by round.

Limits: a caller's record holds, beside data, proofs that each summand has degree at most 2 in each
variable (`deg`, `dege`): whoever writes a caller pays them. It is not said that the verifier of
`V1` is the one that the programs run at a given place: that the programs leave out the linear
coefficient there is by reading. Nor which summands give the model, nor how the joints meet a
neighbour's. The errors are counts of bad draws. Nothing is said on the honest prover, on
completeness or on zero knowledge.
-/
import Johnson.Top.KindKnowAt
import Cb.Pv.Lay.WeightsFirst
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Lay

section
variable (E : Type) [Field E] [Fintype E]

/-- Who calls the merge. -/
structure MergeCaller : Type 1 where
  G   : WeightsL E
  Ex  : ExtSpec
  Kc  : Type
  Wp  : Type
  /-- the signature: the committed messages are its -/
  Sg  : Sig E
  R0  : IOR.Rels Kc G.St Ex (Sg.Msg × Wp)
  msg : Sg.Msg → G.J → E

/-- Who calls the merge with one sent scalar. -/
structure MergeSentCaller : Type 1 where
  G   : WFirstL E
  Ex  : ExtSpec
  Kc  : Type
  Wp  : Type
  Sg  : Sig E
  R0  : IOR.Rels Kc G.St Ex (Sg.Msg × Wp)
  msg : Sg.Msg → G.J → E

variable {E}

/-- The kind, at a written list of callers. -/
@[reducible] noncomputable def kMerge (L : List (MergeCaller E)) : BaseKind.{1} E where
  Size := MergeCaller E
  sizes := L
  Sg := fun c => c.Sg
  Kc := fun c => c.Kc
  St := fun c => c.G.St
  St' := fun c => c.G.L.T.par.Out
  Wp := fun c => c.Wp
  Wp' := fun c => c.Wp
  E₀ := fun c => c.Ex
  E₀' := fun c => c.Ex
  R := fun c => c.G.blk (c.G.L.V1 c.Ex)
  A := fun c => c.G.relIn c.R0 c.msg
  B := fun c => c.G.L.relOut (c.G.R1 c.R0) c.msg
  ext := fun _ _ _ _ wp => wp
  ε := fun c => c.G.eps (Kc := c.Kc) (c.G.L.V1 c.Ex)

theorem merge_knowAt (L : List (MergeCaller E)) : (kMerge L).KnowAtAll :=
  fun c _ => c.G.knowAt c.R0 c.msg (c.G.L.V1 c.Ex)

theorem merge_good (L : List (MergeCaller E)) : ∀ c ∈ L, ((kMerge L).toKind.block c).Good :=
  BaseKind.good_of_knowAt (merge_knowAt L)

theorem merge_errs (L : List (MergeCaller E)) (c : MergeCaller E) :
    TWhole.errList ((kMerge L).ε c) = (c.G.n - 1) :: 1 :: (List.replicate c.G.k 2 ++ [1, 0]) :=
  c.G.errs (Kc := c.Kc) (c.G.L.V1 c.Ex)

/-- The kind with one sent scalar. -/
@[reducible] noncomputable def kMergeSent (L : List (MergeSentCaller E)) : BaseKind.{1} E where
  Size := MergeSentCaller E
  sizes := L
  Sg := fun c => c.Sg
  Kc := fun c => c.Kc
  St := fun c => c.G.St
  St' := fun c => c.G.L.T.par.Out
  Wp := fun c => c.Wp
  Wp' := fun c => c.Wp
  E₀ := fun c => c.Ex
  E₀' := fun c => c.Ex
  R := fun c => c.G.blk (c.G.L.V1 c.Ex)
  A := fun c => c.G.relIn c.R0 c.msg
  B := fun c => c.G.L.relOut (c.G.R1 c.R0) c.msg
  ext := fun _ _ _ _ wp => wp
  ε := fun c => c.G.eps (c.G.L.V1 c.Ex)

theorem mergeSent_knowAt (L : List (MergeSentCaller E)) : (kMergeSent L).KnowAtAll :=
  fun c _ => c.G.knowAt c.R0 c.msg (c.G.L.V1 c.Ex)

theorem mergeSent_good (L : List (MergeSentCaller E)) :
    ∀ c ∈ L, ((kMergeSent L).toKind.block c).Good :=
  BaseKind.good_of_knowAt (mergeSent_knowAt L)

theorem mergeSent_errs (L : List (MergeSentCaller E)) (c : MergeSentCaller E) :
    TWhole.errList ((kMergeSent L).ε c) = c.G.n :: 1 :: (List.replicate c.G.k 2 ++ [1, 0]) :=
  c.G.errs (c.G.L.V1 c.Ex)

end

/-- THE HOLE OF THE KIND, CLOSED: knowledge soundness alone, for every list of callers over the
protocol's field. -/
def HMerge : Prop := ∀ L : List (MergeCaller Cb.Gl.E), (kMerge L).Know

/-- Its discharge. -/
theorem hMerge : HMerge := fun L => BaseKind.know_of_knowAt (merge_knowAt L)

/-- The same with one sent scalar. -/
def HMergeSent : Prop := ∀ L : List (MergeSentCaller Cb.Gl.E), (kMergeSent L).Know

theorem hMergeSent : HMergeSent := fun L => BaseKind.know_of_knowAt (mergeSent_knowAt L)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hMerge
#print axioms VerifiableInference.OnPublicFiles.merge_good
#print axioms VerifiableInference.OnPublicFiles.hMergeSent
#print axioms VerifiableInference.OnPublicFiles.mergeSent_good
