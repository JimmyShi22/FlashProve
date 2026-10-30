-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesOn.lean: the second stops' shares, with a named parameter P
on what a part sees. `hid_held` (Honest/Law/SharesStops.lean) is stated at one input, and asks
its local bounds at what a part sees of that input and its trace. `hid_held_on` says the same with
the reason made a hypothesis of its own. `P` is a condition on an input with its trace; the local
bounds are asked at every v that satisfies P; and that this input with its trace satisfies P is a
hypothesis, `hP`.

What this is. A conditional lemma about the stops of Honest/Frame.lean and the library's own
probability (`Iop.prRho`): one application of `hid_held`. None of the library's goals. Probabilities
are over the verifier's messages, drawn uniformly (`Iop.prRho`), at a fixed private input
and instance.

Terms on whoever uses this lemma.
  (i) P is named in every lemma that uses the share: a hypothesis that is named, never a default. At
      a v with a larger cell the share is not small (7,200 cells of size 128 reach 921,600 against a
      window of 2^17). So "at every v" is false, and it must not be obtained by writing a zero for a
      cell.
  (ii) P reads the hidden input, so it is no public condition of fit. It has to be proved from
      validity, once, by name, as (P-small): every cell of a valid input's trace is at most 128 in
      size. By inspection, not proved in Lean: at a valid input the model's own trace has small
      cells at the cells that Lean's trace has. The relaxed relation itself admits traces with
      larger cells, so which trace the prover returns has to be named. The planes of multiplicities
      and the fill cells are a second half, which no "below 129" of the library reaches. Both halves
      have to be proved.
  (iii) Nobody quantifies the simulator or the environment after P in a way that lets P pick the
      inputs: P is a consequence of validity, the same in both worlds.

Trivially met. With P := False the local bounds hold trivially, but `hP` cannot be proved. With P :=
True, the local bounds are asked at every v. At lists of parts whose first stop always fires the
bound on `Hid` holds with 0: `Part.stopAt` (Honest/Side.lean) asks the first stop first, so the
second is never reached. The first stops' probability is bounded by another lemma (`bad_held`,
Honest/Law/SharesStops.lean).

  `hid_held_on`

Limits.
  * Nothing here proves `hP`, or any local bound.
  * Nothing here says which P serves.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesStops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
  [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)
  {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl}

/-- **`hid_held`, with the parameter P by name.** `hP`: this input with its trace satisfies P. `h₁`,
`h₃`: the local bounds, at every v that satisfies P. -/
theorem hid_held_on (Sf : StopsFit F H D pre₁ e₁) (w : W₀ × Rc × Sd) (x : Xi) (z₁ z₃ : ℝ≥0∞)
    (P : Local W₀ Rc Xi Tr → Prop)
    (hP : ∀ tr, H.trace w.1 x = some tr → P ⟨w.1, w.2.1, x, tr⟩)
    (h₁ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val) H.first C pre₁ D.ds₁ ∧
      ((chainGates (· == some Why.hid) (Face.own.sees v) (·.hidShare.val) H.first pre₁
        D.ds₁).map (·.p)).sum ≤ z₁)
    (h₃ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val) H.second C F.second.blocksInOrder
        D.ds₃ ∧
      ((chainGates (· == some Why.hid) (Face.own.sees v) (·.hidShare.val) H.second F.second.blocksInOrder
        D.ds₃).map (·.p)).sum ≤ z₃) :
    Iop.prRho ((honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x) ≤ z₁ + z₃ :=
  hid_held C D tF tJ t3 F silent B H J sh ext Sf w x z₁ z₃ (fun tr ht => h₁ _ (hP tr ht))
    (fun tr ht => h₃ _ (hP tr ht))

end

end ProofFile.Honest

#print axioms ProofFile.Honest.hid_held_on
