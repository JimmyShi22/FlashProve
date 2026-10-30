-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/CommitterAt.lean: the index committer's share (`Committer`,
Honest/Committer.lean) put at one item of the statement. `Committer.prover` puts the encoded index's
columns at every item: "one stored table". Here the columns are put at one named item; and where a
prover already has just these columns and the committer's key, the resulting prover is that prover.
Definitions, and one statement with its proof, by unfolding.

  `Committer.proverAt`   H with the committer's columns at the item `item₀`, none at another, and
     the committer's key
  `honestCAt`   the definition of `honestC` at that prover
  `Committer.proverAt_self`   where H has that key and these columns: `Cm.proverAt item₀ H = H`

What it is for. A lemma on the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns then speaks of the
prover that `honestCAt` runs, at a filling whose columns are the committer's.

Limits.
  * As those of Honest/Committer.lean: `tie` is a hypothesis; nothing compares `enc` with a code or
    `ood` with `enc`.
  * The library's external string is still computed from `enc` alone (`Committer.ext`).
  * Nothing on a run, a coin or a measure.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Committer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK)

variable {W₀ Rc Sd X Xi Ky Tr X₀ Xh TF TJ T3 : Type}

/-- **A prover whose stored table, at one item, and key are the committer's**: H's other fields
stay. -/
def Committer.proverAt (Cm : Committer W₀ Rc Sd X Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ Xh) : Prover W₀ Rc Xi Ky Tr X₀ Xh :=
  { H with
    stored := fun w₀ rc it x => if it == item₀ then Cm.enc w₀ rc x else none
    key := Cm.key }

/-- **Where a prover has the committer's key and just these columns, `proverAt` returns that
prover.** -/
theorem Committer.proverAt_self {Cm : Committer W₀ Rc Sd X Xi Ky} {item₀ : Nat}
    {H : Prover W₀ Rc Xi Ky Tr X₀ Xh} (hk : H.key = Cm.key)
    (hs : ∀ w₀ rc it x, H.stored w₀ rc it x = if it == item₀ then Cm.enc w₀ rc x else none) :
    Cm.proverAt item₀ H = H := by
  have hs' : H.stored = fun w₀ rc it x => if it == item₀ then Cm.enc w₀ rc x else none :=
    funext fun w₀ => funext fun rc => funext fun it => funext fun x => hs w₀ rc it x
  unfold Committer.proverAt
  rw [← hk, ← hs']

/-- **The honest side of the file's protocol, with one committer, its columns at one item**:
`honestB` at `Committer.proverAt`, the committer's string and key. -/
noncomputable def honestCAt (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (Cm : Committer W₀ Rc Sd X Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ Xh) {R2 R3 : Type} [Fintype R2] [Nonempty R2] [Fintype R3]
    [Inhabited R3] (front : R2 → R3 → W₀ → Rc → Sd → Xi → TF) (join : R2 → W₀ → Rc → Sd → TJ)
    (seam : R2 → R3 → W₀ → Rc → Sd → Xi → T3) :
    Iop.BatchHonestProver (batchOf C D tF tJ t3 F silent) (W₀ × Rc × Sd) :=
  honestB C D tF tJ t3 F silent B (Cm.proverAt item₀ H)
    (fun r2 r3 => Cm.seam (front r2 r3) (join r2) (seam r2 r3)) (Cm.ext D.a)

end ProofFile.Honest

#print axioms ProofFile.Honest.Committer.proverAt_self
