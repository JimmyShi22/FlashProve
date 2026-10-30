-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/AtValue.lean: what a value of the typing of a whole file holds where the first
queries of the three chains read it: the salt, the request root, the three silent rounds' plain
parts; and the two seals as read, in the spelling of OnBytes/TypedOracleCompiler/Run/ChainFRead.lean.

OnBytes/Maker/Page/Rows.lean asks these of a typed proof string π as hypotheses, in general letters.
Here π is a value of `toBPrfW` (OnBytes/Maker/TypingW.lean).

Main theorems, each at `toBPrfW .. r = some π`.
  `value_salt`: there is a run's value of the first chain as read, and π's salt is its bits.
  `value_rtreq`: π's request root is the binding tree's root as read.
  `value_front`, `value_join`, `value_seam`: the plain parts of the front round, of the joining
    round and of the seam are pF, pJ, p3.
  `seals_read`: the two seals, from the record of the program's reading.

What is not claimed. That the typing returns. Nothing on the outer roots of a query, which are no
part of π. Nothing on soundness.


-/
import OnBytes.Maker.Page.RunsTools

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Params (Rounds)

section
variable (C : CK) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) (pF : TF) (pJ : TJ)
  (p3 : T3) (tabs : List (ℕ × List (ℕ × Row3)))
  (ext : (oneExternalString (2 ^ D.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
  (path : List ByteArray) (r : Proof.TailRead)
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
  (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π)
include h

/-- **The salt**: run₁ is fixed by the first equation. -/
theorem value_salt : ∃ run₁, r.first.out.run = some run₁ ∧ π.salt = bytesToBits run₁ := by
  unfold toBPrfW at h
  split at h
  · rename_i run₁ pl₁ pl₂ pl₃ e₁ _ _ _
    cases h
    exact ⟨run₁, e₁, rfl⟩
  · cases h

/-- **The request root.** -/
theorem value_rtreq : π.rtreq = bytesToDig r.place.root :=
  toBPrfW_rtreq C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r π h

/-- **The front round's plain part.** -/
theorem value_front : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1 = pF := by
  obtain ⟨pl₁, pl₂, pl₃, -, -, -, hp, -⟩ :=
    toBPrfW_parts C D tF tJ t3 pF pJ p3 tabs silent run ext salt path r π h
  rw [pls₁_A _ π _ _ _ hp]
  rfl

/-- **The joining round's plain part.** -/
theorem value_join : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1 = pJ := by
  obtain ⟨pl₁, pl₂, pl₃, -, -, -, hp, -⟩ :=
    toBPrfW_parts C D tF tJ t3 pF pJ p3 tabs silent run ext salt path r π h
  rw [pls₂_A _ π _ _ _ hp]
  rfl

/-- **The seam's plain part.** -/
theorem value_seam : (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = p3 := by
  obtain ⟨pl₁, pl₂, pl₃, -, -, -, hp, -⟩ :=
    toBPrfW_parts C D tF tJ t3 pF pJ p3 tabs silent run ext salt path r π h
  rw [pls₃_A _ π _ _ _ hp]
  rfl

end

/-- **The two seals as read**, in the spelling of OnBytes/TypedOracleCompiler/Run/ChainFRead.lean. -/
theorem seals_read {p : Proof.TailPublic} {block1 : Blk Proof.FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : Proof.FirstEnd} {S₁ : Fmt.SpecX}
    {r : Proof.TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : Proof.SharedEnd}
    {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃) :
    TypedOracleCompiler.Run.PQ.sealRead r.first.out = seal1 ∧ TypedOracleCompiler.Run.PQ.sealRead r.shared.out = seal2 :=
  ⟨sealRead_of_seal r.first seal1 T.first_seal, sealRead_of_seal r.shared seal2 T.shared_seal⟩

end OnBytes.Maker.Page
