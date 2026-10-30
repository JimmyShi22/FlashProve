-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingHolds.lean: the stored string that the compiled verifier builds from the typing
of a whole file holds what was read.

The compiled verifier (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, `afterB`) calls the decision at the
transcript `mkTr` and at the string that the stored table's wire record builds from the openings of
the external string. This file has two laws on that string.

  `toBPrfW_ext`   the openings of the external string in a value of `toBPrfW` are those put in.
  `build_atT`     the string built from the look-ups in one table holds, at a listed place, the
                  place and the listed column.

OnBytes/Maker/AcceptAtA.lean goes on from these to what the transcript holds.

Not claimed. That the typing returns a value. Nothing on hashes, paths or salts; nothing on
soundness.


-/
import OnBytes.Maker.TypingTr
import OnBytes.Maker.TypingViews
import OnBytes.Maker.TypeFile

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

section Whole
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- The openings of the stored table in a value of the typing are those given to it. -/
theorem toBPrfW_ext (pF : TF) (pJ : TJ) (p3 : T3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ D.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π) :
    π.ext = ext := by
  unfold toBPrfW at h
  split at h
  · cases h
    rfl
  · cases h

end Whole

/-- **The stored string.** The string that the stored table's wire record builds from the look-ups
in one table holds, at a listed place, the place and the listed column. -/
theorem build_atT (a : ℕ) (etab : List (ℕ × Row3)) (x : ℕ) (hx : x < 2 ^ a) (c : List UInt64)
    (s : Bits) (pt : List (Dig 256)) (h : etab.lookup x = some (c, s, pt)) :
    (weOne a).build (fun p => (atT (fun c => some (p.val, c)) etab p.val).map Opening.sym)
      ⟨x, hx⟩ = (x, c) := by
  show ((atT (fun c => some (x, c)) etab x).map Opening.sym).getD (0, []) = (x, c)
  unfold atT
  rw [h]
  rfl

end OnBytes.Maker
