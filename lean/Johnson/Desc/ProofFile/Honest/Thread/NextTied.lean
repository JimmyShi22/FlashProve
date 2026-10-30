-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/NextTied.lean: `SaidNext` AT THE LAST CHAIN's LETTER. `BaseTied` is
carried with no premise, so `saidNext_field_of_owes` asks only what it asks of every field letter.

  `saidNext_tied`   `SaidNext` at `SaidField T (BaseTied F T)`, at every number: the field `next₃`
  `saidNext_tied_at`   the same with `DepthsAt` asked only at stands behind a member, under `Thr`

What these are. Conditional lemmas on our own definitions. None is one of the library's goals. The
last chain has no walk, so `hdp` of `saidNext_tied_at` is asked where `Thr` and the letter hold in
front of the member: the input is valid and the challenges fit there. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BaseTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Tr X V Pb : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
  (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)

/-- **The field `next₃`.** -/
theorem saidNext_tied (hfit : T.fits T.bs.length = true)
    (o : OwesS T (SaidField T (BaseTied F T)))
    (hst : ∀ b, b < T.bs.length → T.fresh b ≠ [] → ∀ blk, T.bs[b]? = some blk →
      ∀ (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn),
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b, b < T.bs.length → ∀ (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X),
      DepthsAt T (b + 1) k m) :
    ∀ b, SaidNext T (SaidField T (BaseTied F T)) b :=
  saidNext_field_of_owes T hfit o hst (fun b _ => baseTied_kept F T b) ho hdp

/-- **The field `next₃`, with `DepthsAt` asked only behind a member, from `Thr` and the letter.** -/
theorem saidNext_tied_at (hfit : T.fits T.bs.length = true)
    (o : OwesS T (SaidField T (BaseTied F T)))
    (hst : ∀ b, b < T.bs.length → T.fresh b ≠ [] → ∀ blk, T.bs[b]? = some blk →
      ∀ (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn),
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E →
      SaidField T (BaseTied F T) b k m → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → DepthsAt T (b + 1) k (y.2.took cols)) :
    ∀ b, SaidNext T (SaidField T (BaseTied F T)) b := by
  intro b blk hblk k s m E ds y cols hA hS hd hM
  have hj := lt_of_member T hblk
  have hT : TreesNext T (SaidField T (BaseTied F T)) b := by
    by_cases h : T.fresh b = []
    · exact treesNext_of_fresh_nil T h
    · exact treesNext_of_playsS T (o b hj).1 (hst b hj h)
  have hTr := hT blk hblk k s m E ds y cols hA hS hd hM
  have hD := hdp b blk hblk k s m E ds y cols hA hS hd hM
  obtain ⟨hOk, base, hB, hL⟩ := hS
  exact ⟨saidNext_ok T b blk hblk k s m E ds y cols hA hOk hd hM, base,
    baseTied_kept F T b blk hblk k m E ds y cols base hM hB,
    field_all_next T hfit (Nat.le_of_lt hj) hblk hA hM hTr hL (ho b hj) hD⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.saidNext_tied
#print axioms ProofFile.Honest.saidNext_tied_at
