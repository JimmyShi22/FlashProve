-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAsmProofs.lean: the statements of Cb/Req1/LdSegRefAsm.lean, proved.

The proofs use Cb/Ld/LdLkpAsm2PullProofs.lean (the assembled lookup on the named entries; the
number of its rows), Cb/Ld/LdLkpMultProofs.lean (valid vectors of multiplicities) and
Cb/Req1/LdSegRefDigProofs.lean.
What each statement says, and the limits: the head of Cb/Req1/LdSegRefAsm.lean.
-/
import Cb.Req1.LdSegRefAsm
import Cb.Req1.LdSegRefDigProofs
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpMultProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

theorem ldSegRef_asm_L : Spec.ldSegRef_asm_L := fun _ _ _ _ _ _ _ => rfl

open Classical in
theorem ldLkpMult_congr : Spec.ldLkpMult_congr := by
  intro E _ n T w W key t M M' hW h ⟨h1, h2, h3⟩
  refine ⟨fun u hu j hj => by rw [h u hu j hj]; exact h1 u hu j hj,
    fun u hu j hWj hj => by rw [h u hu j hj]; exact h2 u hu j hWj hj,
    fun x => ?_⟩
  rw [← h3 x]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < 2 ^ T := Finset.mem_range.1 (Finset.mem_filter.1 hu).1
  unfold multOf Alg.Lookup.mult
  refine Finset.sum_congr rfl fun j hj => ?_
  show (if decide (M' u j = 1) = true then 2 ^ j else 0) =
    if decide (M u j = 1) = true then 2 ^ j else 0
  rw [h u hu' j (lt_of_lt_of_le (Finset.mem_range.1 hj) hW)]

theorem ldSegRef_asm_mult : Spec.ldSegRef_asm_mult := by
  intro E Kc E₀ Wp _ _ X h hq hH hK hW hw hB x y m hT hv
  have hA : X.Q.sh.inC x.1 m := (ldSegRef_dg_allIn E Kc _ _ X.Q x.1 m h hq hH hK).2 hT
  have v1 : ∀ f < 2 ^ 1, Valid X.Q.v X.Q.d X.w (X.n + 1) (X.keyF (X.Q.T.ents m) f) (X.tabF f)
      (hbit X.Q.v (X.n + 1) (X.keyF (X.Q.T.ents m) f) (X.tabF f)) :=
    fun f hf => ldLkpMult_honest E X.Q.v X.Q.d X.w (X.n + 1) _ _ hW (hA f hf)
  have v2 :=
    ldLkpMult_shift E 1 X.Q.v X.Q.d X.w (X.n + 1) (X.keyF (X.Q.T.ents m)) X.tabF X.Q.tag _ v1 x.2
  show Valid (X.Q.v + 1) (1 + X.Q.d) X.w (X.n + 1) (shKey X.Q.v (X.keyF (X.Q.T.ents m)) X.Q.tag x.2)
    (shTab X.Q.d X.tabF X.Q.tag x.2) (X.A.H.bit (X.Q.T.ents m))
  rw [Nat.add_comm X.Q.v 1]
  exact ldLkpMult_congr E _ _ _ _ _ _ _ _ hw (fun Y hY j hj => hB m hv Y hY j hj) v2

theorem ldSegRef_asm_allB : Spec.ldSegRef_asm_allB := by
  intro E Kc E₀ Wp _ _ pp _ X hι hP hAdm
  refine (allB_one X.link).2 (ldSegRef_dg_sub E Kc _ _ X.Q X.mult X.ent X.A.nRows _ ?_ ?_)
  · exact ldLkpAsm2N_ok E pp X.A X.Q.Nn X.ι X.A.ValidMu X.Q.T E₀ Kc Wp X.Q.R1 X.Q.T.ents hι hP
      hAdm (ldLkpAsm2_muValid E X.A hAdm.1)
  · intro x y τ xo hx
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ldLkpAsm2N_len E X.A X.Q.Nn X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents _ _ _ _ hx'

theorem ldSegRef_asm_hyp : Spec.ldSegRef_asm_hyp := by
  intro E Kc E₀ Wp _ _ pp _ X h hPl hq hH hK ht hι hP hAdm hB
  have hW : 2 ^ X.Q.v < 2 ^ (X.n + 1) :=
    lt_trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) hAdm.2.1
  exact ldSegRef_dg_hyp E Kc _ _ X.Q X.mult X.ent X.A.nRows X.lk h hPl hq hH hK ht
    (ldSegRef_asm_mult E Kc _ _ X h hq hH hK hW hAdm.1 hB)
    (ldSegRef_asm_allB E Kc _ _ pp X hι hP hAdm)

end Cb
