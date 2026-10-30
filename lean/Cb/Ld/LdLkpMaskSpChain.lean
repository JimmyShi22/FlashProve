-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskSpChain.lean: n + 1 masked blocks in a row, the claims between them being what the
honest run so far has made true (`MJ.sp`, `MJ.Link`: Cb/Ld/LdLkpMaskSp.lean).
This file does for n + 1 reductions in a row what Cb/Ld/LdLkpMaskSp.lean does for two.

Definitions, statements and proofs. Glue.

Main names:
  `MJ.spTo X b D C l`: the claim before block l.
  `mjsp_chain`: what the chain b 0, .., b n makes of C is the claim before block n + 1.
  `mjst_spTo`: the claim before block l does not read S, if C does not and no message of an earlier
    block does.
  `mjl_chain`: the chain, started with C, is a link, under three premises (`Sr l` and `Sw l` are the
    two sets of block l's link: `MJ.Link`, Cb/Ld/LdLkpMaskSp.lean):
    (1) block l, started with the claim before it, is a link (l ≤ n);
    (2) what an earlier block's messages read (`Sr l`) and what a later block writes (`Sw l'`) are
        disjoint;
    (3) C reads no `Sw l` (l ≤ n), in which the chain's own masks lie.
    The chain's two sets are the unions of the `Sr l` and of the `Sw l` over l ≤ n.

Notation: `J`: the type that names the entries; `E`: the type of their values; `b l`: block l
(`BkA`, Cb/Ld/LdLkpTreeP.lean); `D l`: its `MJ` record (Cb/Ld/LdLkpMaskChain.lean); `C`: the claim
before block 0 (`MJ.spTo .. 0`); `rd`: a map `M × Wp → J → E`: from a witness (`Honest`,
Ior/Honest.lean) to the entries' values.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskSp

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

section
variable {E J K M : Type} {Ex : ExtSpec} {Wp : Type} (X : ℕ → Type)
  (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R) (C : X 0 → (J → E) → Prop)

/-- The claim before block l. -/
def MJ.spTo : (l : ℕ) → X l → (J → E) → Prop
  | 0 => C
  | l + 1 => (D l).sp (MJ.spTo l)

theorem mjsp_chain : ∀ n, (MJ.chain X b D n).sp C = MJ.spTo X b D C (n + 1)
  | 0 => rfl
  | n + 1 => by
      funext x' k
      refine propext ((mjsp_seq (MJ.chain X b D n) (D (n + 1)) C x' k).trans ?_)
      rw [mjsp_chain n]
      exact Iff.rfl

theorem mjst_spTo (S : J → Prop) (Sr : ℕ → J → Prop) (hC : MjStab C S) :
    ∀ l, (∀ l' < l, (D l').MReads (Sr l')) →
      (∀ l' < l, ∀ j, Sr l' j → ¬ S j) → MjStab (MJ.spTo X b D C l) S
  | 0, _, _ => hC
  | l + 1, hR, hd =>
    mjst_sp (mjst_spTo S Sr hC l (fun l' h => hR l' (Nat.lt_succ_of_lt h)) fun l' h =>
        hd l' (Nat.lt_succ_of_lt h))
      (hR l (Nat.lt_succ_self l)) (hd l (Nat.lt_succ_self l))

theorem mjl_chain (rd : M × Wp → J → E) (Sr Sw : ℕ → J → Prop) :
    ∀ n, (∀ l ≤ n, (D l).Link (b l).H rd rd (Sr l) (Sw l) (MJ.spTo X b D C l)) →
      (∀ l l', l < l' → l' ≤ n → ∀ j, Sr l j → ¬ Sw l' j) → (∀ l ≤ n, MjStab C (Sw l)) →
      (MJ.chain X b D n).Link (BkA.chain X b n).H rd rd (fun j => ∃ l ≤ n, Sr l j)
        (fun j => ∃ l ≤ n, Sw l j) C
  | 0, hL, _, _ =>
    mjl_mono (hL 0 (le_refl 0)) (fun _ h => ⟨0, le_refl 0, h⟩) fun _ h => ⟨0, le_refl 0, h⟩
  | n + 1, hL, hd, hs => by
      have h2 := hL (n + 1) (le_refl _)
      rw [← mjsp_chain X b D C n] at h2
      exact mjl_mono
        (mjl_seq (mjl_chain rd Sr Sw n (fun l hl => hL l (Nat.le_succ_of_le hl))
            (fun l l' h1 h2 => hd l l' h1 (Nat.le_succ_of_le h2))
            fun l hl => hs l (Nat.le_succ_of_le hl))
          h2 (fun j ⟨l, hl, hj⟩ => hd l (n + 1) (Nat.lt_succ_of_le hl) (le_refl _) j hj)
          (hs (n + 1) (le_refl _)))
        (fun _ h =>
          h.elim (fun ⟨l, hl, hj⟩ => ⟨l, Nat.le_succ_of_le hl, hj⟩) fun hj =>
            ⟨n + 1, le_refl _, hj⟩) fun _ h =>
              h.elim (fun ⟨l, hl, hj⟩ => ⟨l, Nat.le_succ_of_le hl, hj⟩) fun hj =>
                ⟨n + 1, le_refl _, hj⟩

end
end Cb
