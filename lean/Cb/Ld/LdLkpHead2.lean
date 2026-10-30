-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpHead2.lean: the first part of the lookup argument, for `LkAsm2` (Cb/Ld/LdLkpAsm2.lean):
the head (first challenge, tie) without the claim on the idle bit positions.

Definitions, statements (in `Cb.Spec`) and proofs.
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).

The block is that of Cb/Ld/LdLkpHead.lean (`H.headA`), unchanged. There the joint after the head
has, beside "all bits are bits" and "the multiplicities sum to the number of keys", the claim "the
product of the table at every idle bit position is 1" (`H.Idle`), and "the vector is the
multiplicities" has to imply it (`H.MuOK`). With the public factor in the table's leaf
(Cb/Ld/LdLkpInst2.lean) that product is 1 for all messages, and the claim falls.

Main names:
  `H.RestOn x m`: all bits are bits; the multiplicities sum to the number of keys.
  `H.MuOn Mu`: what is asked of "the vector is the multiplicities": for keys in the table, the claim
    after λ (`LkB.mid`, Cb/Ld/LdLkp.lean) holds at every λ. Nothing on idle positions.
  `ldLkpHead2_good`: under `H.lkb.Adm p`, p the characteristic of E, and `H.MuOn Mu`, for any joint
    R0 that rides along (`cj`, Cb/Ld/LdLkpKit.lean), the head leads from "every key is in the table
    [exact: and Mu]" to `RestOn` [exact: and Mu], what the tie has done, the tie's open claim
    (`BkA.Good`).
  `ldLkpHead2_mu`: under `H.lkb.Adm p`, the honest bits (first-occurrence rule) meet `H.MuOn`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpHead

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

namespace LkHead
variable {E : Type} [Field E] [Fintype E] (H : LkHead E)

/-- What waits after λ beside the identity. -/
def RestOn (_ : H.St × E) (m : H.J → E) : Prop :=
  Bits H.d H.w (H.bit m) ∧ NumKeys H.v H.d (H.n + 1) (H.bit m)

/-- What is asked of "the vector is the multiplicities". -/
def MuOn (Mu : H.St → (H.J → E) → Prop) : Prop :=
  ∀ st m, H.lkb.inR st m → Mu st m → ∀ lam : E, H.lkb.mid (st, lam) m

end LkHead
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The head. -/
def ldLkpHead2_good : Prop :=
  ∀ (p : ℕ) [CharP E p] (H : LkHead E) (Mu : H.St → (H.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (R0 : Rels Kc H.St Ex (M × Wp)) (msg : M → H.J → E),
    H.lkb.Adm p → H.MuOn Mu →
    (H.headA Ex M Wp Kc msg).Good (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg (fun x => ((H.tie.lv (H.n + 1)).base x.2).1)
        (fun x m =>
          ((H.RestOn ((H.tie.lv (H.n + 1)).base x.2) m ∧ Mu ((H.tie.lv (H.n + 1)).base x.2).1 m) ∧
            H.tie.Done H.n x.2 m) ∧
          H.tie.claim (H.n + 1) x m) fun x m =>
            (H.RestOn ((H.tie.lv (H.n + 1)).base x.2) m ∧ H.tie.Done H.n x.2 m) ∧
            H.tie.claim (H.n + 1) x m)

def ldLkpHead2_mu : Prop := ∀ (p : ℕ) (H : LkHead E), H.lkb.Adm p → H.MuOn H.lkb.IsMult

def ldLkpHead2_of : Prop := ∀ (H : LkHead E) (Mu : H.St → (H.J → E) → Prop), H.MuOK Mu → H.MuOn Mu

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpHead2_of : Spec.ldLkpHead2_of E := fun _ _ h st m hin hm lam => (h st m hin hm lam).1

theorem ldLkpHead2_mu : Spec.ldLkpHead2_mu E := fun p H hA =>
  ldLkpHead2_of E H _ (ldLkpHead_muOK E p H hA)

theorem ldLkpHead2_good : Spec.ldLkpHead2_good E := by
  intro p _ H Mu Ex Kc M Wp R0 msg hA hMu
  have g1 : GoodAt (IOR.draw E (Prod.mk : H.St → E → H.St × E) Ex)
      (Honest.draw E Prod.mk Ex (M × Wp)) (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg Prod.fst (fun x m => H.lkb.mid x m ∧ Mu x.1 m) H.lkb.mid) (fun _ _ _ wp => wp)
      (Nums.draw Kc E Prod.mk Ex (2 ^ H.v - 1)) := by
    refine goodAt_draw Kc M H.St (H.St × E) Ex Wp E Prod.mk _ _ (2 ^ H.v - 1) ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_
    · intro st y w β h
      exact ⟨h.1, hMu st _ h.2.1 h.2.2 β, h.2.2⟩
    · intro st y m _
      refine (cnt_mono fun β hβ => ?_).trans
        (ldLkp_lambda_cnt E H.St (H.J → E) H.J p H.lkb st (msg m) hA)
      obtain ⟨wp, h1, h2⟩ := hβ
      exact ⟨h1.2, fun h => h2 ⟨h1.1, h⟩⟩
  have hstep : H.tie.StepTo H.n := fun st m j hj =>
    (ldLkpTie_hU E (H.n + 1) (H.PT st m) (Nat.succ_pos _)).1 j hj
  have g2 := ldLkpTie_chain E H.tie Ex M Wp Kc msg
    (cj R0 msg Prod.fst (fun x m => H.RestOn x m ∧ Mu x.1 m) H.RestOn) H.n hstep
  unfold BkA.Good at g2 ⊢
  rw [ldLkpTieR_cj E H.tie Ex Kc H.St M Wp R0 msg Prod.fst
      (fun x m => H.RestOn x m ∧ Mu x.1 m) H.RestOn H.n] at g2
  have hq : ∀ (x : H.St × E) (m : H.J → E),
      H.tie.Q x m 0 = ∏ j ∈ range (H.n + 1), tabProd H.d (H.tab x.1) (H.bit m) x.2 j ^ 2 ^ j :=
    fun x m => (ldLkpTie_hU E (H.n + 1) (H.PT x m) (Nat.succ_pos _)).2.2
  have g3 := goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _
    (cj R0 msg Prod.fst (fun x m => H.lkb.mid x m ∧ Mu x.1 m) H.lkb.mid) _ _ _ _
    (fun x : H.St × E => ((0 : E), x)) ?_ ?_ ?_ ?_ g2
  · exact goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ _ _ _ (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ g1 g3 fun _ _ _ _ _ _ _ => rfl
  · intro x y w h
    obtain ⟨hR, ⟨⟨hb, hn, hid⟩, _⟩, hm⟩ := h
    refine ⟨⟨hR, ⟨hb, hn⟩, hm⟩, ?_⟩
    show keyProd H.v (H.key x.1 (msg w.1)) x.2 - H.tie.Q x (msg w.1) 0 = 0
    rw [hq]
    exact sub_eq_zero.mpr hid
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro x y w _ h
    obtain ⟨⟨hR, hb, hn⟩, hc⟩ := h
    have hc' : keyProd H.v (H.key x.1 (msg w.1)) x.2 - H.tie.Q x (msg w.1) 0 = 0 := hc
    rw [hq] at hc'
    exact ⟨hR, ⟨hb, hn, sub_eq_zero.mp hc'⟩, trivial⟩

end
end Cb
