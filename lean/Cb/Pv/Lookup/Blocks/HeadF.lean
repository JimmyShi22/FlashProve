-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/HeadF.lean: the head of a lookup with padding: the point's draw, then the tie.

Definitions, statements (in `Cb.Spec`) and proofs. As Cb/Ld/LdLkpHead2.lean, with the padding of
Cb/Pv/Lookup/Alg/PadAlg.lean and the tie of Cb/Pv/Lookup/Blocks/TieF.lean.

Main names:
  `LkHeadF`: sizes, keys, table, the places of the counts' bits, the padding. n + 2 of the 2^w bit
    positions count.
  `H.fac`: the public factor. `H.midF`: the claim after the draw (`MidP`).
  `H.RestF`: all are bits; the counts sum to the number of keys that are not padding.
  `H.numRowF`: that sum as a linear row (`Spec.headF_num`).
  `H.MuOnF Mu`: what is asked of "the vector is the multiplicities": for keys in the table, where Mu
    holds, `H.midF` holds at every value of the point.
  `Spec.headF_cnt`: if a key is no row of the table, `H.midF` holds for at most 2^v - 1 values of
    the point.
  `Spec.headF_good`: draw and tie together are good (`BkA.Good`, Cb/Ld/LdLkpTreeP.lean) from "every
    key is a row of the table [exact: and Mu]" to `H.RestF` [exact: and Mu], what the tie has done
    (`TieF.Done`) and the tie's open claim.
  `Spec.headF_mu`: the honest bits, padding not counted (`H.IsMultP`), meet `H.MuOnF`.
  `Spec.headF_open`: the tie's open claim is on the product at the highest position that counts.
Premises: `H.lkb.Adm p` (Cb/Ld/LdLkp.lean; p the characteristic of E) and `padsOK`; for
`Spec.headF_good` also `H.MuOnF Mu`. The sumcheck is a parameter (`PscBk`); the lists of errors
(`Spec.headF_ll`) are for `PscBk.lib`.
Limits: `H.RestF`, the tie's rows and the claims on the products are left to the blocks that follow.

-/
import Cb.Pv.Lookup.Alg.PadAlg
import Cb.Pv.Lookup.Blocks.TieFRows
import Cb.Ld.LdLkpHead2

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

noncomputable section

/-- The data of the lookup's head, for the tie `TieF`. n + 2 of the 2^w bit positions count. -/
structure LkHeadF (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  v : ℕ
  d : ℕ
  w : ℕ
  n : ℕ
  key : St → (J → E) → ℕ → E
  tab : St → ℕ → E
  bAt : ℕ → ℕ → J
  /-- The public padding: (row of the table, how many padding keys hold it). -/
  pads : List (ℕ × ℕ)
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cZ  : J
  cAt : ℕ → Bool → J

attribute [instance] LkHeadF.finJ LkHeadF.decJ

namespace LkHeadF
variable {E : Type} [Field E] [Fintype E] (H : LkHeadF E)

def bit (m : H.J → E) : ℕ → ℕ → E := fun u j => m (H.bAt u j)

/-- The lookup claim, on entries, as a record `LkB` (Cb/Ld/LdLkp.lean). -/
def lkb : LkB E H.St (H.J → E) H.J :=
  ⟨⟨H.v, H.d, H.key, H.tab, fun _ _ => True⟩, H.w, H.n + 2, H.bit, id⟩

def PT (x : H.St × E) (m : H.J → E) (j : ℕ) : E := tabProd H.d (H.tab x.1) (H.bit m) x.2 j

/-- The public factor, read off the state after λ. -/
def fac (x : H.St × E) : E := padFac (H.tab x.1) H.pads x.2

/-- The tie's data. -/
def tie : TieF E where
  St0 := H.St × E
  J := H.J
  a := H.fac
  PK := fun x m => keyProd H.v (H.key x.1 m) x.2
  PT := H.PT
  Q := fun x m j => Lkp.hU (H.n + 2) (H.PT x m) j
  wAt := H.wAt
  cZ := H.cZ
  cAt := H.cAt

/-- The claim after λ. -/
def midF (x : H.St × E) (m : H.J → E) : Prop :=
  MidP H.v H.d H.w (H.n + 2) (H.key x.1 m) (H.tab x.1) H.pads (H.bit m) x.2

/-- What waits after λ beside the identity: all are bits; the multiplicities sum to the number of
keys that are not padding. -/
def RestF (_ : H.St × E) (m : H.J → E) : Prop :=
  Bits H.d H.w (H.bit m) ∧ NumKeysP H.v H.d (H.n + 2) (padNum H.pads) (H.bit m)

/-- What is asked of "the vector is the multiplicities": as `LkHead.MuOn` (Cb/Ld/LdLkpHead2.lean),
with `midF` as the claim after λ. -/
def MuOnF (Mu : H.St → (H.J → E) → Prop) : Prop :=
  ∀ st m, H.lkb.inR st m → Mu st m → ∀ lam : E, H.midF (st, lam) m

/-- The honest bits, padding not counted. pad: which positions are padding; row: the prover's choice
of a row for each key (both are arguments). -/
def IsMultP (pad : ℕ → Bool) (row : H.St → (H.J → E) → ℕ → ℕ) : H.St → (H.J → E) → Prop :=
  fun st m =>
    LaidP H.v H.d (H.key st m) (H.tab st) H.pads pad (row st m) ∧
    ∀ u < 2 ^ H.d, ∀ j < 2 ^ H.w, H.bit m u j = hbitP H.v (H.n + 2) pad (row st m) u j

/-- As a row of the read-out: the multiplicities sum to 2^v less the number of padding keys. -/
def numRowF : Row E H.J :=
  ⟨fun i => ∑ u ∈ range (2 ^ H.d), ∑ j ∈ range (H.n + 2), if H.bAt u j = i then (2 : E) ^ j else 0,
    ((2 ^ H.v - padNum H.pads : ℕ) : E)⟩

/-- The lookup's head, as one block. -/
def headA {Ex : ExtSpec} {M Wp Kc : Type} (msg : M → H.J → E)
    (S : PscBk E Ex M Wp Kc) : BkA Kc M H.St (E × (H.tie.lv (H.n + 1)).T.St) Ex Wp :=
  (⟨IOR.draw E Prod.mk Ex,
      Honest.draw E Prod.mk Ex (M × Wp),
      Nums.draw Kc E Prod.mk Ex (2 ^ H.v - 1)⟩ : BkA Kc M H.St (H.St × E) Ex Wp).seq
    ((H.tie.tieA msg S H.n).preM fun x => ((0 : E), x))

end LkHeadF
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The first challenge, for a fixed tuple of messages, with the public factor. -/
def headF_cnt : Prop :=
  ∀ (p : ℕ) [CharP E p] (H : LkHeadF E) (st : H.St) (m : H.J → E),
    H.lkb.Adm p → padsOK H.v H.d H.pads = true →
    cnt (fun lam : E => H.midF (st, lam) m ∧ ¬ H.lkb.inR st m) ≤ 2 ^ H.v - 1

/-- The head. -/
def headF_good : Prop :=
  ∀ (p : ℕ) [CharP E p] (H : LkHeadF E) (Mu : H.St → (H.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (S : PscBk E Ex M Wp Kc) (R0 : Rels Kc H.St Ex (M × Wp))
      (msg : M → H.J → E),
    H.lkb.Adm p → padsOK H.v H.d H.pads = true → H.MuOnF Mu →
    (H.headA msg S).Good (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg (fun x => ((H.tie.lv (H.n + 1)).base x.2).1)
        (fun x m =>
          ((H.RestF ((H.tie.lv (H.n + 1)).base x.2) m ∧ Mu ((H.tie.lv (H.n + 1)).base x.2).1 m) ∧
            H.tie.Done H.n x.2 m) ∧
          H.tie.claim (H.n + 1) x m) fun x m =>
            (H.RestF ((H.tie.lv (H.n + 1)).base x.2) m ∧ H.tie.Done H.n x.2 m) ∧
            H.tie.claim (H.n + 1) x m)

/-- The condition on Mu can be met: the honest bits, padding not counted, meet it. -/
def headF_mu : Prop :=
  ∀ (p : ℕ) (H : LkHeadF E) (pad : ℕ → Bool) (row : H.St → (H.J → E) → ℕ → ℕ),
    H.lkb.Adm p → padsOK H.v H.d H.pads = true → H.MuOnF (H.IsMultP pad row)

/-- The tie's open claim is a claim on the product at the highest position that counts. -/
def headF_open : Prop := ∀ (H : LkHeadF E) x m, H.tie.Q x m (H.n + 1) = H.PT x m (H.n + 1)

/-- `numRowF` holds if and only if `NumKeysP` does. -/
def headF_num : Prop :=
  ∀ (H : LkHeadF E) (m : H.J → E),
    H.numRowF.Holds m ↔ NumKeysP H.v H.d (H.n + 2) (padNum H.pads) (H.bit m)

/-- Errors and numbers of values, with `PscBk.lib`. -/
def headF_ll : Prop :=
  ∀ (H : LkHeadF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E),
    LL (H.headA msg (PscBk.lib E Ex M Wp Kc))
      ([2 ^ H.v - 1] ++ (List.range (H.n + 1)).flatMap fun _ => [1, 3, 0])
      ([Fintype.card E] ++
        (List.range (H.n + 1)).flatMap fun _ => [Fintype.card E, Fintype.card E - 1, 1])

def headF_rounds : Prop :=
  ∀ (H : LkHeadF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E),
    (H.headA msg (PscBk.lib E Ex M Wp Kc)).R.shape.length = 1 + 3 * (H.n + 1)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable (E : Type) [Field E] [Fintype E]

theorem headF_open : Spec.headF_open E := fun H x m =>
  (ldLkpTie_hU E (H.n + 2) (H.PT x m) (by omega)).2.1

theorem headF_cnt : Spec.headF_cnt E := by
  intro p _ H st m hA hP
  by_cases hin : InTable H.v H.d (H.key st m) (H.tab st)
  · exact (le_of_eq (cnt_false fun lam h => h.2 ⟨hin, trivial⟩)).trans (Nat.zero_le _)
  · have h1 : H.n + 2 ≤ 2 ^ H.w := hA.1
    have h2 : 2 ^ H.v < 2 ^ (H.n + 2) := hA.2.1
    have h3 : 2 ^ H.d * (2 ^ (H.n + 2) - 1) < p := hA.2.2
    have hc := cnt_badAl_pad_le E p H.v H.d H.w (H.n + 2) (H.key st m) (H.tab st) H.pads (H.bit m)
      h1 h2 h3 hP hin
    exact (cnt_mono fun lam h => h.1).trans hc

theorem headF_mu : Spec.headF_mu E := by
  intro _ H pad row hA hP st m _ hm lam
  have h1 : H.n + 2 ≤ 2 ^ H.w := hA.1
  have h2 : 2 ^ H.v < 2 ^ (H.n + 2) := hA.2.1
  exact midP_congr H.v H.d H.w (H.n + 2) (H.key st m) (H.tab st) H.pads _ _ lam h1 hm.2
    (honestP E H.v H.d H.w (H.n + 2) (H.key st m) (H.tab st) H.pads pad (row st m) h2 hP hm.1 lam)

theorem headF_num : Spec.headF_num E := by
  intro H m
  have e : ∑ i, H.numRowF.cf i * m i =
      ∑ u ∈ range (2 ^ H.d), ∑ j ∈ range (H.n + 2), (2 : E) ^ j * H.bit m u j := by
    unfold LkHeadF.numRowF
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  unfold Row.Holds NumKeysP
  rw [e]
  exact Iff.rfl

theorem headF_good : Spec.headF_good E := by
  intro p _ H Mu Ex Kc M Wp S R0 msg hA hP hMu
  have g1 : GoodAt (IOR.draw E (Prod.mk : H.St → E → H.St × E) Ex)
      (Honest.draw E Prod.mk Ex (M × Wp)) (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg Prod.fst (fun x m => H.midF x m ∧ Mu x.1 m) H.midF) (fun _ _ _ wp => wp)
      (Nums.draw Kc E Prod.mk Ex (2 ^ H.v - 1)) := by
    refine goodAt_draw Kc M H.St (H.St × E) Ex Wp E Prod.mk _ _ (2 ^ H.v - 1) ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_
    · intro st y w β h
      exact ⟨h.1, hMu st _ h.2.1 h.2.2 β, h.2.2⟩
    · intro st y m _
      refine (cnt_mono fun β hβ => ?_).trans (headF_cnt E p H st (msg m) hA hP)
      obtain ⟨wp, h1, h2⟩ := hβ
      exact ⟨h1.2, fun h => h2 ⟨h1.1, h⟩⟩
  have hstep : H.tie.StepTo H.n := fun st m j hj =>
    (ldLkpTie_hU E (H.n + 2) (H.PT st m) (by omega)).1 (j + 1) (by omega)
  have g2 := tieF_chain E H.tie Ex M Wp Kc S msg
    (cj R0 msg Prod.fst (fun x m => H.RestF x m ∧ Mu x.1 m) H.RestF) H.n hstep
  unfold BkA.Good at g2 ⊢
  rw [tieFR_cj E H.tie Ex Kc H.St M Wp R0 msg Prod.fst
      (fun x m => H.RestF x m ∧ Mu x.1 m) H.RestF H.n] at g2
  have hq : ∀ (x : H.St × E) (m : H.J → E),
      H.tie.Q x m 1 ^ 2 * H.PT x m 0 =
        ∏ j ∈ range (H.n + 2), tabProd H.d (H.tab x.1) (H.bit m) x.2 j ^ 2 ^ j :=
    fun x m =>
      ((ldLkpTie_hU E (H.n + 2) (H.PT x m) (by omega)).1 0 (by omega)).symm.trans
        (ldLkpTie_hU E (H.n + 2) (H.PT x m) (by omega)).2.2
  have g3 := goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _
    (cj R0 msg Prod.fst (fun x m => H.midF x m ∧ Mu x.1 m) H.midF) _ _ _ _
    (fun x : H.St × E => ((0 : E), x)) ?_ ?_ ?_ ?_ g2
  · exact goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ _ _ _ (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ g1 g3 fun _ _ _ _ _ _ _ => rfl
  · intro x y w h
    obtain ⟨hR, ⟨hb, hn, hid⟩, hm⟩ := h
    refine ⟨⟨hR, ⟨hb, hn⟩, hm⟩, ?_⟩
    show keyProd H.v (H.key x.1 (msg w.1)) x.2 -
        H.fac x * (H.tie.Q x (msg w.1) 1 ^ 2 * H.PT x (msg w.1) 0) = 0
    rw [hq]
    exact sub_eq_zero.mpr hid
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro x y w _ h
    obtain ⟨⟨hR, hb, hn⟩, hc⟩ := h
    have hc' : keyProd H.v (H.key x.1 (msg w.1)) x.2 -
        H.fac x * (H.tie.Q x (msg w.1) 1 ^ 2 * H.PT x (msg w.1) 0) = 0 := hc
    rw [hq] at hc'
    exact ⟨hR, hb, hn, sub_eq_zero.mp hc'⟩

theorem headF_ll : Spec.headF_ll E := fun H Ex M Wp Kc msg =>
  ll_seq (ll_draw Ex Wp E Prod.mk (2 ^ H.v - 1))
    (ll_preM (tieF_ll E H.tie Ex M Wp Kc msg H.n) fun x => ((0 : E), x))

theorem headF_rounds : Spec.headF_rounds E := by
  intro H Ex M Wp Kc msg
  have e : (H.headA msg (PscBk.lib E Ex M Wp Kc)).R.shape =
      (IOR.draw E (Prod.mk : H.St → E → H.St × E) Ex).shape ++
        (H.tie.tieA msg (PscBk.lib E Ex M Wp Kc) H.n).R.shape := rfl
  rw [e, List.length_append, tieF_rounds E H.tie Ex M Wp Kc msg H.n]
  rfl

end
end Cb
