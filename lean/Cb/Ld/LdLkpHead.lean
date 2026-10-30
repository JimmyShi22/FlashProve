-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpHead.lean: the first part of the lookup argument as one reduction: the verifier's first
challenge λ, then sumchecks that tie the two sides of the resulting product identity.

Definitions, statements (in `Cb.Spec`) and proofs. Nothing is assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). The claim after λ has an identity between the product of λ - key over the keys
and the product, over the n + 1 bit positions j that count, of (the product over the table at
j)^(2^j). The library calls this part the lookup's head, a block at the base (at the base: between
joints in which the tuple of messages is a part of the witness, before the lift over a signature,
Cb/Ld/LdSigLift.lean), and its sumchecks the tie.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).
Parts: Cb/Ld/LdLkpKit.lean (`cj`; λ at the base is proved here anew, for Mu, by `goodAt_draw`,
Cb/Ld/LdBattKit.lean), Cb/Ld/LdLkpTie*.lean (the chain of sumchecks without variable: no variable
but a dummy one; three rounds each), Cb/Ld/LdLkpTieRows.lean, Cb/Ld/LdSigStep.lean (a step without
rounds).

Main names:
  `LkHead`: the data: states St, entries J; 2^v keys, any function of state and entries; a table of
    2^d entries, read off the state; 2^w bit positions of which the first n + 1 count; `bAt`: where
    the bit (table entry u, position j) is among the entries; the places of the tie's own masks.
  `H.tie`: the tie's data: PK = the product of λ - key; PT_j = the product over the table at the bit
    position j; Q_j by square-and-multiply (`Cb.Lkp.hU`).
  `H.Idle`: the idle positions: for n + 1 ≤ j < 2^w the product PT_j is 1. A choice of this library:
    the honest bits are 0 there; the claim is added after λ, rides along, and is used where the
    roots of the table's forest (`LkInst.DT`, Cb/Ld/LdLkpInst.lean) get their point. (A write-up
    of ours (lean/CREDITS.md) says nothing on these positions.)
  `H.Rest`: all are bits; the multiplicities sum to the number of keys; `H.Idle`.
  `H.MuOK Mu`: "the vector is the multiplicities" is a parameter Mu of the honest side, with one
    condition: for keys in the table it gives the claim after λ at every λ, and idle positions
    (`H.Idle`, at every λ as well).
    `ldLkpHead_muOK`: under `H.lkb.Adm p`, the bits of "the number of keys equal to this entry and
    to no earlier one" meet it. (A table with repeated entries, a joint table after a random shift,
    has other honest vectors: any that meets the condition will do.)
  `H.headA`: the block: λ | (no round: target 0) | the steps 0, .., n of the tie.
  `ldLkpHead_good`: under the conditions below, `H.headA` is `BkA.Good`, that is `GoodAt`, from one
    joint to another, for any joint R0. Both joints are made by `cj` (Cb/Ld/LdLkpKit.lean) from R0,
    which rides along, and from two claims on the entries: one for the honest relation, one for the
    relaxed relation. The two claims differ in Mu ("the vector is the multiplicities") alone: it
    stands in the honest relation only. The input joint: every key is an entry of the table; honest:
    and Mu. The output joint: `H.Rest` at (state, λ); all that the tie has done (`TieP.Done`: its
    rows; the masked claims on PK and on PT_j, j < n); the tie's open claim, the masked claim on
    Q_n; honest: and Mu. Conditions: the numbers (`LkB.Adm`: n + 1 ≤ 2^w, 2^v < 2^(n+1), 2^d
    (2^(n+1) - 1) < p, p the characteristic), and `H.MuOK Mu`.
  `ldLkpHead_open`: Q_n is PT_n. `ldLkpHead_rounds`: 1 + 3 (n + 1) rounds.

Limits: this file says nothing on zero knowledge.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpTieRows
import Cb.Ld.LdLkpTieProofs
import Cb.Ld.LdLkpTieQ
import Cb.Ld.LdSigStep

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

noncomputable section

/-- The data of the lookup's head. -/
structure LkHead (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  v : ℕ
  d : ℕ
  w : ℕ
  n : ℕ
  key : St → (J → E) → ℕ → E
  tab : St → ℕ → E
  bAt : ℕ → ℕ → J
  wS  : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) → J
  cS  : Bool → J
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cAt : ℕ → Bool → J

attribute [instance] LkHead.finJ

namespace LkHead
variable {E : Type} [Field E] [Fintype E] (H : LkHead E)

def bit (m : H.J → E) : ℕ → ℕ → E := fun u j => m (H.bAt u j)

/-- the lookup claim, on entries -/
def lkb : LkB E H.St (H.J → E) H.J :=
  ⟨⟨H.v, H.d, H.key, H.tab, fun _ _ => True⟩, H.w, H.n + 1, H.bit, id⟩

def PT (x : H.St × E) (m : H.J → E) (j : ℕ) : E := tabProd H.d (H.tab x.1) (H.bit m) x.2 j

/-- The tie's data. -/
def tie : TieP E where
  St0 := H.St × E
  J := H.J
  PK := fun x m => keyProd H.v (H.key x.1 m) x.2
  PT := H.PT
  Q := fun x m j => Lkp.hU (H.n + 1) (H.PT x m) j
  wS := H.wS
  cS := H.cS
  wAt := H.wAt
  cAt := H.cAt

/-- The idle positions. -/
def Idle (x : H.St × E) (m : H.J → E) : Prop := ∀ j, H.n + 1 ≤ j → j < 2 ^ H.w → H.PT x m j = 1

/-- What waits after λ beside the identity. -/
def Rest (x : H.St × E) (m : H.J → E) : Prop :=
  Bits H.d H.w (H.bit m) ∧ NumKeys H.v H.d (H.n + 1) (H.bit m) ∧ H.Idle x m

/-- What is asked of "the vector is the multiplicities": with it, for keys in the table, the claim
after λ holds at every λ, and the idle positions are idle. -/
def MuOK (Mu : H.St → (H.J → E) → Prop) : Prop :=
  ∀ st m, H.lkb.inR st m → Mu st m → ∀ lam : E, H.lkb.mid (st, lam) m ∧ H.Idle (st, lam) m

/-- The lookup's head, as one block. -/
def headA (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E) :
    BkA Kc M H.St (E × (H.tie.lv (H.n + 1)).T.St) Ex Wp :=
  (⟨IOR.draw E Prod.mk Ex,
      Honest.draw E Prod.mk Ex (M × Wp),
      Nums.draw Kc E Prod.mk Ex (2 ^ H.v - 1)⟩ : BkA Kc M H.St (H.St × E) Ex Wp).seq
    ⟨(H.tie.tieA Ex Wp Kc msg H.n).R.pre (fun x => some ((0 : E), x)) (ExtMap.id Ex),
      (H.tie.tieA Ex Wp Kc msg H.n).H.pre (fun x => some ((0 : E), x))
        (ExtMap.id Ex) fun o => (((0 : E), o.1), o.2),
      (H.tie.tieA Ex Wp Kc msg H.n).P.pre (fun x => some ((0 : E), x)) (ExtMap.id Ex)⟩

end LkHead
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The head. -/
def ldLkpHead_good : Prop :=
  ∀ (p : ℕ) [CharP E p] (H : LkHead E) (Mu : H.St → (H.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (R0 : Rels Kc H.St Ex (M × Wp)) (msg : M → H.J → E),
    H.lkb.Adm p → H.MuOK Mu →
    (H.headA Ex M Wp Kc msg).Good (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg (fun x => ((H.tie.lv (H.n + 1)).base x.2).1)
        (fun x m =>
          ((H.Rest ((H.tie.lv (H.n + 1)).base x.2) m ∧ Mu ((H.tie.lv (H.n + 1)).base x.2).1 m) ∧
            H.tie.Done H.n x.2 m) ∧
          H.tie.claim (H.n + 1) x m) fun x m =>
            (H.Rest ((H.tie.lv (H.n + 1)).base x.2) m ∧ H.tie.Done H.n x.2 m) ∧
            H.tie.claim (H.n + 1) x m)

/-- Under `H.lkb.Adm p`, the honest bits (first-occurrence rule) meet the condition. -/
def ldLkpHead_muOK : Prop := ∀ (p : ℕ) (H : LkHead E), H.lkb.Adm p → H.MuOK H.lkb.IsMult

/-- The tie's open claim is a claim on the product at the highest position that counts. -/
def ldLkpHead_open : Prop := ∀ (H : LkHead E) x m, H.tie.Q x m H.n = H.PT x m H.n

def ldLkpHead_rounds : Prop :=
  ∀ (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E),
    (H.headA Ex M Wp Kc msg).R.shape.length = 1 + 3 * (H.n + 1)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable (E : Type) [Field E] [Fintype E]

/-- For the honest bits (`IsMult`) the idle positions are idle. -/
theorem LdLkp.LkHead.idle_of_isMult
    (H : LkHead E) (x : H.St × E) (m : H.J → E) (h : H.lkb.IsMult x.1 m) : H.Idle x m := by
  intro j hj hjw
  unfold LkHead.PT tabProd
  refine Finset.prod_eq_one fun u hu => ?_
  have hb : H.bit m u j = hbit H.v (H.n + 1) (H.key x.1 m) (H.tab x.1) u j :=
    h u (mem_range.mp hu) j hjw
  have h0 : hbit H.v (H.n + 1) (H.key x.1 m) (H.tab x.1) u j = 0 :=
    if_neg fun hc => absurd hc.1 (Nat.not_lt.mpr hj)
  rw [hb, h0, zero_mul, add_zero]

theorem ldLkpHead_open : Spec.ldLkpHead_open E := fun H x m =>
  (ldLkpTie_hU E (H.n + 1) (H.PT x m) (Nat.succ_pos _)).2.1

theorem ldLkpHead_muOK : Spec.ldLkpHead_muOK E := fun p H hA st m hin hm lam =>
  ⟨(ldLkp_lambda_fwd E H.St (H.J → E) H.J H.lkb p st m lam hA ⟨hin, hm⟩).1,
    H.idle_of_isMult E (st, lam) m hm⟩

theorem ldLkpHead_good : Spec.ldLkpHead_good E := by
  intro p _ H Mu Ex Kc M Wp R0 msg hA hMu
  have g1 : GoodAt (IOR.draw E (Prod.mk : H.St → E → H.St × E) Ex)
      (Honest.draw E Prod.mk Ex (M × Wp)) (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg Prod.fst (fun x m => (H.lkb.mid x m ∧ H.Idle x m) ∧ Mu x.1 m) H.lkb.mid)
      (fun _ _ _ wp => wp) (Nums.draw Kc E Prod.mk Ex (2 ^ H.v - 1)) := by
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
    (cj R0 msg Prod.fst (fun x m => H.Rest x m ∧ Mu x.1 m) H.Rest) H.n hstep
  unfold BkA.Good at g2 ⊢
  rw [ldLkpTieR_cj E H.tie Ex Kc H.St M Wp R0 msg Prod.fst
      (fun x m => H.Rest x m ∧ Mu x.1 m) H.Rest H.n] at g2
  have hq : ∀ (x : H.St × E) (m : H.J → E),
      H.tie.Q x m 0 = ∏ j ∈ range (H.n + 1), tabProd H.d (H.tab x.1) (H.bit m) x.2 j ^ 2 ^ j :=
    fun x m => (ldLkpTie_hU E (H.n + 1) (H.PT x m) (Nat.succ_pos _)).2.2
  have g3 := goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _
    (cj R0 msg Prod.fst (fun x m => (H.lkb.mid x m ∧ H.Idle x m) ∧ Mu x.1 m) H.lkb.mid) _ _ _ _
    (fun x : H.St × E => ((0 : E), x)) ?_ ?_ ?_ ?_ g2
  · exact goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ _ _ _ (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ g1 g3 fun _ _ _ _ _ _ _ => rfl
  · intro x y w h
    obtain ⟨hR, ⟨⟨⟨hb, hn, hid⟩, _⟩, hidle⟩, hm⟩ := h
    refine ⟨⟨hR, ⟨hb, hn, hidle⟩, hm⟩, ?_⟩
    show keyProd H.v (H.key x.1 (msg w.1)) x.2 - H.tie.Q x (msg w.1) 0 = 0
    rw [hq]
    exact sub_eq_zero.mpr hid
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro x y w _ h
    obtain ⟨⟨hR, hb, hn, _⟩, hc⟩ := h
    have hc' : keyProd H.v (H.key x.1 (msg w.1)) x.2 - H.tie.Q x (msg w.1) 0 = 0 := hc
    rw [hq] at hc'
    exact ⟨hR, ⟨hb, hn, sub_eq_zero.mp hc'⟩, trivial⟩

theorem ldLkpHead_rounds : Spec.ldLkpHead_rounds E := by
  intro H Ex M Wp Kc msg
  have e : (H.headA Ex M Wp Kc msg).R.shape =
      (IOR.draw E (Prod.mk : H.St → E → H.St × E) Ex).shape ++
        (H.tie.tieA Ex Wp Kc msg H.n).R.shape := rfl
  rw [e, List.length_append, ldLkpTie_rounds E H.tie Ex M Wp Kc msg H.n]
  rfl

end
end Cb
