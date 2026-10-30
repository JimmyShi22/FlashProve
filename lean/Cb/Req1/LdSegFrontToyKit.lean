-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontToyKit.lean: the named conditions of a segment's front
(Cb/Req1/LdSegFrontRef.lean), from plain ones.

Statements and proofs, for any data; used by the toy of Cb/GlVal/GlJ3SegFrontToy.lean. Glue; no
protocol.

Main names:
  `pre_muFrom`: `F.OK`'s clause `muFrom` (F : `LdPreD`, Cb/Req1/LdSegRefLkpPre.lean) "what rides
    along on the honest side gives the lookup's exact clause at every shift"
    (`F.Rr.rel x.1 y w → F.PS.outC x w.1 → F.Mu x (F.msg w.1)`): under hv, hd (the numbers fit),
    from multiplicities that are valid function by function (h; Cb/Ld/LdLkpMult.lean:
    `ldLkpMult_shift`), for Mu := "the bits write a valid vector" of the lookup that runs (hMu:
    `F.Mu = F.A.ValidMu`).
  `pre_zkOK`: for the same Mu (hMu): `F.ZkOK` (Cb/Req1/LdSegRefLkpPreZk.lean), with the lookup's
    exact claim as the claim with which the item is started: from `F.OK`, the four plain conditions
    on places (Cb/Ld/LdLkpMaskPlaces2.lean), and: the reading keeps what the lookup reads.
  `bit_ownOur`, `end_ownOur`: the conditions on own places (Cb/Ld/LdPscZk.lean: `OwnOur`) of the
    sumchecks of the bit test (Cb/Ld/LdLkpBit.lean) and of the closing (Cb/Ld/LdLkpEnd.lean), from:
    own places pairwise apart, in Rd, apart from the table's places; the table's places in Rd; the
    incoming form 0 outside Rd and at the own places.
  `end_takes`: see its docstring (the closing: Cb/Ld/LdLkpEnd.lean; target: the value + 1).
  `psc_quiet`: overwriting the own masks of a sumcheck whose reading keeps Rd changes no entry of
    Rd', if Rd' lies in Rd and holds none of its own places. It is stated for an earlier block that
    reads the same vector of entries (one type J, one msg), and a later block whose reading keeps
    what the earlier one reads. (A sufficient condition.)
  `psc_not_quiet`: the other way, for own places that are pairwise different (hi): if two witnesses
    agree on all entries that the later sumcheck's reading keeps, and differ at an entry of Rd',
    then its fact is not quiet for Rd' (in this sense: `¬ ldQuiet ..`,
    Cb/Req1/LdSegFrontTabZk.lean). So an entry that an earlier block reads, and that can vary
    while the kept entries stay, must be kept by the later block's reading: places that are pairwise
    different do not suffice.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefLkpPreZk
import Cb.Ld.LdLkpToyMask
import Cb.Ld.LdLkpMultProofs
import Cb.Req1.LdSegFrontRef
import Cb.Ld.LdLkpEndProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section Pre
variable {E Kc : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp : Type} (F : LdPreD E Kc S E₀ Wp)

theorem pre_muFrom (hMu : F.Mu = F.A.ValidMu)
    (hv : F.P.g + F.P.v = F.A0.v' + 1) (hd : F.P.g + F.P.d = F.A0.d)
    (h : ∀ st y w, F.Rr.rel st y w →
      ∀ f < 2 ^ F.P.g,
        Valid F.P.v F.P.d F.A0.w (F.A0.n + 1) (F.P.key st (F.msg w.1) f) (F.P.tab st f)
          fun u j => F.msg w.1 (F.A0.bAt (f * 2 ^ F.P.d + u) j)) :
    ∀ (x : F.St × E) y w, F.Rr.rel x.1 y w → F.PS.outC x w.1 → F.Mu x (F.msg w.1) := by
  intro x y w hr _
  rw [hMu]
  have h1 := ldLkpMult_shift E F.P.g F.P.v F.P.d F.A0.w (F.A0.n + 1)
    (F.P.key x.1 (F.msg w.1)) (F.P.tab x.1) F.P.tag
    (fun f u j => F.msg w.1 (F.A0.bAt (f * 2 ^ F.P.d + u) j)) (h x.1 y w hr) x.2
  have e : shBit F.P.d (fun f u j => F.msg w.1 (F.A0.bAt (f * 2 ^ F.P.d + u) j)) =
      fun u j => F.msg w.1 (F.A0.bAt u j) := by
    funext u j
    show F.msg w.1 (F.A0.bAt (u / 2 ^ F.P.d * 2 ^ F.P.d + u % 2 ^ F.P.d) j) = _
    rw [Nat.div_add_mod']
  rw [e, hv, hd] at h1
  exact h1

theorem pre_zkOK (p : ℕ) (Dt Rd : F.A0.J → Prop) (hMu : F.Mu = F.A.ValidMu) (hOK : F.OK p)
    (hP : F.A.PlacesOK Dt) (hRd : ∀ j, F.A.srAll Dt j → Rd j) :
    F.ZkOK p Dt Rd (F.A.lk.inP F.Mu) where
  ok := hOK
  places := ldLkpPlaces2_ok E F.A Dt hP
  inRd := hRd
  gives := fun _ _ h => h
  stable := by rw [hMu]; exact ldLkpMask_claim_stab E F.A Dt hP
  reads := fun k k' st hk hc => by
    rw [hMu] at hc ⊢
    exact ldLkpMask_claim_reads E F.A Dt hP st k k' (fun j hj => hk j (Or.inl hj)) hc
  from' := fun st m hc => by
    rw [hMu] at hc ⊢
    exact ldLkpMask_claim_reads
      E F.A Dt hP st m _ (fun j hj => (mjCut_of m (hRd j (Or.inl hj))).symm) hc

end Pre

section Own
variable {E : Type} [Field E] [Fintype E]

theorem bit_ownOur (B : LkBit E) (Rd : B.J → Prop)
    (hi : Function.Injective (Sum.elim B.wAt fun _ : Unit => B.cAt))
    (ho : ∀ i, Rd (Sum.elim B.wAt (fun _ : Unit => B.cAt) i)) (ht : ∀ b, Rd (B.tAt b))
    (ha : ∀ b i, B.tAt b ≠ Sum.elim B.wAt (fun _ : Unit => B.cAt) i) : B.zc.next.OwnOur Rd := by
  refine ⟨hi, ho, fun st m m' hm => ?_, fun _ _ _ _ => funext fun b => b.elim, fun _ _ _ => rfl,
    fun st m m' hm => ?_, fun _ _ _ _ => funext fun b => b.elim, fun _ _ => rfl⟩
  · funext a X
    show Alg.mle (fun b => m (B.tAt b)) _ = Alg.mle (fun b => m' (B.tAt b)) _
    rw [funext fun b => hm (B.tAt b) (ht b)]
  · funext a X
    show Alg.mle (fun b => m (B.tAt b)) _ = Alg.mle (fun b => m' (B.tAt b)) _
    rw [funext fun b => hm (B.tAt b) (ha b)]

theorem end_ownOur (B : LkEnd E) (Rd : B.J → Prop)
    (hi : Function.Injective (Sum.elim B.wAt fun _ : Unit => B.cAt))
    (ho : ∀ i, Rd (Sum.elim B.wAt (fun _ : Unit => B.cAt) i)) (ht : ∀ b, Rd (B.tAt b))
    (ha : ∀ b i, B.tAt b ≠ Sum.elim B.wAt (fun _ : Unit => B.cAt) i)
    (hs : ∀ s j, ¬ Rd j → B.inc s j = 0)
    (hso : ∀ s i, B.inc s (Sum.elim B.wAt (fun _ : Unit => B.cAt) i) = 0) : B.psc.OwnOur Rd := by
  refine ⟨hi, ho, fun st m m' hm => ?_, fun _ _ _ _ => funext fun b => b.elim, hs,
    fun st m m' hm => ?_, fun _ _ _ _ => funext fun b => b.elim, hso⟩
  · funext a X
    show Alg.mle (fun b => m (B.tAt b)) _ = Alg.mle (fun b => m' (B.tAt b)) _
    rw [funext fun b => hm (B.tAt b) (ht b)]
  · funext a X
    show Alg.mle (fun b => m (B.tAt b)) _ = Alg.mle (fun b => m' (B.tAt b)) _
    rw [funext fun b => hm (B.tAt b) (ha b)]

/-- A row "extension of the table at a point, plus a challenge at one mask, is a value" is the input
claim of a closing with the public vector 1, that point, and the incoming form "the challenge at
that mask". -/
theorem end_takes (B : LkEnd E) (o : B.X) (m : B.J → E) (c : B.J) (β v : E)
    (hcp : ∀ b, B.cp o b = 1) (h1 : B.inc o c = β) (h2 : ∀ j, j ≠ c → B.inc o j = 0) :
    B.psc.SumHolds (v + 1, o) m ↔ Alg.mle (fun b => m (B.tAt b)) (B.z o) + m c * β = v := by
  classical
  refine ((ldLkpEnd_sum E B (v + 1, o) m).trans (ldLkpEnd_less E B (v + 1, o) m)).trans ?_
  have e1 : (fun b => B.cp o b * m (B.tAt b)) = fun b => m (B.tAt b) :=
    funext fun b => by rw [hcp, one_mul]
  have e2 : ∑ j, B.inc o j * m j = m c * β := by
    rw [Finset.sum_eq_single c (fun j _ hj => by rw [h2 j hj, zero_mul]) fun h =>
          absurd (Finset.mem_univ c) h,
      h1, mul_comm]
  show Alg.mle (fun b => B.cp o b * m (B.tAt b)) (B.z o) + ∑ j, B.inc o j * m j = v + 1 - 1 ↔ _
  rw [e1, e2, add_sub_cancel_right]

/-- A later sumcheck's masks, and what an earlier block reads. -/
theorem psc_quiet (Kc : Type) (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd Rd' : T.J → Prop)
    (h1 : ∀ j, Rd' j → Rd j) (h2 : ∀ j, Rd' j → ∀ i, j ≠ Sum.elim T.wAt T.cAt i) :
    ldQuiet S (frFact Kc T S E₀ Wp A0 msg Rd) msg Rd' := by
  classical
  intro w w' M hw j hj
  have e : (T.own Rd).cut (msg (S.msgs w'.1)) j =
      (T.own Rd).put M ((T.own Rd).cut (msg (S.msgs w.1))) j := congrFun hw j
  have e1 : ∀ m : T.J → E, (T.own Rd).cut m j = m j := fun m => if_pos (h1 j hj)
  rw [e1, PscPar.put_off M _ j fun i hi => h2 j hj i hi, e1] at e
  exact e

/-- Under the hypotheses below, a reading that forgets what an earlier block reads is not quiet for
it. -/
theorem psc_not_quiet (Kc : Type) (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd Rd' : T.J → Prop)
    (hi : Function.Injective (Sum.elim T.wAt T.cAt)) (j0 : T.J) (h0 : Rd' j0) (w w' : S.Wit × Wp)
    (hs : ∀ j, Rd j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j)
    (hne : msg (S.msgs w'.1) j0 ≠ msg (S.msgs w.1) j0) :
    ¬ ldQuiet S (frFact Kc T S E₀ Wp A0 msg Rd) msg Rd' := by
  classical
  intro hq
  refine hne
    (hq w w' (fun i => (T.own Rd).cut (msg (S.msgs w.1)) (T.wAt i),
        fun a => (T.own Rd).cut (msg (S.msgs w.1)) (T.cAt a))
      ?_ j0 h0)
  show (T.own Rd).cut (msg (S.msgs w'.1)) =
    Function.extend (Sum.elim T.wAt T.cAt)
      (Sum.elim (fun i => (T.own Rd).cut (msg (S.msgs w.1)) (T.wAt i)) fun a =>
        (T.own Rd).cut (msg (S.msgs w.1)) (T.cAt a))
      ((T.own Rd).cut (msg (S.msgs w.1)))
  have e1 : (T.own Rd).cut (msg (S.msgs w'.1)) =
      (T.own Rd).cut (msg (S.msgs w.1)) := funext fun j => by
    by_cases h : Rd j
    · exact (if_pos h).trans ((hs j h).trans (if_pos h).symm)
    · exact (if_neg h).trans (if_neg h).symm
  rw [e1]
  funext j
  by_cases h : ∃ i, Sum.elim T.wAt T.cAt i = j
  · obtain ⟨i, rfl⟩ := h
    rw [hi.extend_apply]
    rcases i with i | a <;> rfl
  · rw [Function.extend_apply' _ _ _ h]

end Own
end Cb
