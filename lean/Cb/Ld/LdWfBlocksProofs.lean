-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfBlocksProofs.lean: the proofs of the statements of Cb/Ld/LdWfBlocks.lean (the lookup
arguments inside the sub-protocol for the claim that the encoded index is well-formed, each defined
as the assembled lookup on the keys of the index).
The lookups meant are those of the preamble of weights-formedness, as values.

Between the theorems there is glue: claims that read keys only below 2^v (`inTable_congr`,
`holds_congr`); the places lie among the messages' entries (`Lks.places`); what rides along past the
lookup of a forest (`rideL`); `LdLkp.LkAsm2.supp_formK` and `LdLkp.getD_pull` (see their
docstrings).

Limits: what the head of Cb/Ld/LdWfBlocks.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfBlocks
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdBldWfSuppProofs
import Cb.Ld.LdWfProofsRel
import Cb.Req.ReqSumCubeProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldWfB_key : Spec.ldWfB_key E := by
  intro C P hL f hf U b hb
  have h := hL.keyLin f hf U (P.cz (P.v f) b)
  have e : Blocks.ext (P.v f) (P.key f U) (P.cz (P.v f) b) = P.key f U b := by
    show Blocks.ext (P.v f) (P.key f U) (Blocks.nat (Alg.corner (Alg.bits (P.v f) b))) = _
    rw [Cb.Req.ext_nat E (P.v f) (P.key f U) (Alg.corner (Alg.bits (P.v f) b)),
      Alg.mle_corner, Alg.num_bits hb]
  rw [← e]
  exact h

end

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

omit [Field E] [Fintype E] in
/-- Glue: "in the table" and a masked claim (`holds_congr`, the next theorem) read the keys below
2^v only. -/
theorem inTable_congr {v d : ℕ} {k k' t : ℕ → E} (h : ∀ b < 2 ^ v, k b = k' b) :
    Lkp.InTable v d k t ↔ Lkp.InTable v d k' t :=
  ⟨fun H b hb => by rw [← h b hb]; exact H b hb, fun H b hb => by rw [h b hb]; exact H b hb⟩

omit [Fintype E] in
theorem holds_congr {N : Type} [Fintype N] (c : MCl E N) {v : ℕ} {k k' : ℕ → E}
    (h : ∀ b < 2 ^ v, k b = k' b) (μ : N → E) :
    c.Holds v k μ ↔ c.Holds v k' μ := by
  unfold MCl.Holds
  rw [Blocks.ext_congr h]

/-- Glue: what rides along past the lookup of forest l, on tuples (message of the index, messages).
-/
def rideL (P : LdWfP E C) (l : ℕ) : Rels Unit P.WSt C.E0 ((C.Msg × P.S.Msg) × Unit) where
  rel  := fun st _ w =>
    (P.Done l st w.1.1 w.1.2 ∧ ∀ f, l < f → f ≤ P.n → P.InT f w.1.1) ∧
    ∀ f, l < f → f ≤ P.n → P.mult f w.1.1 (P.body w.1.2)
  relR := fun a w => P.Done l a.1 w.1.1 w.1.2 ∧ ∀ f, l < f → f ≤ P.n → P.InT f w.1.1
  on   := fun _ => True
  core := fun _ => ()

theorem Lks.places (K : P.Lks) (f : ℕ) :
    (K.asm f).PlacesIn fun j => j ∈ Set.range (Sum.inr : P.N → P.bt.J) :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end LdWfP

section
variable (E : Type) [Field E] [Fintype E]
open LdWfP

theorem ldWfB_lkp : Spec.ldWfB_lkp E := by
  intro p _ C P K hL hK l hl
  have hv := hK.v l hl
  have g := ldLkpAsm2N_idx E p (K.asm l) P.N Sum.inr (K.asm l).ValidMu C P.S
    (fun st : P.WSt => st.1) (P.rideL l) P.msg Sum.inr_injective (K.places l) (hK.adm l hl)
    (ldLkpAsm2_muValid E (K.asm l) (hK.adm l hl).1)
  -- the keys of the assembled lookup at a tuple are the keys of the forest
  have hkey : ∀ (st : P.WSt) (U : C.Msg) (m : P.S.Msg) (b : ℕ),
      b < 2 ^ P.v l → P.key l U b = (K.asm l).key st (P.msg (U, m)) b :=
    fun st U m b hb => ldWfB_key E C P hL l hl U b hb
  have hin : ∀ (st : P.WSt) (U : C.Msg) (m : P.S.Msg),
      P.InT l U ↔
      Lkp.InTable (K.v' l + 1) (P.d l)
        ((K.asm l).key st (P.msg (U, m))) (P.tab l) := fun st U m => by
    rw [← hv]
    exact inTable_congr (hkey st U m)
  have hcl : ∀ (c : MCl E P.N) (st : P.WSt) (U : C.Msg) (m : P.S.Msg),
      c.Holds (P.v l) (P.key l U) (P.ent m) ↔
      c.Holds (K.v' l + 1) ((K.asm l).key st (P.msg (U, m))) (P.ent m) := fun c st U m => by
    rw [← hv]
    exact holds_congr c (hkey st U m) _
  refine goodB_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (goodB_conseq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl)
      ⟨Err.le_refl _, le_refl _, le_refl _, fun _ _ h => h, fun _ => rfl⟩)
  · -- exact input
    rintro x y w ⟨hE, hAns, ⟨⟨hT, hMore⟩, hMu⟩, hEnc, hLater⟩
    have hd := dcd_of_enc hL hEnc
    have hMore' := (via_enc hL hEnc _).1 hMore
    have hMu' := (via_enc hL hEnc _).1 hMu
    have hLater' := (via_enc hL hEnc _).1 hLater
    have hT' : Lkp.InTable (P.v l) (P.d l) (P.keyAt l x.1 (y.1, P.S.msgs w.1)) (P.tab l) := hT
    rw [keyAt_eq l (ym := (y.1, P.S.msgs w.1)) hd] at hT'
    exact ⟨hE, hAns, hEnc, ⟨hMore', hLater'⟩,
      ⟨(hin x.1 _ _).1 hT', trivial⟩, hK.mult l hl x.1 _ _ hMu'⟩
  · -- exact output
    rintro x y w ⟨hE, hAns, hEnc, ⟨hMore, hLater⟩, hc, hr, _⟩
    have hd := dcd_of_enc hL hEnc
    refine ⟨hE, hAns, ⟨?_, hr, (via_enc hL hEnc _).2 hMore⟩, hEnc, (via_enc hL hEnc _).2 hLater⟩
    show x.1.2.1.Holds (P.v l) (P.keyAt l x.1.1 (y.1, P.S.msgs w.1)) (P.ent (P.S.msgs w.1))
    rw [keyAt_eq l (ym := (y.1, P.S.msgs w.1)) hd]
    exact (hcl _ x.1.1 _ _).2 hc
  · exact fun a h => ⟨h.1, h.2, trivial⟩
  · exact fun b h => ⟨h.1, h.2.1⟩
  · -- relaxed input
    rintro a w _ ⟨hdec, U, hU, hMore, hT, _⟩
    refine ⟨hdec, ?_, U, hU, hMore⟩
    show Lkp.InTable (P.v l) (P.d l) (P.keyAt l a.1.1 (a.2.1, P.S.msgs w.1)) (P.tab l)
    rw [keyAt_eq l (ym := (a.2.1, P.S.msgs w.1)) hU]
    exact (hin a.1.1 U _).2 hT
  · -- relaxed output
    rintro b w ⟨hdec, hc, hr, U, hU, hMore⟩
    refine ⟨hdec, U, hU, hMore, ?_, hr, trivial⟩
    have hc' : b.1.1.2.1.Holds (P.v l)
        (P.keyAt l b.1.1.1 (b.2.1, P.S.msgs w.1)) (P.ent (P.S.msgs w.1)) := hc
    rw [keyAt_eq l (ym := (b.2.1, P.S.msgs w.1)) hU] at hc'
    exact (hcl _ b.1.1.1 U _).1 hc'

theorem ldWfB_idx : Spec.ldWfB_idx E := fun C P K l =>
  ldLkpAsm2N_idxStep E (K.asm l) P.N Sum.inr C P.S P.msg
theorem ldWfB_passes : Spec.ldWfB_passes E := fun C P K l =>
  ldLkpAsm2N_passes E (K.asm l) P.N Sum.inr C P.S P.msg
theorem ldWfB_len : Spec.ldWfB_len E := by
  intro p C P K hK l hl x y τ x' h
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [hK.rows l hl]
  exact ldLkpAsm2N_len E (K.asm l) P.N Sum.inr C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg _ _ _ _ hxo

/-- Glue: the mask form of the claim on the keys reads the two inner masks of the last level of the
keys' tree, and nothing else. -/
theorem LdLkp.LkAsm2.supp_formK
    (A : LkAsm2 E) (G : A.J → Prop) (hG : ∀ b, G (A.cK A.v' b)) (o : A.XB) :
    SuppIn G (A.rd o).2.1.mf := by
  classical
  intro j hj
  show - pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS (A.oldT o).2) j = 0
  refine neg_eq_zero.2 (supp_pushJ _ _ G (fun j' hj' => ?_) j hj)
  have hc : ∀ b,
      ((A.IK.setV (A.v' + 1)).DK.lv A.v').toJ
          (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.cAt (((A.IK.setV (A.v' + 1)).DK.lv A.v').two b)) =
        A.cK A.v' b := fun b => by
    cases A.v' <;> rfl
  show ((A.IK.setV (A.v' + 1)).DK.lv A.v').T.lst (A.oldT o).2.1.st
        (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.par.hp (A.oldT o).2.1.st (A.oldT o).2.1.pt) *
      ((if j' = ((A.IK.setV (A.v' + 1)).DK.lv A.v').toJ
                (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.cAt
                  (((A.IK.setV (A.v' + 1)).DK.lv A.v').two false)) then
            1 - (A.oldT o).2.2
          else 0) +
        if j' = ((A.IK.setV (A.v' + 1)).DK.lv A.v').toJ
              (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.cAt
                (((A.IK.setV (A.v' + 1)).DK.lv A.v').two true)) then (A.oldT o).2.2
        else 0) = 0
  have h1 : j' ≠
      ((A.IK.setV (A.v' + 1)).DK.lv A.v').toJ
        (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.cAt
          (((A.IK.setV (A.v' + 1)).DK.lv A.v').two false)) :=
    fun e => hj' (by rw [e, hc]; exact hG false)
  have h2 : j' ≠
      ((A.IK.setV (A.v' + 1)).DK.lv A.v').toJ
        (((A.IK.setV (A.v' + 1)).DK.lv A.v').T.cAt
          (((A.IK.setV (A.v' + 1)).DK.lv A.v').two true)) :=
    fun e => hj' (by rw [e, hc]; exact hG true)
  rw [if_neg h1, if_neg h2]
  simp

omit [Fintype E] in
/-- Glue: an entry of a list of pulled-back rows. -/
theorem LdLkp.getD_pull {J N : Type} (ι : N → J) (G : J → Prop) (n : N) (hn : ¬ G (ι n)) :
    ∀ (l : List (Row E J)) (i : ℕ),
      RowsSupp G l → ((l.map (Row.pull ι)).getD i ⟨fun _ => 0, 0⟩).cf n = 0
  | [], _, _ => rfl
  | r :: _, 0, h => h r List.mem_cons_self (ι n) hn
  | _ :: l, i + 1, h => getD_pull ι G n hn l i fun r hr => h r (List.mem_cons_of_mem _ hr)

theorem ldWfB_supp : Spec.ldWfB_supp E := by
  intro p C P K hK l hl x y τ x' h
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨o, _, ho⟩ := Option.bind_eq_some_iff.mp hxo
  obtain rfl := Option.some.inj ho
  refine ⟨fun n hn => ?_, fun b n hn => ?_⟩
  · exact (K.asm l).supp_formK E (fun j => ∃ n', j = Sum.inr n' ∧ P.gC l n')
      (fun b => ⟨_, rfl, hK.supC l hl b⟩) o (Sum.inr n) fun ⟨n', e, hg⟩ => hn (Sum.inr.inj e ▸ hg)
  · exact getD_pull E Sum.inr _ n (fun ⟨n', e, hg⟩ => hn (Sum.inr.inj e ▸ hg)) _ _
      (ldBldWf_suppRows E (K.asm l) _ (hK.supR l hl b) o)

theorem ldWfB_same : Spec.ldWfB_same E := fun C P K l =>
  ldLkpAsm2N_same E (K.asm l) P.N Sum.inr C P.S P.msg

end
end Cb
