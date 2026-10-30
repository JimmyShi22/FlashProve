-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscGood.lean: the bundle of the sumcheck for a polynomial summand as a masked block, between
statements about oracle messages; and that, under the hypotheses of its statement, it does not look
at other blocks' masks.

This file sets the sumcheck of Cb/Ld/LdPsc.lean (`PscPar.psc`) between statements about oracle
messages (`S.over`, Cb/Ld/LdSig.lean), and states there the record `GoodM` (Ior/Masked.lean) of it.
Definitions, statements and proofs. S is a signature (Cb/Ld/LdSig.lean); "msg" reads the entries
that the block's parameters name off the tuple of messages of S; A0 is any base joint that rides
along.

Main names:
  `Y.maskSig S E₀ Wp msg O`: the fields (`IOR.MaskData`) of the item "masked messages"
    (`IOR.Honest.MM`; both Ior/Masked.lean) over S: those of Cb/Ld/LdPscZk.lean, read through the
    constructions that set the block over S (Ior/MaskedFrame.lean, Ior/MaskedMap.lean). Of a witness
    (pairs of message and encoding randomness, further part) is read: the entries in O.Rd of the
    messages; no encoding randomness.
    Of the explicit part ((target, state), samples): (target, state); no sample. Same simulator as
    at the base.
  `Spec.psc_goodM_sig`: under `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` and `Y.OwnOK O`, the block over S
    has the bundle `GoodM` (Ior/Masked.lean): all of `GoodT` but zero knowledge
    (Cb/Ld/LdPscSig.lean), the item, and "the relation gives the claim". This is the form that the
    rule for chains with masks sent in advance takes (Ior/KnowCollRulesMask.lean:
    `Spec.goodT_seq_masked`).
  `Spec.psc_core_goodM_sig`: `Y.core` alone (round 0 and the rounds of the variables; the whole
    block where no map is revealed), with `Y.OwnW Rd` for `Y.OwnOK O`.
  `Spec.psc_our_goodM_sig`: the instance with the dummy last variable, under the hypotheses of its
    statement.
  `Spec.psc_blind`: the block as a link before another masked block (`Iop.IOR.Honest.Blind`), under
    `Y.OwnOK O`: let Rd' be a set of entries that holds all that this block reads, and let other
    mask entries lie at places "at'" that this block does not read. Then overwriting them changes
    nothing that this block sends or ends with, and `Y.cutAt Rd' (msg ·)` of the two witnesses
    handed on differs by the same overwriting.
  `Spec.psc_blind_sig`: the same over S.

Limits: this file does not say zero knowledge of a chain: for that the rounds before the block must
leave the own masks uniform given all that they show (`Honest.Fresh`), which is a matter of the
block that sends them (exactly: `Honest.Fresh`, Ior/KnowCollRulesMask.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscSig
import Cb.Ld.LdPscZkOur
import Ior.MaskedMap
import Ior.KnowCollRulesMask

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

namespace PscPar
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

/-- The fields of the item (`IOR.MaskData`) over a signature. -/
def maskSig (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (msg : S.Msg → Y.J → E) (O : Y.Own) :
    IOR.MaskData ((Y.psc E₀).keep S.Smp S.ext) (S.Wit × Wp) :=
  ((Y.maskData E₀ (fun w : S.Msg × Wp => msg w.1) O).keep S.Smp S.ext).mapW fun w =>
    (S.msgs w.1, w.2)
def maskSigC (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (msg : S.Msg → Y.J → E) (Rd : Y.J → Prop) :
    IOR.MaskData ((Y.core E₀).keep S.Smp S.ext) (S.Wit × Wp) :=
  ((Y.maskDataC E₀ (fun w : S.Msg × Wp => msg w.1) Rd).keep S.Smp S.ext).mapW fun w =>
    (S.msgs w.1, w.2)

open Classical in
/-- the entries in Rd; all others set to 0 -/
def cutAt (Rd : Y.J → Prop) (m : Y.J → E) : Y.J → E := fun j => if Rd j then m j else 0

end PscPar

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- States, under the hypotheses below: the block over a signature is a masked block (`IOR.GoodM`).
-/
def psc_goodM_sig : Prop :=
  ∀ (S : Sig E) (Y : PscPar E) (E₀ : ExtSpec) (Wp Kc : Type) (A0 : Rels Kc Y.St E₀ (S.Msg × Wp))
      (msg : S.Msg → Y.J → E) (O : Y.Own),
    Y.VarsOK → Y.DegOK → Y.ValInj → Y.OwnOK O →
    GoodM ((Y.psc E₀).keep S.Smp S.ext) (S.liftH (Y.hon E₀ fun w => msg w.1))
      (S.over (Y.baseIn A0 fun w => msg w.1)) (S.over (Y.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((Y.nums E₀ Kc).keep S.Smp S.ext) (Y.maskSig S E₀ Wp msg O)

def psc_core_goodM_sig : Prop :=
  ∀ (S : Sig E) (Y : PscPar E) (E₀ : ExtSpec) (Wp Kc : Type) (A0 : Rels Kc Y.St E₀ (S.Msg × Wp))
      (msg : S.Msg → Y.J → E) (Rd : Y.J → Prop),
    Y.VarsOK → Y.DegOK → Y.ValInj → Y.OwnW Rd →
    GoodM ((Y.core E₀).keep S.Smp S.ext) (S.liftH (Y.honC E₀ fun w => msg w.1))
      (S.over (Y.baseIn A0 fun w => msg w.1)) (S.over (Y.baseMid A0 fun w => msg w.1))
      (fun _ _ w => w) ((Y.numsC E₀ Kc).keep S.Smp S.ext) (Y.maskSigC S E₀ Wp msg Rd)

/-- The instance with the dummy variable. -/
def psc_our_goodM_sig : Prop :=
  ∀ (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp Kc : Type) (A0 : Rels Kc T.St E₀ (S.Msg × Wp))
      (msg : S.Msg → T.J → E) (Rd : T.J → Prop),
    T.VarsOK → T.DegX → T.DegY → T.ValInj → T.OwnOur Rd →
    GoodM ((T.par.psc E₀).keep S.Smp S.ext) (S.liftH (T.par.hon E₀ fun w => msg w.1))
      (S.over (T.par.baseIn A0 fun w => msg w.1)) (S.over (T.par.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((T.par.nums E₀ Kc).keep S.Smp S.ext) (T.par.maskSig S E₀ Wp msg (T.own Rd))

/-- States, under the hypotheses below: the block does not look at masks that it does not read. -/
def psc_blind : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O : Y.Own), Y.OwnOK O →
    ∀ (Rd' : Y.J → Prop) (I' : Type) (at' : I' → Y.J), (∀ j, O.Rd j → Rd' j) →
      (∀ i, ¬ O.Rd (at' i)) →
      (Y.hon Ex msg).Blind (fun w => Y.cutAt Rd' (msg w)) (fun w => Y.cutAt Rd' (msg w)) (I' → E)
        (fun M k => Function.extend at' M k) (fun M k => Function.extend at' M k)

/-- The same over a signature. -/
def psc_blind_sig : Prop :=
  ∀ (S : Sig E) (Y : PscPar E) (E₀ : ExtSpec) (Wp : Type) (msg : S.Msg → Y.J → E) (O : Y.Own),
    Y.OwnOK O →
    ∀ (Rd' : Y.J → Prop) (I' : Type) (at' : I' → Y.J), (∀ j, O.Rd j → Rd' j) →
      (∀ i, ¬ O.Rd (at' i)) →
      (S.liftH (Wp := Wp) (Y.hon E₀ fun w => msg w.1)).Blind
        (fun w => Y.cutAt Rd' (msg (S.msgs w.1))) (fun w => Y.cutAt Rd' (msg (S.msgs w.1))) (I' → E)
        (fun M k => Function.extend at' M k) (fun M k => Function.extend at' M k)

end Spec
end

/-! ## Proofs -/

section NoOrc

/-- every round's oracle part has at most one value -/
def noOrcs : Shape → Prop
  | [] => True
  | r :: s => Subsingleton r.Orc ∧ noOrcs s

theorem tr_ext_noOrcs :
    ∀ (s : Shape), noOrcs s → ∀ τ τ' : Tr s, τ.plains = τ'.plains → τ.rho = τ'.rho → τ = τ'
  | [], _, _, _, _, _ => rfl
  | _ :: s, h, (m, c, a), (m', c', a'), hp, hr => by
      have h1 : m.2 = m'.2 := congrArg Prod.fst hp
      have h2 : a.plains = a'.plains := congrArg Prod.snd hp
      have h3 : c = c' := congrArg Prod.fst hr
      have h4 : a.rho = a'.rho := congrArg Prod.snd hr
      have h5 : m = m' := Prod.ext (h.1.elim _ _) h1
      rw [h5, h3, tr_ext_noOrcs s h.2 a a' h2 h4]

theorem noOrcs_rounds {E : Type} [Field E] :
    ∀ (l : List (PFmt E)) (t : Shape), noOrcs t → noOrcs (pRounds l ++ t)
  | [], _, h => h
  | _ :: l, t, h => ⟨inferInstanceAs (Subsingleton Unit), noOrcs_rounds l t h⟩

end NoOrc

section Proofs
open IOR
variable (E : Type) [Field E] [Fintype E]

theorem PscPar.sumHolds_cut {E : Type} [Field E] [Fintype E] {Y : PscPar E} {O : Y.Own}
    (hO : Y.OwnOK O) (x : E × Y.St) (m : Y.J → E) (h : Y.SumHolds x m) :
    Y.SumHolds x (O.cut m) := by
  show hSumAll (Y.vars x.2) (Y.sum x.2 (O.cut m)) + Y.inc x.2 (O.cut m) = x.1
  rw [PscPar.sum_congr (PscPar.G_cut hO x.2 m) (PscPar.Gb_cut hO x.2 m), PscPar.inc_cut hO]
  exact h

theorem psc_goodM_sig : Spec.psc_goodM_sig E := fun S Y E₀ Wp Kc A0 msg O hV hD hI hO =>
  { base := psc_goodB_sig E S Y E₀ Wp Kc A0 msg hV hD hI
    mm := mm_mapW _ _ _ _ _ _ _ _ _ _ _ _ _
      (mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
        (psc_mm E Y E₀ (S.Msg × Wp) (fun w => msg w.1) O hV hD hO))
    claim := fun x _ w h => PscPar.sumHolds_cut hO x.1 (msg (S.msgs w.1)) h.2.2.2 }

open Classical in
theorem psc_core_goodM_sig : Spec.psc_core_goodM_sig E := fun S Y E₀ Wp Kc A0 msg Rd hV hD hI hO =>
  { base := psc_core_goodB_sig E S Y E₀ Wp Kc A0 msg hV hD hI
    mm := mm_mapW _ _ _ _ _ _ _ _ _ _ _ _ _
      (mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
        (psc_core_mm E Y E₀ (S.Msg × Wp) (fun w => msg w.1) Rd hV hD hO))
    claim := fun x _ w h => by
      have cr : ∀ j, Rd j → (if Rd j then msg (S.msgs w.1) j else 0) = msg (S.msgs w.1) j :=
        fun j h => if_pos h
      show hSumAll (Y.vars x.1.2) (Y.sum x.1.2 fun j => if Rd j then msg (S.msgs w.1) j else 0) +
          Y.inc x.1.2 (fun j => if Rd j then msg (S.msgs w.1) j else 0) = x.1.1
      rw [PscPar.sum_congr (hO.rdG x.1.2 _ _ cr) (hO.rdGb x.1.2 _ _ cr),
        PscPar.inc_congr fun j hj => cr j (by by_contra h; exact hj (hO.rdS x.1.2 j h))]
      exact h.2.2.2 }

theorem psc_our_goodM_sig : Spec.psc_our_goodM_sig E := fun S T E₀ Wp Kc A0 msg Rd hV hX hY hI hO =>
  psc_goodM_sig E S T.par E₀ Wp Kc A0 msg (T.own Rd) ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY)
    ((psc_our_ok E T).2 hI) (psc_our_own E T Rd hO)

/-- Under `h1`, `h2`, `h`: what the block reads is not touched by an overwriting of entries that it
does not read. -/
theorem PscPar.cut_eq_of_blind {E : Type} [Field E] [Fintype E] {Y : PscPar E} {O : Y.Own}
    {Rd' : Y.J → Prop} {I' : Type} {at' : I' → Y.J} (h1 : ∀ j, O.Rd j → Rd' j)
    (h2 : ∀ i, ¬ O.Rd (at' i)) {m m' : Y.J → E} {M : I' → E}
    (h : Y.cutAt Rd' m' = Function.extend at' M (Y.cutAt Rd' m)) : O.cut m' = O.cut m := by
  funext j
  by_cases hj : O.Rd j
  · have e := congrFun h j
    rw [Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact h2 i hj)] at e
    have a : ∀ u : Y.J → E, Y.cutAt Rd' u j = u j := fun u => if_pos (h1 j hj)
    rw [a, a] at e
    rw [PscPar.cut_rd m' j hj, PscPar.cut_rd m j hj, e]
  · exact (if_neg hj).trans (if_neg hj).symm

theorem psc_blind : Spec.psc_blind E := by
  intro Y Ex Wt msg O hO Rd' I' at' h1 h2 w w' M x c ρ h
  have hc : O.cut (msg w') = O.cut (msg w) := PscPar.cut_eq_of_blind h1 h2 h
  have e2 := psc_hands E Y Ex Wt msg O hO w' x c ρ
  have e1 := psc_hands E Y Ex Wt msg O hO w x c ρ
  refine ⟨?_, ?_, ?_⟩
  · have hn : noOrcs (Y.psc Ex).shape :=
      (⟨inferInstanceAs (Subsingleton Unit),
        noOrcs_rounds Y.fmt [pRoundV E Y.A]
          (⟨inferInstanceAs (Subsingleton Unit), trivial⟩ : Subsingleton Unit ∧ True)⟩ :
        Subsingleton Unit ∧ noOrcs (pRounds Y.fmt ++ [pRoundV E Y.A]))
    refine tr_ext_noOrcs _ hn _ _ ?_ ?_
    · rw [(PscPar.run_hon Ex msg w' x c ρ).1, (PscPar.run_hon Ex msg w x c ρ).1,
        ← PscPar.sent_cut hO, hc, PscPar.sent_cut hO]
    · rw [Strat.rho_run, Strat.rho_run]
  · rw [e2, e1, hc]
  · rw [e2, e1]
    exact h

theorem psc_blind_sig : Spec.psc_blind_sig E := by
  intro S Y E₀ Wp msg O hO Rd' I' at' h1 h2 w w' M x c ρ h
  obtain ⟨b1, b2, -⟩ := psc_blind E Y E₀ (S.Msg × Wp) (fun w => msg w.1) O hO Rd' I' at' h1 h2
    (S.msgs w.1, w.2) (S.msgs w'.1, w'.2) M x.1 c ρ h
  have run : ∀ v : S.Wit × Wp, ((S.liftH (Y.hon E₀ fun w => msg w.1)).strat v x c).run ρ =
      ((((Y.hon E₀ fun w : S.Msg × Wp => msg w.1).strat (S.msgs v.1, v.2) x.1 c).run ρ).1,
        (((((Y.hon E₀ fun w : S.Msg × Wp => msg w.1).strat (S.msgs v.1, v.2) x.1 c).run ρ).2.1,
            x.2),
          (v.1, (((Y.hon E₀ fun w : S.Msg × Wp => msg w.1).strat (S.msgs v.1, v.2) x.1 c).run
              ρ).2.2.2))) := by
    intro v
    show (Strat.map _
        (Strat.map _
          ((Y.hon E₀ fun w : S.Msg × Wp => msg w.1).strat (S.msgs v.1, v.2) x.1 c))).run ρ = _
    rw [Strat.run_map, Strat.run_map]
  rw [run, run]
  exact ⟨b1, by rw [b2], h⟩

end Proofs
end Cb
