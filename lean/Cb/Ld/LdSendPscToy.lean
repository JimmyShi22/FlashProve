-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendPscToy.lean: a sending, then the masked sumcheck, at a small code, at a radius not below
half the distance: all hypotheses of `Spec.send_psc_our_goodT` (Cb/Ld/LdSendFresh.lean) met
together, nothing assumed beyond the hypotheses of `Spec.send_psc_toy`.

Statement (`Cb.Spec.send_psc_toy`) and proof. A guard against empty theorems; no parameter of a
protocol.

This file gives a small example: a reduction that sends one word, followed by the masked sumcheck of
Cb/Ld/LdPsc.lean, for which all hypotheses of `Spec.send_psc_our_goodT` (Cb/Ld/LdSendFresh.lean) are
proved.

The claim. Two data d_0, d_1 in the field with 101 elements, known to the prover alone, and a public
target: d_0 + d_1 = τ. (So the statement does not determine the witness: `Spec.send_psc_toy`'s first
clause.)
The oracle message. The code of Cb/Ld/LdRelToy.lean (Reed-Solomon, five points, one message symbol
and one symbol of randomness a row, distance 4, radius 2: not below half the distance), seven rows:
the two data; the two coefficients of a hiding polynomial; one inner mask for each datum; the pad.
The sample. The row with a pad of Cb/Gen/OodDecPad.lean: equality weights at a point on the six
entries proper (each has a corner of its own), β other than 0 on the pad.
The sender. The witness holds the data; the coins that go into the message are the four masks and
the pad.
The sumcheck (Cb/Ld/LdPsc.lean, the instance with the dummy variable). No variable of its own; both
data are revealed maps; the summand is value_0 + value_1, of degree 1 in the values. So: the sum of
the hiding polynomial; the coefficient ε; one round polynomial (in the dummy variable), the
challenge β' other than 0; the values d_a + β' c_a in the clear.

Main names:
  `Spec.send_psc_toy`:
    two different witnesses of one statement;
    the laws of the code, lists of at most 2, the sample evades, fair seeds, the sender's laws, the
      encoding hides 1 long position;
    the conditions of the sumcheck (variables, degrees, challenges);
    the conditions on the own entries (`OwnOur`);
    the conditions on the split of the sender's coins (`Own.Laws`: over, lay, pad);
    the two readings give one claim;
    and so, for every joint A0 that rides along, "the sending, then the sumcheck" has the bundle
      `GoodT`: in particular exact honest-verifier zero knowledge (`GoodT.exact`: `Honest.Exact`,
      Ior/Honest.lean).

`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.
What `LdCode.Laws`, `Sig.Sender.Laws`, `Fair`, `ListLE`, `Evades` and `Hides` ask: the head of
Cb/Ld/LdRng.lean ("What the sending's hypotheses ask").

Limits: this file says nothing on real parameters. That the errors are below the numbers of values
is not said here.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFreshProofs
import Cb.Ld.LdSendMem
import Cb.Ld.LdSendToy

set_option autoImplicit false

namespace Cb

/-- for an injective `O.at`: to overwrite the own entries twice is to overwrite them once -/
theorem PscPar.put_put {E : Type} [Field E] [Fintype E] {Y : PscPar E} {O : Y.Own}
    (hi : Function.Injective O.at) (M M' : O.Mk) (k : Y.J → E) :
    O.put M (O.put M' k) = O.put M k := by
  funext j
  by_cases h : ∃ i, O.at i = j
  · obtain ⟨i, rfl⟩ := h
    exact (hi.extend_apply _ _ _).trans (hi.extend_apply _ _ _).symm
  · exact (Function.extend_apply' _ _ _ h).trans
      ((Function.extend_apply' _ _ _ h).trans (Function.extend_apply' _ _ _ h).symm)

namespace PscToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy

noncomputable section

/-- the names of the coefficients of the hiding polynomial: one variable (the dummy), degree 1 -/
abbrev WI : Type := PIdx (([] : List (PFmt K)) ++ [pDummy K 1])
/-- the entries proper: the two data; the own masks (hiding coefficients, one inner mask for each
datum) -/
abbrev J0 : Type := Bool ⊕ (WI ⊕ Bool)
/-- the rows: the entries proper, and the pad -/
abbrev Rw : Type := J0 ⊕ Unit

/-- the entries of a message are the rows -/
def nuR : (toyLd Rw).J ≃ Rw where
  toFun j := j.2.1
  invFun r := ⟨(), (r, (0 : Fin 1))⟩
  left_inv := by
    rintro ⟨⟨⟩, b, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl
  right_inv := fun _ => rfl

/-- each entry proper has a corner of its own -/
def plR : J0 → J0 → Bool := fun j i => decide (i = j)

theorem plR_inj : Function.Injective plR := fun j j' h => by
  have h1 : plR j j = plR j' j := congrFun h j
  have h2 : plR j j = true := decide_eq_true rfl
  rw [h2] at h1
  exact of_decide_eq_true h1.symm

/-- the sample -/
@[reducible] def padR : Sample K (J0 ⊕ Unit) :=
  Sample.pad K J0 J0 Unit Bn plR (fun _ => 1) fun β => β.1

/-- the oracle message -/
@[reducible] def toyM : OMsg K := OMsg.plain (toyLd Rw) (padR.comap nuR) 2 fun _ => 0

/-- The sumcheck. -/
@[reducible] def toyT : PscOur K where
  St := Unit
  J := Rw
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun _ m a _ => m (.inl (.inl a))
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false + v true
  S1 := fun _ _ _ b => b.elim
  DY := 1
  slS := fun _ _ => 0
  wAt := fun i => .inl (.inr (.inl i))
  cAt := fun a => .inl (.inr (.inr a))

/-- what the sumcheck reads: every entry but the pad -/
def toyRd : Rw → Prop := fun j => j.isLeft = true

abbrev toyOw : toyT.par.Own := toyT.own toyRd
abbrev Sn : Sig K := Sig.nil K
abbrev Nn : Sig K := Sig.one toyM
abbrev Wp : Type := Bool → K

/-- a message, from the data, the own masks and the pad -/
def layR (d : Wp) (k : (toyOw.Mk × Unit) × K) : Rw → K :=
  Sum.elim (Sum.elim d (Sum.elim k.1.1.1 k.1.1.2)) fun _ => k.2

/-- the sender of the one member -/
@[reducible] def toyMem : ∀ a, (Nn.om a).Sender (Sn.Wit × Wp) Unit := fun _ =>
  { N := (toyLd Rw).Nn
    upM := fun m => m
    upR := fun r => r
    Mk := (toyOw.Mk × Unit) × K
    put := fun w k j => layR w.2 k (nuR j)
    rest := fun _ => ()
    w0 := (fun a => a.elim, 0) }

/-- The sender. -/
@[reducible] def toyDs : Nn.Sender (Sn.Wit × Wp) (Sn.Wit × Unit) :=
  Sig.Sender.ofMem toyMem (fun w => (w.1, ())) (fun a => a.elim, 0)

/-- the split of its coins -/
@[reducible] def toyU : toyDs.Own toyOw.Mk :=
  { M0 := Unit, Pd := K, κ := Equiv.funUnique Unit ((toyOw.Mk × Unit) × K) }

/-- the extractor of the sending: the data -/
def toyBk : Nn.Msg → Unit → Wp := fun m _ a => m () (nuR.symm (.inl (.inl a)))

/-- the two readings of the entries -/
def toyMsg : (Sn.sum Nn).Msg → Rw → K := fun m j => m (.inr ()) (nuR.symm j)
def toyMsg0 : Sn.Msg × Wp → Rw → K := fun w => Sum.elim (Sum.elim w.2 fun _ => 0) fun _ => 0

abbrev toySd : Nn.Seeds := Sig.Seeds.indep Nn

end
end PscToy

namespace Spec
open Iop LdToy PscToy IOR

def send_psc_toy : Prop :=
  (∃ d d' : Wp,
    d ≠ d' ∧
    toyT.SumHolds (1, ()) (toyMsg0 (fun a => a.elim, d)) ∧
    toyT.SumHolds (1, ()) (toyMsg0 (fun a => a.elim, d'))) ∧
  (∀ a, (Nn.om a).C.Laws) ∧ toySd.Fair ∧ (∀ a, (Nn.om a).ListLE 2) ∧ (∀ a, (Nn.om a).Evades) ∧
  toyDs.Laws (Sn.backN Nn toyBk) ∧ toyDs.Nn.Hides (Nn.budT fun _ => 1) ∧
  toyT.VarsOK ∧ toyT.DegX ∧ toyT.DegY ∧ toyT.ValInj ∧ toyT.OwnOur toyRd ∧
  toyU.Laws toySd
    (fun m w' => toyOw.cut (toyMsg (Sn.join Nn (T := OMsg.Msg) (Sn.msgs w'.1) m))) toyOw.put ∧
  (∀ x (m : (Sn.sum Nn).Msg) wp',
    toyT.SumHolds x
      (toyMsg0 (Sn.left Nn (T := OMsg.Msg) m, toyBk (Sn.right Nn (T := OMsg.Msg) m) wp')) ↔
    toyT.SumHolds x (toyMsg m)) ∧
  ∀ (Kc : Type) (E₀ : ExtSpec) (A0 : Rels Kc Unit E₀ (Sn.Msg × Wp)) (d : Sn.Wit × Wp),
    GoodT ((ldSendSig Sn Nn toySd (K × Unit) E₀).seq
        ((toyT.par.psc E₀).keep (Sn.sum Nn).Smp (Sn.sum Nn).ext))
      ((ldSendSigHon toySd (K × Unit) E₀ toyDs).seq
        ((Sn.sum Nn).liftH (toyT.par.hon E₀ fun w => toyMsg w.1)))
      (Sn.over (toyT.par.baseIn A0 toyMsg0)).cf
      ((Sn.sum Nn).over (toyT.par.baseOut (Sn.grow Nn A0 toyBk) fun w => toyMsg w.1)).cf
      (IOR.extSeq _ _
        (fun _ _ w =>
          (Sn.left Nn (T := OMsg.Wit) w.1, toyBk (Nn.msgs (Sn.right Nn (T := OMsg.Wit) w.1)) w.2))
        (fun _ _ w => w) d)
      ((ldSendSigNums Sn Nn toySd (K × Unit) E₀ Kc (fun _ => 2) fun _ => 1).seq
        ((toyT.par.nums E₀ Kc).keep (Sn.sum Nn).Smp (Sn.sum Nn).ext))

end Spec

namespace PscToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy

/-- a bijection pushes uniform to uniform, whatever the instances on the target -/
theorem map_unif_bij_any {α β : Type} [Fintype α] [Nonempty α] (iβ : Fintype β) (nβ : Nonempty β)
    {f : α → β} (hf : Function.Bijective f) :
    (unif α).map f = @unif β iβ nβ :=
  map_unif_of_bijective hf

theorem at_eq (i : WI ⊕ Bool) : Sum.elim toyT.wAt toyT.cAt i = Sum.inl (Sum.inr i) := by
  rcases i with i | i <;> rfl

theorem at_inj : Function.Injective (Sum.elim toyT.wAt toyT.cAt) := fun a b h => by
  rw [at_eq, at_eq] at h
  exact Sum.inr_injective (Sum.inl_injective h)

theorem ownOur : toyT.OwnOur toyRd :=
  { inj := at_inj
    own := fun i => by rw [at_eq]; rfl
    rdF := fun _ m m' hm => funext fun a => funext fun _ => hm (.inl (.inl a)) rfl
    rdFb := fun _ _ _ _ => funext fun b => b.elim
    rdS := fun _ _ _ => rfl
    oF := fun _ m m' hm => funext fun a => funext fun _ => hm (.inl (.inl a)) fun i h => by
      rw [at_eq] at h
      exact Sum.inl_ne_inr (Sum.inl_injective h)
    oFb := fun _ _ _ _ => funext fun b => b.elim
    oS := fun _ _ => rfl }

theorem degY : toyT.DegY := by
  intro _ _ v u _
  refine ⟨![v false + v true, u false + u true], fun y => ?_⟩
  show (v false + u false * y) + (v true + u true * y) + ∑ b : Empty, _ = _
  simp [hev, Fin.sum_univ_two]
  ring

theorem sumHolds_iff (x : K × Unit) (m : Rw → K) :
    toyT.SumHolds x m ↔ m (.inl (.inl false)) + m (.inl (.inl true)) = x.1 := by
  show (m (.inl (.inl false)) + m (.inl (.inl true)) + ∑ b : Empty, _) + ∑ j : Rw, (0 : K) * m j =
      x.1 ↔
    _
  simp

theorem padR_okOn : padR.OKOn (PadInF K) :=
  ood_okOn_pad K K J0 J0 Unit Bn _ _ _ plR_inj (fun _ _ h => Subtype.ext h) padBasis.1

theorem toyM_evades : toyM.Evades :=
  sig_evades_of_okOn K toyM _
    (ood_okOn_comap K (J0 ⊕ Unit) (toyLd Rw).J padR nuR (PadInF K) padR_okOn)
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

/-- the answer of the sample, for a message given by its rows -/
theorem val_rows (ρ : padR.D) (v : Rw → K) :
    (padR.comap nuR).val ρ (fun j => v (nuR j)) =
      fun _ => (∑ j : J0, Alg.eqk ρ.1 (plR j) * v (.inl j)) + ρ.2.1 * 1 * v (.inr ()) := by
  funext s
  show ∑ j, padR.mat ρ s (nuR j) * v (nuR j) = _
  rw [nuR.sum_comp fun n => padR.mat ρ s n * v n, Fintype.sum_sum_type]
  simp

theorem laws : toyDs.Laws (Sn.backN Nn toyBk) :=
  ldSendMem_laws K Nn _ _ toyMem _ _ _ (fun _ _ _ => rfl) fun w k => Prod.ext rfl (funext fun a => by
    show layR w.2 (k ()) (nuR (nuR.symm (.inl (.inl a)))) = w.2 a
    rw [Equiv.apply_symm_apply]
    rfl)

theorem ownLaws :
    toyU.Laws toySd (fun m w' => toyOw.cut (toyMsg (Sn.join Nn (T := OMsg.Msg) (Sn.msgs w'.1) m)))
      toyOw.put := by
  classical
  refine ⟨fun M M' k => PscPar.put_put (O := toyOw) at_inj M M' k,
    ⟨fun w _ => toyOw.cut (toyMsg0 (fun a => a.elim, w.2)), fun w M k₀ η => ?_⟩,
    ?_⟩
  · funext j
    show (if toyRd j then layR w.2 ((M, k₀), η) (nuR (nuR.symm j)) else 0) =
      Function.extend (Sum.elim toyT.wAt toyT.cAt) (Sum.elim M.1 M.2)
        (toyOw.cut (toyMsg0 (fun a => a.elim, w.2))) j
    rw [Equiv.apply_symm_apply]
    rcases j with (a | i) | u
    · rw [Function.extend_apply' _ _ _
          (by rintro ⟨i, h⟩; rw [at_eq] at h; exact Sum.inr_ne_inl (Sum.inl_injective h))]
      exact (if_pos rfl).trans (if_pos rfl).symm
    · rw [← at_eq i, at_inj.extend_apply, at_eq i]
      exact if_pos rfl
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, h⟩; rw [at_eq] at h; exact Sum.inl_ne_inr h)]
      have hn : ¬ toyRd (Sum.inr u) := fun h => Bool.noConfusion h
      exact (if_neg hn).trans (if_neg hn).symm
  · refine own_pad_of_uniform K Nn _ _ toyDs _ toyU toySd fun s w M k₀ => ?_
    have hv : ∀ η : K, toyDs.ans toySd s w (toyU.mk' M k₀ η) =
        fun _ _ =>
          (∑ j : J0, Alg.eqk (s ()).1 (plR j) * layR w.2 ((M, k₀), η) (.inl j)) +
              (s ()).2.1 * 1 * η := by
      intro η
      funext a
      cases a
      show (padR.comap nuR).val (s ()) (fun j => layR w.2 ((M, k₀), η) (nuR j)) = _
      rw [val_rows]
      rfl
    rw [funext hv]
    refine map_unif_bij_any _ _ ⟨fun η η' h => ?_,
      fun y =>
        ⟨(y () () - ∑ j : J0, Alg.eqk (s ()).1 (plR j) * layR w.2 ((M, k₀), 0) (.inl j)) /
            ((s ()).2.1 * 1),
          ?_⟩⟩
    · have h1 := congrFun (congrFun h ()) ()
      have h2 : (s ()).2.1 * 1 * η = (s ()).2.1 * 1 * η' := add_left_cancel h1
      exact mul_left_cancel₀ (by rw [mul_one]; exact (s ()).2.2) h2
    · funext a b
      cases a
      cases b
      have hb : (s ()).2.1 * 1 ≠ 0 := by rw [mul_one]; exact (s ()).2.2
      show (∑ j : J0, Alg.eqk (s ()).1 (plR j) * layR w.2 ((M, k₀), 0) (.inl j)) +
          (s ()).2.1 * 1 * _ = y () ()
      rw [mul_div_cancel₀ _ hb]
      ring

end PscToy

open LdToy PscToy in
theorem send_psc_toy : Spec.send_psc_toy := by
  have hT := ld_toy Rw
  have hC : ∀ a, (Nn.om a).C.Laws := fun _ => hT.1
  have hF : toySd.Fair := (ldSendFam_fair_indep K Nn).1
  have hL : ∀ a, (Nn.om a).ListLE 2 := fun _ => sig_list_of_code K toyM 2 hT.2.2.2.1
  have hE : ∀ a, (Nn.om a).Evades := fun _ => toyM_evades
  have hZ : toyDs.Nn.Hides (Nn.budT fun _ => 1) :=
    ldSendMem_hides K Nn _ _ toyMem _ _ (fun _ => 1) fun _ => hT.2.2.2.2.2.2.1
  have hV : toyT.VarsOK := fun _ v hv => absurd hv List.not_mem_nil
  have hX : toyT.DegX := fun _ _ _ => trivial
  have hI : toyT.ValInj := fun f hf => absurd hf List.not_mem_nil
  have hcl : ∀ x (m : (Sn.sum Nn).Msg) wp',
      toyT.SumHolds x
        (toyMsg0 (Sn.left Nn (T := OMsg.Msg) m, toyBk (Sn.right Nn (T := OMsg.Msg) m) wp')) ↔
      toyT.SumHolds x (toyMsg m) := fun x m wp' => by
    rw [sumHolds_iff, sumHolds_iff]
    exact Iff.rfl
  refine ⟨⟨fun b => if b then 1 else 0, fun b => if b then 0 else 1, fun h => ?_, ?_, ?_⟩, hC, hF,
    hL, hE, laws, hZ, hV, hX, degY, hI, ownOur, ownLaws, hcl, fun Kc E₀ A0 d => ?_⟩
  · have h1 : (1 : K) = 0 := congrFun h true
    exact one_ne_zero h1
  · rw [sumHolds_iff]
    show (0 : K) + 1 = 1
    rw [zero_add]
  · rw [sumHolds_iff]
    show (1 : K) + 0 = 1
    rw [add_zero]
  · exact send_psc_our_goodT K Sn Nn toySd toyT Kc Wp Unit E₀ A0 toyBk toyMsg0 toyMsg toyRd toyDs
      (fun _ => 2) (fun _ => 1) d toyU hC hF hL hE laws hZ hV hX degY hI ownOur ownLaws hcl

end Cb
