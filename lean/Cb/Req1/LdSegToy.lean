-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegToy.lean: a guard against emptiness: a whole toy segment: all hypotheses of
`Cb.ldSeg_goodB` met together, nothing assumed but that the bridge's evader evades and whatever the
arguments hold as proofs (among them: the evader's type D of seeds is not empty: `Evader.ne`,
Cb/Gen/BatEvader.lean).

Definitions, statements (in `Cb.Spec`) and proofs. No parameter of a real protocol.

The group: the toy of Cb/Ld/LdGroupToy.lean: field with 101 elements; Reed-Solomon, five points,
dimension 2, distance 4, radius 2 (not below half the distance); oracle messages "ord" (three main
rows, one mask row), "kep" (one main row: kept), "msk" (mask-only); k = 2 variables; four super-rows
of two base rows, one virtual zero row, a copy of the kept row in every super-row. A base row has
two message entries: of "kep" the first is a cell, the second its pad place.
The segment (`LdGToy.V`; `StdNew`, `V.seg`: Cb/Ld/LdGroupNewStd.lean). No body, no batching.
   bridge, arrangement, fold: on the group, beside "kep", which is held in the folded word from here
     on. 4 rounds.
   the one sending: two new oracle messages, standard ones (data and one pad; the row with a pad as
     sample; each datum has a corner of its own) under the same five-point code at the radius 2:
     "kep" encoded anew: its cell at the same place, a fresh pad at the pad place; the carried
     message: the folded ordinary slot, the two folded masks, all encoding randomness, the old pad
     of "kep", and a pad of its own. 2 rounds.
   the locations: one location of the folded word; "kep" as it was sent leaves here. 1 round.
The rows of the claim on the group, the bridge's evader and what is claimed of "kep" beside them
(any base joint A₀) are parameters.

Main names:
  `Spec.ldSeg_toy`: for all these, if the evader evades: `V.SegAll` (Cb/Ld/LdGroupNewStd.lean): the
    segment's five hypotheses (`LdSeg.Hyp`); all of the bundle but zero knowledge
    (`Cb.ldSeg_goodB`); knowledge soundness on collision-free statements of the first stage a that
    also meet `a.A.on` into collision-free statements (`Cb.ldSeg_into`); its rounds are
    bridge-to-fold's and 3 more; and bridge-to-fold has 4: 7 rounds in all.
  `Spec.ldSeg_toy_new`: the new messages are as described: the cell of "kep" stands at the same
    place of the new message; its old pad stands in the carried message; at the pad place the new
    message has a fresh entry.
  The errors, by the names under which the segment's numbers are built, each against the number of
  values of its verifier message. The first two are told after other files, named beside them;
  `Spec.ldSeg_toy_err` has the last two.
      the bridge: 2 · (the evader's number); with independent coefficients 2 · 101^(r - 1) of 101^r
        (`ldGroup_toy_ev`, Cb/Ld/LdGroupToy.lean).
      the fold: 2 of 101; 52 of 101; 20 of 101 (by reading of the definitions; `ld_pack_toy_err`,
        Cb/Ld/LdSumPackToy.lean, states bounds).
      the seeds: (2 choose 2) · err of each new message is below the number of its seeds: a standard
        message with m data, each with a coordinate of its own, has err =
        max (m · 101^(m - 1) · 100) (101^m) and 101^m · 100 seeds; "kep" anew has m = 1; the carried
        message has m ≤ 26 (26 = all entries that are placed).
      the location: 2 of 5.

Limits: No security. Zero knowledge is no item of a segment. This file does not say that the list of
errors of the segment's term is these numbers in this order. No body, no batching, no rider of a
next segment.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStd
import Cb.Ld.LdGroupToy
import Cb.Obj.LdObjectToyConf
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood LdToy

namespace LdGToy

/-- each datum has a corner of its own -/
def ind {X : Type} [DecidableEq X] : X → X → Bool := fun d m => decide (m = d)

theorem ind_inj {X : Type} [DecidableEq X] : Function.Injective (ind (X := X)) := fun d d' h => by
  have h1 : decide (d = d) = decide (d = d') := congrFun h d
  simpa using h1

theorem sJ_inj : ∀ n n' : Hh.hd.Ent, Hh.hd.sJ n.1 n.2 = Hh.hd.sJ n'.1 n'.2 → n = n' := by
  rintro ⟨⟨⟨o, ho⟩, hc⟩, j⟩ ⟨⟨⟨o', ho'⟩, hc'⟩, j'⟩ h
  obtain rfl : o = .kep := ho
  obtain rfl : o' = .kep := ho'
  rcases j with ⟨u, c⟩ | ⟨e, _⟩
  · rcases j' with ⟨u', c'⟩ | ⟨e, _⟩
    · have h1 : c = c' := (Prod.mk.inj (Sum.inl.inj h)).2
      subst h1
      rfl
    · exact e.elim
  · exact e.elim

open Classical in
/-- The new messages of the toy's closing. -/
def V : StdNew Hh.hd P5 where
  ag := fun _ => True
  pj := fun k => pjAll k.1.1.1
  Mn := fun k =>
    toyStd {j : (D.code k.1.1.1).J // j ≠ pjAll k.1.1.1}
      {j : (D.code k.1.1.1).J // j ≠ pjAll k.1.1.1} ind
  cl := fun _ => Equiv.refl _
  Mc := @toyStd _ _ (Fintype.ofFinite _) (Classical.decEq _)
    (Fintype.ofFinite _) (Classical.decEq _) ind
  cc := Equiv.refl _
  inj := sJ_inj

open Classical in
theorem V_ok : V.OK 2 1 :=
  ⟨(@toyStd_ok _ _ (Fintype.ofFinite _) (Classical.decEq _) (Fintype.ofFinite _)
      (Classical.decEq _) ind ind_inj).1,
    fun _ => (toyStd_ok _ _ ind ind_inj).1⟩

end LdGToy

namespace Spec
open LdGToy

open Classical in
/-- States: if the evader evades (`Z.OK`), the toy segment has all its hypotheses, and so what
`SegAll` (Cb/Ld/LdGroupNewStd.lean) gathers of what Cb/Req1/LdSeg.lean states of a segment;
bridge-to-fold has 4 rounds, the segment 4 + 3. -/
def ldSeg_toy : Prop :=
  ∀ (B Kc St₀ Wp : Type) [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf K (Sb b) D.G.C.J)
      (Z : Evader K (D.G.Row B)) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((D.S.sub kp).Msg × Wp))
      (dw : D.S.Wit × Wp)
      (w0 : (Hh.hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hh.hd.foldD Sb sl Z A₀).tgt.Wp),
    Z.OK → V.SegAll Sb sl Z A₀
        (Hh.hd.link Sb sl Z A₀ (fun _ => Or.inl trivial) dw 4 1 (fun _ => 2) (fun _ => 16)
          (fun _ => 16) (fun _ => 16) 2)
        w0 2 1 1 dw ∧
      (Hh.hd.link Sb sl Z A₀ (fun _ => Or.inl trivial) dw 4 1 (fun _ => 2) (fun _ => 16)
          (fun _ => 16) (fun _ => 16) 2).R.shape.nAll = 4

/-- the one kept message, as a message that is encoded anew -/
def kepK : {k // V.ag k} := ⟨⟨⟨.kep, rfl⟩, trivial⟩, trivial⟩

/-- The new messages are as described. -/
def ldSeg_toy_new : Prop :=
  (∀ m : V.N.N₀.Msg, (V.N.cut m).1 (Hh.hd.sJ kepK.1 (.inl ((), toyPlace Bool false))) =
    m (some kepK) (V.N.same kepK (.inl ((), toyPlace Bool false)))) ∧
  (∃ c : V.N.oc.C.J,
    ∀ m : V.N.N₀.Msg, (V.N.cut m).1 (Hh.hd.sJ kepK.1 (.inl ((), toyPlace Bool true))) = m none c) ∧
  (∃ q : V.N.Qo, V.N.place (.inr q) = ⟨some kepK, V.N.same kepK (.inl ((), toyPlace Bool true))⟩)

/-- The errors of the sending and of the location. -/
def ldSeg_toy_err : Prop :=
  Nat.choose 2 2 * V.Mc.Z.err < Fintype.card V.Mc.Z.D ∧
  Nat.choose 2 2 * (V.Mn kepK).Z.err < Fintype.card (V.Mn kepK).Z.D ∧
  Nat.card V.Mc.Dt ≤ 26 ∧
  Nat.card (V.Mn kepK).Dt = 1 ∧
  (Fintype.card P5 - 2 - 1) ^ 1 = 2 ∧
  Fintype.card (Fin 1 → P5) = 5

end Spec

open LdGToy in
open Classical in
theorem ldSeg_toy : Spec.ldSeg_toy := by
  intro B Kc St₀ Wp _ Sb sl Z E₀ A₀ dw w0 hZ
  obtain ⟨-, -, -, -, -, hl, hr⟩ := ldGroup_toy B Kc St₀ Wp Sb sl Z E₀ A₀ dw hZ
  exact ⟨stdNew_all V Sb sl Z A₀ _ w0 1 dw hl V_ok, hr⟩

open LdGToy Spec in
theorem ldSeg_toy_new : Spec.ldSeg_toy_new := by
  have hc : ¬ V.N.pad kepK (.inl ((), toyPlace Bool false)) := fun h => by
    have h1 : toyPlace Bool false = toyPlace Bool true := (Prod.mk.inj (Sum.inl.inj h)).2
    exact absurd ((toyPlace Bool).injective h1) (by decide)
  have hp : V.N.pad kepK (.inl ((), toyPlace Bool true)) := rfl
  exact ⟨fun m => ldGroup_place_cells K D.S D.G T.sh kp Hh.hd V.N m kepK _ hc,
    ldGroup_place_pads K D.S D.G T.sh kp Hh.hd V.N kepK _ hp,
    ⟨.inl ⟨kepK, ⟨_, hp⟩⟩, ldGroup_place_fresh K D.S D.G T.sh kp Hh.hd V.N kepK _ hp⟩⟩

namespace LdGToy

theorem cardJ : Nat.card T.sh.Cf.J = 12 := by
  show Nat.card
      ((Option Unit × (Σ _ : Unit, Bool × Fin 1))
        ⊕ ((Σ _ : Unit, PCol 1 1 1 × Fin 1) ⊕ (Σ _ : Unit, PCol 1 1 1 × Fin 1))) = 12
  simp [PCol]

theorem cardQ : Nat.card T.sh.Cf.Q = 12 := by
  show Nat.card
      ((Option Unit × (Σ _ : Unit, Bool × Fin 1))
        ⊕ ((Σ _ : Unit, PCol 1 1 1 × Fin 1) ⊕ (Σ _ : Unit, PCol 1 1 1 × Fin 1))) = 12
  simp [PCol]

instance : Unique {k // V.ag k} := ⟨⟨Spec.kepK⟩, fun ⟨⟨⟨o, ho⟩, _⟩, _⟩ => by
  obtain rfl : o = .kep := ho
  rfl⟩

theorem cardPad : Nat.card (Σ k : {k // V.ag k}, {j // V.pad k j}) = 1 := by
  haveI : Unique (Σ k : {k // V.ag k}, {j // V.pad k j}) := ⟨⟨⟨default, ⟨V.pj default, rfl⟩⟩⟩, fun ⟨k, j⟩ => by
    obtain rfl := Subsingleton.elim k default
    exact congrArg (Sigma.mk default) (Subtype.ext j.2)⟩
  exact Nat.card_unique

theorem cardAll : Nat.card (Hh.hd.All V.ag V.pad Unit) = 26 := by
  show Nat.card ((T.sh.Cf.J ⊕ T.sh.Cf.Q) ⊕ ((Σ k : {k // V.ag k}, {j // V.pad k j}) ⊕ Unit)) = 26
  rw [@Nat.card_sum (T.sh.Cf.J ⊕ T.sh.Cf.Q) _ _ _, @Nat.card_sum T.sh.Cf.J T.sh.Cf.Q _ _,
    @Nat.card_sum (Σ k : {k // V.ag k}, {j // V.pad k j}) Unit _ _, cardJ, cardQ, cardPad]
  simp

theorem cardCell : Nat.card (V.Mn Spec.kepK).Dt = 1 := by
  haveI : Unique {j : (D.code .kep).J // j ≠ pjAll .kep} :=
    ⟨⟨⟨.inl ((), toyPlace Bool false), fun h => by
      have h1 : toyPlace Bool false = toyPlace Bool true := (Prod.mk.inj (Sum.inl.inj h)).2
      exact absurd ((toyPlace Bool).injective h1) (by decide)⟩⟩, fun ⟨j, hj⟩ => by
    rcases j with ⟨u, c⟩ | ⟨e, _⟩
    · obtain ⟨b, rfl⟩ := (toyPlace Bool).surjective c
      cases b
      · rfl
      · exact absurd rfl hj
    · exact e.elim⟩
  show Nat.card {j : (D.code .kep).J // j ≠ pjAll .kep} = 1
  exact Nat.card_unique

theorem bnCard : Fintype.card Bn = 100 := by
  rw [Fintype.card_subtype_compl, ZMod.card, Fintype.card_subtype_eq]

theorem arith (m : ℕ) (hm : m < 101) :
    Nat.choose 2 2 * max (m * 101 ^ (m - 1) * 100) (101 ^ m) < 101 ^ m * 100 := by
  rw [Nat.choose_self, one_mul]
  refine max_lt ?_ ?_
  · rcases m with _ | m
    · simp
    · have h1 : (m + 1) * 101 ^ (m + 1 - 1) < 101 ^ (m + 1) := by
        rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm]
        exact Nat.mul_lt_mul_of_pos_left hm (by positivity)
      exact Nat.mul_lt_mul_of_pos_right h1 (by norm_num)
  · have h2 : 0 < 101 ^ m := by positivity
    omega

/-- a standard message over the field with 101 elements whose pad's coefficient has 100 values and
whose point has fewer than 101 coordinates: the error of its seed is below the number of its
seeds -/
theorem stdM_err {P : Type} [Fintype P] (M : StdM K P)
    (hB : Fintype.card M.B = 100) (h : Fintype.card M.μ < 101) :
    Nat.choose 2 2 * M.Z.err < Fintype.card M.Z.D := by
  show Nat.choose 2 2 *
      max (Fintype.card M.μ * Fintype.card K ^ (Fintype.card M.μ - 1) * Fintype.card M.B)
        (Fintype.card K ^ Fintype.card M.μ) <
    Fintype.card ((M.μ → K) × M.B)
  rw [Fintype.card_prod, Fintype.card_fun, hB, ZMod.card]
  exact arith _ h

end LdGToy

open LdGToy Spec in
open Classical in
theorem ldSeg_toy_err : Spec.ldSeg_toy_err := by
  have hc : Nat.card V.Mc.Dt ≤ 26 :=
    le_trans (Finite.card_subtype_le _) (le_trans (Finite.card_subtype_le _) (le_of_eq cardAll))
  refine ⟨?_, ?_, hc, ?_, ?_, ?_⟩
  · exact stdM_err V.Mc bnCard
      (lt_of_le_of_lt (le_of_eq (@Nat.card_eq_fintype_card _ V.Mc.finμ).symm)
        (lt_of_le_of_lt hc (by norm_num)))
  · exact stdM_err (V.Mn kepK) bnCard
      (lt_of_le_of_lt
        (le_of_eq ((@Nat.card_eq_fintype_card _ (V.Mn kepK).finμ).symm.trans cardCell))
        (by norm_num))
  · exact cardCell
  · rw [card5]
    rfl
  · rw [Fintype.card_fun, card5]
    simp

end Cb
