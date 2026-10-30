-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupToy.lean: a group with an ordinary message, a kept message and a mask-only message at
which all hypotheses of the first half of a closing hold together for every evader that evades,
nothing else assumed, at a radius not below half the distance.

In standard terms: a small worked instance (Reed-Solomon codes of length 5 and dimension 2 over a
field with 101 elements, proximity radius 2) at which all hypotheses of the theorems on batching and
folding a set of oracle messages hold at once, for every evader that evades (`Evader.OK`,
Cb/Gen/BatEvader.lean); with `Spec.ldGroup_toy_ev` it shows that these hypotheses can be met
together.
Evader (lean/GLOSSARY.md): data: a set of seeds, a vector of coefficients for each seed, and a
number (`Evader`, Cb/Gen/BatEvader.lean).

Definitions (`LdGToy`), statements (in `Cb.Spec`) and proofs. A guard against empty theorems; no
parameter of a real protocol.

1. For every standard group over codes at the toy's five long positions (Cb/Ld/LdGroupStd.lean;
field with 101 elements):
  `Spec.ldGroup_toy_hyp`: if Cb, Zb and Zb under the fresh mask's reading (`T.sh.par.Zw`) have their
    laws and distance at least 4 (`Dist 4`), then the fold's own hypotheses (`SumPar.Hyp`) hold at
    the radius 2 with lists of at most 2 codewords at every stage (the Johnson bound) and at most 16
    exceptional values for every table, given the rest of that record: degree at least 2, distinct
    challenges, the law of the packing (`PackOK`), the degrees of its weights (`QwDeg`), one row of
    the fresh mask hides 1 long position.
  `Spec.ldGroup_toy_list`: if `T.sh.OK` and Cb, Zb have distance at least 4, the complex as sent has
    lists of at most 2 codewords at the radius 2.
2. The instance (`LdGToy`). Codes: the toy of Cb/Ld/LdRelToy.lean (distance 4): two interleaved rows
for the base code, so that a base row has two message entries; for the mask code one row for each
column of the packing. k = 2 variables (h = 1, g = 1), degree n = 2, radius 2 (2 · 2 is not below
4).
  Three oracle messages: "ord": three main rows and one mask row; "kep": one main row, no mask row:
  kept; "msk": no main row, one mask row: mask-only.
  Four super-rows of two base rows each. Slot none: the three rows of "ord" in the super-rows 00,
  10, 01; in the super-row 11 nothing is sent: a virtual zero row. Slot some (): in every super-row
  a copy of the row of "kep". The two mask rows fill the cube of one variable.
  Read after the bridge: "kep" alone. It is held in the folded word.
  `Spec.ldGroup_toy`: for every set of rows of a claim, every evader that evades, every carried
    joint: the laws of the shape; the laws of the kept message; the fold's hypotheses; the joint
    radius implies each member's own; the list bound; so all four hypotheses of the move "first half
    of the closing of a group" (Cb/Req1/LdSegKit.lean: `LdFoldD.Hyp`) hold, and bridge, arrangement,
    fold beside the carried part has 4 rounds. (`Spec.ldGroup_fold`, Cb/Ld/LdGroupFold.lean, says,
    under the hypotheses of its statement, that it is a piece of a chain.)
  `Spec.ldGroup_toy_shape`: the instance is as described: a zero row, the copies, 2 · 2 not below 4.
  The errors: 2 · (the evader's number) for the bridge: with independent coefficients that is 2 of
    101 (`Spec.ldGroup_toy_ev`, for a nonempty set of rows); then the fold's: 2 of 101; 16 + 32 + 2
    · 2 = 52 of 101; 16 + 2 · 2 = 20 of 101 (the arithmetic: Cb/Ld/LdSumPackToy.lean:
    `ld_pack_toy_err`).

Limits: 52 of 101 is no security. This file says nothing on the second half of a closing (at this
group: `Spec.ldSeg_toy`, Cb/Req1/LdSegToy.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupStdMsg
import Cb.Ld.LdTowerToyKit
import Cb.Ld.LdSendToy
import Cb.Ld.LdSumPackToy
import Cb.Gen.BatEvaderProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood LdToy

namespace Spec

/-- The fold's hypotheses, for every standard group at the toy's positions.
(not all hypotheses are named here: see the statement below) -/
def ldGroup_toy_hyp : Prop :=
  ∀ (D : StdG K P5) (T : StdArr D), D.Cb.Laws → D.Cb.Dist 4 → D.Zb.Laws → D.Zb.Dist 4 →
    T.sh.par.Zw.Laws → T.sh.par.Zw.Dist 4 → 2 ≤ T.n → Function.Injective T.val → T.sh.par.PackOK →
    T.sh.par.QwDeg → T.sh.par.Zw.Zk 1 →
    T.sh.par.Hyp 4 2 1 (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16)

def ldGroup_toy_list : Prop :=
  ∀ (D : StdG K P5) (T : StdArr D), T.sh.OK → D.Cb.Dist 4 → D.Zb.Dist 4 → D.G.C.ListAt 2 2

end Spec

theorem ldGroup_toy_hyp : Spec.ldGroup_toy_hyp := by
  intro D T hC hCD hZ hZD hW hWD hn hv hP hQ hzk
  have hCs : T.sh.par.C.Laws := ld_laws_il K P5 _ _ hC
  have hCsD : T.sh.par.C.Dist 4 := ld_dist_il K P5 _ _ 4 hCD
  exact
    { codes := ⟨⟨hCs, hZ, hW⟩, ⟨hCsD, hZD, hWD⟩, by norm_num⟩
      errs :=
        { list := fun j _ =>
            list5 _ (ld_laws_pair K P5 _ _ (ld_laws_il K P5 _ _ hCs)
                (ld_laws_pair K P5 _ _ (ld_laws_il K P5 _ _ hZ) (ld_laws_il K P5 _ _ hW)))
            (ld_dist_pair K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 hCsD)
              (ld_dist_pair K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 hZD) (ld_dist_il K P5 _ _ 4 hWD)))
          mcaC := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hCs)
          mcaS := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hZ)
          mcaW := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hW) }
      inj := hv
      deg := hn
      pack := hP
      qw := hQ
      zk := ld_zk_il K P5 _ _ 1 hzk }

theorem ldGroup_toy_list : Spec.ldGroup_toy_list := by
  intro D T hOK hCD hZD
  refine ldGroup_list K D.S D.G T.sh 2 2 hOK (list5 _ ?_ ?_)
  · exact ld_laws_pair K P5 _ _ (ld_laws_il K P5 _ _ (ld_laws_il K P5 _ _ hOK.base))
      (ld_laws_il K P5 _ _ hOK.mask)
  · exact ld_dist_pair K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 hCD))
      (ld_dist_il K P5 _ _ 4 hZD)

/-! ## The instance -/

namespace LdGToy

/-- the three oracle messages -/
inductive Mem
  | ord
  | kep
  | msk
  deriving DecidableEq, Fintype

/-- their main rows and their mask rows -/
@[reducible] def Rm : Mem → Type
  | .ord => Fin 3
  | .kep => Unit
  | .msk => Empty
@[reducible] def Rz : Mem → Type
  | .ord => Unit
  | .kep => Empty
  | .msk => Unit

instance : ∀ a, Fintype (Rm a) := fun a => by cases a <;> infer_instance
instance : ∀ a, DecidableEq (Rm a) := fun a => by cases a <;> infer_instance
instance : ∀ a, Fintype (Rz a) := fun a => by cases a <;> infer_instance
instance : ∀ a, DecidableEq (Rz a) := fun a => by cases a <;> infer_instance

/-- the base code, the mask code -/
abbrev Cb5 : LdCode K P5 := toyLd Bool
abbrev Zb5 : LdCode K P5 := toyLd (PCol 1 1 1)

/-- the pad place of each message; of "kep": the second entry of its row -/
def pjAll : ∀ o : Mem, ((Cb5.il (Rm o)).pair (Zb5.il (Rz o))).J
  | .ord => .inl ((0 : Fin 3), toyPlace Bool true)
  | .kep => .inl ((), toyPlace Bool true)
  | .msk => .inr ((), plc5 1 1 (.inr (.inr ())))

/-- The group's data: each message is a standard oracle message (Cb/Ld/LdGroupStdMsg.lean): all
entries but the pad place are data; the sample is the row with a pad, its coefficient other than 0.
-/
@[reducible] def R5 : StdGM K P5 where
  Cb := Cb5
  Zb := Zb5
  A := Mem
  Rm := Rm
  Rz := Rz
  pj := pjAll
  B := Bn
  b := fun β => β.1
  e := 2

/-- The standard group. -/
@[reducible] def D : StdG K P5 := R5.D

instance : Nonempty D.G.P := ⟨(⟨0, by decide⟩ : Fin 5)⟩

/-- the corner of the cube of two variables with the number i -/
def corner (i : Fin 3) : Fin (1 + 1) → Bool := fun v => (i.val).testBit v.val

/-- The arrangement. -/
def T : StdArr D where
  Kp := Unit
  h := 1
  g := 1
  dst := fun r => match r with
    | ⟨⟨.ord, _⟩, i⟩ => .inl (corner i)
    | ⟨⟨.kep, _⟩, _⟩ => .inr ()
    | ⟨⟨.msk, _⟩, i⟩ => i.elim
  ord := fun b => match b 0, b 1 with
    | false, false => some ⟨⟨.ord, trivial⟩, (0 : Fin 3)⟩
    | true, false => some ⟨⟨.ord, trivial⟩, (1 : Fin 3)⟩
    | false, true => some ⟨⟨.ord, trivial⟩, (2 : Fin 3)⟩
    | true, true => none
  kept := fun _ => ⟨⟨.kep, trivial⟩, ()⟩
  dstZ := fun r => match r with
    | ⟨⟨.ord, _⟩, _⟩ => fun _ => false
    | ⟨⟨.kep, _⟩, i⟩ => i.elim
    | ⟨⟨.msk, _⟩, _⟩ => fun _ => true
  ordZ := fun b => match b 0 with
    | false => some ⟨⟨.ord, trivial⟩, ()⟩
    | true => some ⟨⟨.msk, trivial⟩, ()⟩
  n := 2
  Ch := K
  val := id
  AaW := Zb5.Aa
  TW := Zb5.T
  srcW := Zb5.src
  pk := pkAt (plc5 1 1) (pkC 1 1 1)
  Qw := QwAt (plc5 1 1) (QwC 1 1 1)

/-- read after the bridge: the kept message -/
@[reducible] def kp : Mem → Prop := fun o => o = .kep

/-- The kept message. -/
def Hh : StdHeld T kp where
  cl := fun _ => True
  noZ := fun k => by
    obtain ⟨⟨o, ho⟩, _⟩ := k
    obtain rfl : o = .kep := ho
    exact inferInstanceAs (IsEmpty Empty)
  slot := fun _ _ => ()

end LdGToy

namespace Spec
open LdGToy

/-- The instance is as described. -/
def ldGroup_toy_shape : Prop :=
  T.ord (fun _ => true) = none ∧
  (∀ b : Fin (1 + 1) → Bool, T.sh.am.src (b, some ()) = some ⟨⟨.kep, trivial⟩, ()⟩) ∧
  ¬ 2 * 2 < 4 ∧ D.e = 2

/-- States: for every nonempty set of rows, the evader with independent coefficients evades, and
2 · (its number) is 2 of 101 of the number of its seeds: an evader for the bridge. -/
def ldGroup_toy_ev : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] [Nonempty J],
    (Evader.indep K J).OK ∧
    (2 * (Evader.indep K J).err) * 101 = 2 * Fintype.card (Evader.indep K J).D

open Classical in
/-- States: for every set of rows of a claim, every evader that evades (`Z.OK`) and every carried
joint: all hypotheses together, and 4 rounds; the head lists them. -/
def ldGroup_toy : Prop :=
  ∀ (B Kc St₀ Wp : Type) [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf K (Sb b) D.G.C.J)
      (Z : Evader K (D.G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((D.S.sub kp).Msg × Wp)) (dw : D.S.Wit × Wp),
    Z.OK → T.sh.OK ∧ Hh.hd.Laws ∧
      T.sh.par.Hyp 4 2 1 (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16) ∧
      D.G.Fits ∧ D.G.C.ListAt 2 2 ∧
      (Hh.hd.foldD Sb sl Z A₀).Hyp
        (Hh.hd.link Sb sl Z A₀ (fun _ => Or.inl trivial) dw 4 1 (fun _ => 2) (fun _ => 16)
          (fun _ => 16) (fun _ => 16) 2) ∧
      (ldRunG D.G kp Sb sl Z St₀ E₀
          (T.sh.block Sb sl Z 4 1 (fun _ => 2) (fun _ => 16)
            (fun _ => 16) (fun _ => 16))).shape.length = 4

end Spec

namespace LdGToy

theorem ok : T.sh.OK := by
  obtain ⟨hC, -⟩ := ld_toy Bool
  obtain ⟨hZ, -⟩ := ld_toy (PCol 1 1 1)
  refine (ldStd_ok K P5 D T hC hZ ?_ ?_ ?_ (by decide)).1
  · rintro ⟨⟨o, _⟩, i⟩ b hb
    cases o
    · obtain rfl : corner i = b := Sum.inl.inj hb
      have h3 : ∀ i : Fin 3, T.ord (corner i) = some ⟨⟨.ord, trivial⟩, i⟩ :=
        fun i => by fin_cases i <;> rfl
      exact h3 i
    · cases hb
    · exact i.elim
  · rintro ⟨⟨o, _⟩, i⟩ j hj
    cases o
    · cases hj
    · rfl
    · exact i.elim
  · rintro ⟨⟨o, _⟩, i⟩
    cases o
    · rfl
    · exact i.elim
    · rfl

theorem held : Hh.hd.Laws := by
  refine ldStd_held K P5 D T kp Hh ?_
  rintro ⟨⟨o, ho⟩, _⟩ r
  obtain rfl : o = .kep := ho
  rfl

theorem hyp : T.sh.par.Hyp 4 2 1 (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16) := by
  obtain ⟨hC, hCD, -⟩ := ld_toy Bool
  obtain ⟨hZ, hZD, -, -, -, -, hzk, -, -⟩ := ld_toy (PCol 1 1 1)
  refine ldGroup_toy_hyp D T hC hCD hZ hZD hZ hZD (le_refl 2) (fun _ _ h => h) ?_ ?_ hzk
  · exact (ld_pack_ok_iff K P5 _).2
      (ld_pack_place K 1 1 2 _ _ (plc5 1 1) _ _ (plc5_inj 1 1) (ld_pack_law K 1 1 1))
  · exact ld_pack_deg_place K _ _ _ (plc5 1 1) (QwC 1 1 1) _ (ld_pack_deg K 1 1 1)

end LdGToy

open LdGToy in
theorem ldGroup_toy_shape : Spec.ldGroup_toy_shape := ⟨rfl, fun _ => rfl, by norm_num, rfl⟩

theorem ldGroup_toy_ev : Spec.ldGroup_toy_ev := by
  intro J _ _ _
  refine ⟨ok_indep K J, ?_⟩
  have h := lt_indep K J
  rw [ZMod.card] at h
  rw [← h]
  ring

open LdGToy in
open Classical in
theorem ldGroup_toy : Spec.ldGroup_toy := by
  intro B Kc St₀ Wp _ Sb sl Z E₀ A₀ dw hZ
  have hl : D.G.C.ListAt 2 2 := ldGroup_toy_list D T ok (ld_toy Bool).2.1 (ld_toy (PCol 1 1 1)).2.1
  refine ⟨ok, held, hyp, ldStd_fits K P5 D, hl, ?_, ?_⟩
  · exact ldGroup_seg K B Kc St₀ Wp D.S D.G T.sh kp Hh.hd Sb sl Z E₀ A₀ (fun _ => Or.inl trivial)
      dw 4 1 _ _ _ _ 2 ok held hyp hZ hl (ldStd_fits K P5 D)
  · exact (ldGroup_fold K B Kc St₀ Wp D.S D.G T.sh kp Sb sl Z 2 E₀ A₀
      (fun _ => Or.inl trivial) dw 4 1 _ _ _ _ (fun _ => True) (fun _ => True) ok hyp hZ hl
      (ldStd_fits K P5 D) fun _ _ => trivial).2

end Cb
