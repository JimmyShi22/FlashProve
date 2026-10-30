-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegClose.lean: the first half of a closing, as lists of moves: one group; two groups with
a split.

Definitions and statements (Cb.Spec.ldSegCl_*); the proofs are in Cb/Req1/LdSegCloseProofs.lean.
In standard terms: book-keeping for the moves that lead from many linear claims on oracle messages
to one linear claim on the message of a folded word, relaxed to words within a radius of an encoding
(`heldB`, Cb/Req1/LdSegKit.lean), for each group of oracle messages (`Grp`, Cb/Ld/LdBatSig.lean). A
row is a claim that a linear form of the messages' entries has a target value (`Slf.Holds`,
Cb/Ld/LdRel.lean); "many rows into one" puts in their place the one claim on their linear
combination, with the coefficients that a seed gives (`Slf.bat`, in the same file; `Evader`,
Cb/Gen/BatEvader.lean).
The first half of a closing is what a segment (`LdSeg`) has in its parts bat and fold; the data of
the second half are in Cb/Req1/LdSegFit.lean and Cb/Req1/LdSegFitTwo.lean.
It builds on Cb/Req1/LdSeg.lean and Cb/Req1/LdSegKit.lean (stages, moves, lists of moves),
Cb/Ld/LdBatSig.lean, Cb/Ld/LdSplit.lean (the blocks) and Cb/Ld/LdBatPeel.lean (steps without rounds
in which a claim is written in another form).

Why: the moves of a closing are stated each between its own two stages. Here they are put in a row,
with the steps without rounds that are between them, so that the composition typechecks from the
rows that a segment leaves to the stage with all tests open.

 1. One group (`LdCl1`). Rows on all entries, all of which vanish outside the group G; beside them
    A₀ of the kept messages.
      bat: many rows into one (one round).
      step: the one row, which vanishes outside G, is a row on the message of G (no round).
      fold: the bridge, the arrangement, the fold on G (l: their link, a parameter).
 2. Two groups (`LdCl2`, `LdCl2b`). Rows on all entries, all of which vanish outside G₁ and G₂; κ
    (the field `k`) an entry of an oracle message that is a member of both and that no row reads.
      bat: many rows into one.
      stepA: the one row is (its part on G₁) plus (the rest, on G₂).
      split: the prover sends one scalar: a row on G₁, a row on G₂.
      stepB: the row on G₂ goes inside the joint that the closing of G₁ carries. For that all
        members of G₂ are kept at the bridge of G₁ (kp₁).
      fold₁: bridge, arrangement, fold on G₁. Its test stays open.
      stepC: the row on G₂ comes out again, and the open test of G₁ goes inside the joint that the
        closing of G₂ carries. For that no member of G₂ is held in the folded word of G₁.
      fold₂: bridge, arrangement, fold on G₂, as a group of the oracle messages that are left.
    What else the statement claims (A₀, over any type M of "what is read of the messages"): it is
    read off the messages kept after G₁ by ρ, and, after the bridge of G₂, off the messages kept
    then and the slots of the first folded word by rd'; the one law (hρ) says that these are the
    same reading.

Main names:
  `Spec.ldSegCl_one`: the hypotheses of the list of moves of 1 (`D.prog l`) follow from: the
    evader's property; the rows vanish outside G; the hypotheses of the fold's move.
  `Spec.ldSegCl_two`: the same for 2 (`D.progBat`, `F.progFold l₁ l₂`): the evader's property
    (`D.Z.OK`); the rows vanish outside G₁ and G₂ and do not read κ; the entries read; members of G₂
    kept and not held; the law of the readings (the last four are `F.OK`); the hypotheses of the two
    folds' moves.
  `Spec.ldSegCl_kinds`: the kinds of the moves, for two groups: the first part holds bat, split and
    steps only, the second folds and steps only (as a segment asks: `LdSeg.batT`, `LdSeg.foldT`).

Limits: nothing new on errors: they are those of the moves. This file says nothing on more than two
groups (they would go by the same three steps: not stated here). The second half of a closing (one
sending, the locations) is not here.
The order of the moves restates this protocol's technical report in our own words
(lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSeg
import Cb.Ld.LdBatPeel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-- one claim as a family of claims with one name -/
def oneClaim {E St : Type} (x : E × St) : (Unit → E) × (Unit → St) := (fun _ => x.1, fun _ => x.2)

/-- a step without rounds between two stages over one signature, with the same further oracles and
the same further witness: only the explicit part without the samples is mapped -/
def ldStepF {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp : Type}
    {E₀ : ExtSpec} (A : IOR.Rels Kc St E₀ (S.Msg × Wp))
    (A' : IOR.Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') :
    LdMv (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀, Wp, A'⟩ :=
  .step _ _ (sideF S f) (sideG S (ExtMap.id E₀)) (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2)

/-! ## 1. One group -/

/-- One group closes: the data. -/
structure LdCl1 (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  /-- the rows that are left: forms on all entries -/
  B   : Type
  [finB : Fintype B]
  Sb  : B → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  Z   : Evader E B
  /-- the group, and what is kept -/
  G   : Grp S
  kp  : S.O → Prop
  [decKp : DecidablePred kp]
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)
  /-- the folded complex, its form, the joint radius; the kept messages that are held in it -/
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (S.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (S.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (S.om k.1.1).C.Q → Cf.Q

attribute [instance] LdCl1.finB LdCl1.decKp LdCl1.finPf LdCl1.decCl

namespace LdCl1
variable {E Kc : Type} [Field E] [Fintype E] (D : LdCl1 E Kc)

/-- the state of the one row -/
abbrev Sx : Type := (∀ b, D.Sb b) × D.Z.D
/-- the one row -/
abbrev row : Slf E D.Sx D.S.Ent := Slf.bat D.Z.ze D.sl

@[reducible] def bat : LdBatD E Kc :=
  { S := D.S, B := D.B, Sb := D.Sb, sl := D.sl, Z := D.Z, St₀ := D.St₀, Wp := D.Wp, E₀ := D.E₀,
    A₀ := onMsgRels (D.S.res (T := OMsg.Msg) D.kp) D.A₀ }

@[reducible] def fold : LdFoldD E Kc :=
  { S := D.S, G := D.G, kp := D.kp, B := Unit, Sb := fun _ => D.Sx, sl := fun _ => D.row.onG D.G,
    St₀ := D.St₀, Wp := D.Wp, E₀ := D.E₀, A₀ := D.A₀, Pf := D.Pf, Cf := D.Cf, Stf := D.Stf,
    slf := D.slf, e := D.e, cl := D.cl, sW := D.sW, sJ := D.sJ, sQ := D.sQ }

/-- the step: the one row is a row on the group -/
def step : LdMv D.bat.tgt D.fold.src :=
  ldStepF D.S D.bat.tgt.A D.fold.src.A fun st => (oneClaim st.1, st.2)

/-- The list of moves. -/
def prog (l : IOR.Link Kc D.fold.src.J D.fold.mid) : LdProg D.bat.src D.fold.tgt :=
  .snoc (.snoc (.snoc (.nil _) (.bat D.bat)) D.step) (.fold D.fold l)

end LdCl1


/-! ## 2. Two groups -/

/-- Two groups close, first part: the data up to the fold on the first group. -/
structure LdCl2 (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  /-- the rows that are left: forms on all entries -/
  B   : Type
  [finB : Fintype B]
  Sb  : B → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  Z   : Evader E B
  /-- the two groups, the mask entry, the entries that the split reads -/
  G₁  : Grp S
  G₂  : Grp S
  k   : SplitAt G₁ G₂
  Rd  : S.Ent → Prop
  [decRd : DecidablePred Rd]
  /-- what is kept at the bridge of the first group -/
  kp₁ : S.O → Prop
  [decKp₁ : DecidablePred kp₁]
  /-- what else is claimed: of "what is read of the messages" -/
  M   : Type
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ (M × Wp)
  ρ   : (S.sub kp₁).Msg → M
  /-- the first folded complex -/
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp₁ o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (S.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (S.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (S.om k.1.1).C.Q → Cf.Q

attribute [instance] LdCl2.finB LdCl2.decRd LdCl2.decKp₁ LdCl2.finPf LdCl2.decCl

namespace LdCl2
variable {E Kc : Type} [Field E] [Fintype E] (D : LdCl2 E Kc)

abbrev Sx : Type := (∀ b, D.Sb b) × D.Z.D
abbrev row : Slf E D.Sx D.S.Ent := Slf.bat D.Z.ze D.sl
/-- the part of the one row on the first group; the rest, on the second -/
abbrev sl₁ : Slf E D.Sx D.G₁.C.J := D.row.onG D.G₁
abbrev sl₂ : Slf E D.Sx D.G₂.C.J := (D.row.offG D.G₁).onG D.G₂
/-- the two rows after the split -/
abbrev r₁ : Slf E D.Sx D.G₁.C.J := D.sl₁.addAt 1 D.k.e₁
abbrev r₂ : Slf E D.Sx D.G₂.C.J := D.sl₂.addAt (-1) D.k.e₂

/-- what else is claimed, read off all messages -/
abbrev As : IOR.Rels Kc D.St₀ D.E₀ (D.S.Msg × D.Wp) :=
  onMsgRels (fun m => D.ρ (D.S.res (T := OMsg.Msg) D.kp₁ m)) D.A₀

@[reducible] def bat : LdBatD E Kc :=
  { S := D.S, B := D.B, Sb := D.Sb, sl := D.sl, Z := D.Z, St₀ := D.St₀, Wp := D.Wp,
    E₀ := D.E₀, A₀ := D.As }

@[reducible] def spl : LdSplD E Kc :=
  { S := D.S, G₁ := D.G₁, G₂ := D.G₂, k := D.k, St₁ := D.Sx, St₂ := D.Sx, sl₁ := D.sl₁,
    sl₂ := D.sl₂, St₀ := D.St₀, Wp := D.Wp, E₀ := D.E₀, A₀ := D.As, Rd := D.Rd }

/-- a claim with one name, and its state -/
abbrev Cl : Type := (Unit → E) × (Unit → D.Sx)

/-- What the closing of the first group carries: the row on the second group, and what else is
claimed. -/
abbrev A₁ : IOR.Rels Kc (D.Cl × D.St₀) D.E₀ ((D.S.sub D.kp₁).Msg × D.Wp) :=
  claimRels (fun x m => Slf.All (fun _ : Unit => D.r₂.toSub D.kp₁) x ((D.G₂.sub D.kp₁).msg m))
    (onMsgRels D.ρ D.A₀)

@[reducible] def fold₁ : LdFoldD E Kc :=
  { S := D.S, G := D.G₁, kp := D.kp₁, B := Unit, Sb := fun _ => D.Sx, sl := fun _ => D.r₁,
    St₀ := D.Cl × D.St₀, Wp := D.Wp, E₀ := D.E₀, A₀ := D.A₁, Pf := D.Pf, Cf := D.Cf, Stf := D.Stf,
    slf := D.slf, e := D.e, cl := D.cl, sW := D.sW, sJ := D.sJ, sQ := D.sQ }

/-- stepA: the one row is a part on G₁ plus a part on G₂ -/
def stepA : LdMv D.bat.tgt D.spl.src :=
  ldStepF D.S D.bat.tgt.A D.spl.src.A fun st => ((st.1.1, (st.1.2, st.1.2)), st.2)

/-- stepB: the row on G₂ goes inside what the closing of G₁ carries -/
def stepB : LdMv D.spl.tgt D.fold₁.src :=
  ldStepF D.S D.spl.tgt.A D.fold₁.src.A fun st => (oneClaim st.1.1, (oneClaim st.1.2, st.2))

/-- The list of moves: before the folds. -/
def progBat : LdProg D.bat.src D.fold₁.src :=
  .snoc (.snoc (.snoc (.snoc (.nil _) (.bat D.bat)) D.stepA) (.split D.spl)) D.stepB

/-- the oracle messages that are left after the first fold; the second group among them; its row -/
abbrev S₂ : Sig E := D.fold₁.S₂
abbrev G₂' : Grp D.S₂ := (D.G₂.sub D.kp₁).sub fun a => ¬ D.cl a
abbrev r₂' : Slf E D.Sx D.G₂'.C.J := (D.r₂.toSub D.kp₁).toSub fun a => ¬ D.cl a

end LdCl2

/-- Two groups close, second part: the data of the fold on the second group. -/
structure LdCl2b {E Kc : Type} [Field E] [Fintype E] (D : LdCl2 E Kc) : Type 1 where
  /-- what is kept at the bridge of the second group -/
  kp₂ : D.S₂.O → Prop
  [decKp₂ : DecidablePred kp₂]
  /-- what else is claimed is read off the messages kept then and the slots of the first folded
  word -/
  rd' : (D.S₂.sub kp₂).Msg → (∀ k, (D.fold₁.held.o k).Msg) → D.M
  /-- the second folded complex -/
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp₂ o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (D.S₂.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (D.S₂.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (D.S₂.om k.1.1).C.Q → Cf.Q

attribute [instance] LdCl2b.decKp₂ LdCl2b.finPf LdCl2b.decCl

namespace LdCl2b
variable {E Kc : Type} [Field E] [Fintype E] {D : LdCl2 E Kc} (F : LdCl2b D)

/-- What the closing of the second group carries: the open test of the first group, and what else is
claimed. -/
abbrev A₂ :
    IOR.Rels Kc (((E × D.Stf) × D.fold₁.held.Smp) × D.St₀) (D.Cf.ext.prod D.E₀)
      ((D.S₂.sub F.kp₂).Msg × (D.Cf.N.Wit × D.Wp)) :=
  heldB D.Cf D.e D.fold₁.held D.slf.Holds F.rd' D.A₀

@[reducible] def fold₂ : LdFoldD E Kc :=
  { S := D.S₂, G := D.G₂', kp := F.kp₂, B := Unit, Sb := fun _ => D.Sx, sl := fun _ => D.r₂',
    St₀ := ((E × D.Stf) × D.fold₁.held.Smp) × D.St₀, Wp := D.Cf.N.Wit × D.Wp,
    E₀ := D.Cf.ext.prod D.E₀, A₀ := F.A₂, Pf := F.Pf, Cf := F.Cf, Stf := F.Stf, slf := F.slf,
    e := F.e, cl := F.cl, sW := F.sW, sJ := F.sJ, sQ := F.sQ }

/-- stepC: the row on G₂ comes out; the open test of G₁ goes inside what the closing of G₂
carries -/
def stepC : LdMv D.fold₁.tgt F.fold₂.src :=
  ldStepF D.S₂ D.fold₁.tgt.A F.fold₂.src.A fun st => (st.2.1, (st.1, st.2.2))

/-- The list of moves: the folds. -/
def progFold (l₁ : IOR.Link Kc D.fold₁.src.J D.fold₁.mid)
    (l₂ : IOR.Link Kc F.fold₂.src.J F.fold₂.mid) :
    LdProg D.fold₁.src F.fold₂.tgt :=
  .snoc (.snoc (.snoc (.nil _) (.fold D.fold₁ l₁)) F.stepC) (.fold F.fold₂ l₂)

/-- What is asked of the data. -/
structure OK : Prop where
  /-- the rows vanish outside the two groups, and do not read the mask entry -/
  supp : ∀ b st (n : D.S.Ent), ¬ D.G₁.mem n.1 → ¬ D.G₂.mem n.1 → D.sl b st n = 0
  own  : ∀ b st, D.sl b st ⟨D.k.o, D.k.j⟩ = 0
  /-- the entries that the split reads -/
  rd   : ∀ b st (n : D.S.Ent), ¬ D.Rd n → D.sl b st n = 0
  rdK  : D.Rd ⟨D.k.o, D.k.j⟩
  /-- all members of the second group are kept at the bridge of the first, and none is held in the
  first folded word -/
  kept : ∀ o, D.G₂.mem o → D.kp₁ o
  free : ∀ a : {o // D.kp₁ o}, D.G₂.mem a.1 → ¬ D.cl a
  /-- the two readings of "what else is claimed" are one -/
  hρ   : ∀ (m : D.S₂.Msg) (u : ∀ k, (D.fold₁.held.o k).Msg),
    D.ρ (D.fold₁.rd m u) = F.rd' (D.S₂.res (T := OMsg.Msg) F.kp₂ m) u

end LdCl2b

namespace Spec

def ldSegCl_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdCl1 E Kc) (l : IOR.Link Kc D.fold.src.J D.fold.mid),
    D.Z.OK → (∀ b st (n : D.S.Ent), ¬ D.G.mem n.1 → D.sl b st n = 0) → D.fold.Hyp l → (D.prog l).Hyp

def ldSegCl_two : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdCl2 E Kc) (F : LdCl2b D)
      (l₁ : IOR.Link Kc D.fold₁.src.J D.fold₁.mid) (l₂ : IOR.Link Kc F.fold₂.src.J F.fold₂.mid),
    D.Z.OK → F.OK → D.fold₁.Hyp l₁ → F.fold₂.Hyp l₂ → D.progBat.Hyp ∧ (F.progFold l₁ l₂).Hyp

/-- The kinds of the moves are those that a segment allows in its parts "bat" and "fold". -/
def ldSegCl_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdCl2 E Kc) (F : LdCl2b D)
      (l₁ : IOR.Link Kc D.fold₁.src.J D.fold₁.mid) (l₂ : IOR.Link Kc F.fold₂.src.J F.fold₂.mid),
    (D.progBat.All fun t => t = .bat ∨ t = .split ∨ t = .step) ∧
    ((F.progFold l₁ l₂).All fun t => t = .fold ∨ t = .step)

end Spec
end Cb
