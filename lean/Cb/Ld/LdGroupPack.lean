-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupPack.lean: this file is for toys (a toy: a small example instance). Book-keeping: one
record (a bundle) that holds the oracle messages tested together (a group), the way they are
arranged for the sumcheck that folds them, the new oracle messages of the closing's one sending, and
proofs of the conditions on these data that the theorems on these steps ask; from it, the whole
composed reduction (a segment), with its hypotheses under the premises of `gPack_seg1`.

Definitions, statements as theorems, proofs. Generic.

Why a bundle: the signature at the end of a segment's body is a sum of families. Its member at a
variable name does not reduce, even if all members are copies of one oracle message; so a shape
cannot be written over it directly. It can be written over the constant signature with the same
names, and carried over along the equation of the two families of members, if data and facts travel
together.

Main names:
  `GPack S mem kp clP Pn` (numbers: see "Notation"): memI: the members are those with mem; clI: the
    held ones are those with clP; eI: the group's radius is e; hc: member or kept; ok, held, hyp,
    list, fits, new, cf: proofs of `Sh.OK`, `Hd.Laws`, `Sh.par.Hyp d G.e t Lst mC mS mW`,
    `G.C.ListAt G.e L`, `G.Fits`, `V.OK L₂ t₂`, `Sh.Cf.Laws`.
  `GPack.cast h pk`: the bundle carried over (see "Why a bundle").
  `pk.fold`, `pk.link`, `gPack_fold`: bridge-to-fold for any rows on the group, any evader that
    evades, any carried joint: its hypotheses (Cb/Ld/LdGroupSeg.lean).
  `pk.close`, `gPack_snd`: the second half: the seven hypotheses of the one sending
    (Cb/Ld/LdGroupNewStd.lean).
  `pk.seg1 .. body ..`, `gPack_seg1`: the segment with all five parts (Cb/Req1/LdSegWhole.lean:
    `segOne`).

Notation: `d`, `e`, `t`, `L`, `L₂`, `t₂`: natural numbers; `Lst`, `mC`, `mS`, `mW`: functions ℕ → ℕ.
They are bare parameters; the record's fields alone tie them: `eI : G.e = e`;
`hyp : Sh.par.Hyp d G.e t Lst mC mS mW`; `list : G.C.ListAt G.e L`; `new : V.OK L₂ t₂`. (What `d`,
`t`, `Lst`, `mC`, `mS`, `mW` are to the fold: the doc comment of `GShape.block`,
Cb/Ld/LdGroupFold.lean.)

Limits: this file does not say that a bundle exists. It says nothing on formats:
Cb/Ld/LdGroupNewFmt.lean has those of bridge-to-fold, sending, locations; Cb/Ld/LdGroupPackFmt.lean
that of `pk.seg1` (`gPack_seg1_fmt`, under its hypotheses).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupSolo
import Cb.Ld.LdGroupNewFmt
import Cb.Ld.LdGroupNewRows
import Cb.Req1.LdSegWhole
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- A group with all that a closing needs, in one bundle. -/
structure GPack {E : Type} [Field E] [Fintype E] (S : Sig E) (mem kp : S.O → Prop)
    [DecidablePred kp] (clP : {o // kp o} → Prop) (Pn : Type) [Fintype Pn] (d e t : ℕ)
    (Lst mC mS mW : ℕ → ℕ) (L L₂ t₂ : ℕ) where
  G    : Grp S
  [neP : Nonempty G.P]
  Sh   : GShape G
  Hd   : GHeld Sh kp
  V    : StdNew Hd Pn
  memI : ∀ o, G.mem o ↔ mem o
  clI  : ∀ a, Hd.cl a ↔ clP a
  eI   : G.e = e
  hc   : ∀ o, G.mem o ∨ kp o
  ok   : Sh.OK
  held : Hd.Laws
  hyp  : Sh.par.Hyp d G.e t Lst mC mS mW
  list : G.C.ListAt G.e L
  fits : G.Fits
  new  : V.OK L₂ t₂
  cf   : Sh.Cf.Laws

attribute [instance] GPack.neP

/-- The bundle goes over to a signature with the same names whose members are the same oracle
messages, one by one. -/
def GPack.cast {E : Type} [Field E] [Fintype E] {I : Type} [Fintype I] [DecidableEq I]
    {om om' : I → OMsg E} (h : om = om') {mem kp : I → Prop} [DecidablePred kp]
    {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ}
    {L L₂ t₂ : ℕ}
    (pk : GPack (S := { O := I, om := om }) mem kp clP Pn d e t Lst mC mS mW L L₂ t₂) :
    GPack (S := { O := I, om := om' }) mem kp clP Pn d e t Lst mC mS mW L L₂ t₂ := h ▸ pk

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {mem kp : S.O → Prop}
  [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ}
  {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ} (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) pk.G.C.J) (Z : Evader E (pk.G.Row B)) {St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (dw : S.Wit × Wp)

/-- bridge-to-fold: the data, the link -/
@[reducible] def GPack.fold : LdFoldD E Kc := pk.Hd.foldD Sb sl Z A₀
@[reducible] def GPack.link :
    Link Kc (pk.fold Sb sl Z A₀).src.J (pk.fold Sb sl Z A₀).mid :=
  pk.Hd.link Sb sl Z A₀ pk.hc dw d t Lst mC mS mW L

open Classical in
theorem gPack_fold (hZ : Z.OK) : (pk.fold Sb sl Z A₀).Hyp (pk.link Sb sl Z A₀ dw) :=
  ldGroup_seg E B Kc St₀ Wp S pk.G pk.Sh kp pk.Hd Sb sl Z E₀ A₀ pk.hc dw d t Lst mC mS mW L pk.ok
    pk.held pk.hyp hZ pk.list pk.fits

variable (w0 : (pk.fold Sb sl Z A₀).tgt.S.Wit × (pk.fold Sb sl Z A₀).tgt.Wp) (tl : ℕ)

/-- the second half of the closing -/
@[reducible] def GPack.close : LdCloseD (pk.fold Sb sl Z A₀) :=
  pk.V.close Sb sl Z A₀ w0 L₂ t₂ tl

theorem gPack_snd : (pk.close Sb sl Z A₀ w0 tl).snd.Hyp := stdNew_snd pk.V Sb sl Z A₀ w0 tl pk.new

end

/-! ## A closing with a batching in front -/

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {mem kp : S.O → Prop}
  [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ}
  {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ} (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B) (Zb : Evader E (pk.G.Row Unit))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))

/-- the state of the one row; the one row, on the group -/
abbrev GPack.Sx : Type := (∀ b, Sb b) × Z.D
abbrev GPack.row1 : ∀ _ : Unit, Slf E (GPack.Sx Sb Z) pk.G.C.J := fun _ =>
  (Slf.bat Z.ze sl).onG pk.G

/-- The data of a closing with one group (Cb/Req1/LdSegClose.lean): many rows on all entries into
one; the one row is a row on the group; bridge-to-fold. -/
@[reducible] def GPack.cl1 : LdCl1 E Kc where
  S := S
  B := B
  Sb := Sb
  sl := sl
  Z := Z
  G := pk.G
  kp := kp
  St₀ := St₀
  Wp := Wp
  E₀ := E₀
  A₀ := A₀
  Pf := pk.G.P
  Cf := pk.Sh.Cf
  Stf := ((pk.Sh.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb).jOut pk.G.e).St
  slf := (pk.Sh.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb).slOut
  e := pk.G.e
  cl := pk.Hd.cl
  sW := pk.Hd.sW
  sJ := pk.Hd.sJ
  sQ := pk.Hd.sQ

/-- its bridge-to-fold is the bundle's, by definition -/
theorem gPack_cl1_fold :
    (pk.cl1 Sb sl Z Zb A₀).fold = pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ :=
  rfl

variable {a : LdStage E Kc} (body : LdProg a (pk.cl1 Sb sl Z Zb A₀).bat.src)
  (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step) (dw : S.Wit × Wp)
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp) (tl : ℕ)

/-- The segment: any body; many rows into one; the step; bridge-to-fold; the one sending; the
locations. -/
def GPack.seg1 :
    LdSeg a (pk.close (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ w0 tl).loc.tgt :=
  segOne (pk.cl1 Sb sl Z Zb A₀) body hT
    (pk.link (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ dw)
    (pk.close (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ w0 tl)

/-- Its hypotheses, for a body whose moves are sendings, sub-protocols or steps (`hT`), from: the
body's; the two evaders evade; the rows vanish outside the members. -/
theorem gPack_seg1 (hb : body.Hyp) (hZ : Z.OK) (hZb : Zb.OK)
    (hs : ∀ b st (n : S.Ent), ¬ mem n.1 → sl b st n = 0) :
    (pk.seg1 Sb sl Z Zb A₀ body hT dw w0 tl).Hyp :=
  ldSegWhole_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ hb hZ
    (fun b st n hn => hs b st n fun h => hn ((pk.memI n.1).2 h))
    (gPack_fold pk _ _ Zb A₀ dw hZb) (gPack_snd pk _ _ Zb A₀ w0 tl)

end
end Cb
