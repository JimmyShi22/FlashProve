-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqProtoStd.lean: the protocol's side of the reference request (`LdReqProtoS`): every
sender but those of `more` the standard sender, every link bridge-to-fold the group's own.

Among the parameters of the chain of reductions of the reference request are the honest prover of
each sending and the reduction bridge-to-fold of each closing. This file states, as hypotheses, that
they are definite terms (but for the sendings in `more`), and derives the hypotheses on them from
the conditions of `IsStd` and `IsGrp`.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: an assembly.
The protocol's side is the record `LdReqProto` (Cb/Req1/LdReqModel.lean) of conditions on the parts
of the reference request `ldReqRef` (Cb/Req1/LdReqRef.lean): its list L of segments S, its last
segment T, their bodies A (`LdRefD`, Cb/Req1/LdSegRefAll.lean). d is a sending (`LdSendD a`);
`D : LdFoldD E Kc` with `l : Link Kc D.src.J D.mid` is a move "fold" (Cb/Req1/LdSegKit.lean; `Link`:
Ior/KnowCollRulesChain.lean).
The hypotheses on them (`d.Hyp`, `D.Hyp l`) are theorems, under the conditions below, for two terms:
Cb/Obj/LdObjectSenders.lean (the standard sender of a family, from a layout of its messages into
data, free entries and pads), Cb/Ld/LdGroupSeg.lean (the link of a group with a shape and a choice
of kept messages).

Main names:
  `d.IsStd F`: one equation that says which term d is (`d = LdSendD.std ..`: a hypothesis, as the
    equations of Cb/Obj/LdObjectData.lean), and the hypotheses: the layout (`Y.OK t`: `enc`, `lay`,
    `priv`, `hides`); the extractor undoes what the sender reads; the codes' laws; fair seeds;
    lists; evading samples.
  `D.IsGrp l`: the same for a move "fold": `(D, l) = (Hd.foldD .., Hd.link ..)`, and: `Fintype D.B`;
    `Nonempty D.G.P`; `∀ o, D.G.mem o ∨ D.kp o`; the shape's and the kept messages' laws; the fold's
    parameters; the bridge's evader; the list of the group's complex; `Fits`. (not all hypotheses
    are named here: see `LdFoldD.IsGrp`)
  `Spec.ldReqProtoStd_send`, `Spec.ldReqProtoStd_fold`: these give `d.Hyp`, `D.Hyp l`.
  `Spec.ldReqProtoStd_selfSend`, `Spec.ldReqProtoStd_selfFold`: see their statements.
  `A.ProtoS F pp`, `S.ProtoS F pp`, `L.ProtoS F pp`, `LdReqProtoS F pp R first more L T`:
    Cb/Req1/LdReqModel.lean's "Proto" with `IsStd` and `IsGrp` in place of the hypotheses on senders
    and links, but for `more.Hyp`.
  `Spec.ldReqProtoStd`: `LdReqProtoS .. → LdReqProto ..`.

Why the pads' field is a parameter of its own (the first argument of `IsStd`, `ProtoS`,
`LdReqProtoS`): it need not be the configuration's base field: an oracle message over E, and every
message that holds mask rows, has one pad entry of E for each answer (by type the number is free:
`Sig.StdL.Pd Y a`, Cb/Ld/LdSendStdL.lean, is any finite type, so the type fixes no number); pads in
a subfield belong to messages all of whose rows are over that subfield.

Under `IsGrp`, in a segment's closing the link bridge-to-fold is a term: the bridge with its evader,
the arrangement of the rows (no round), one zero-knowledge sumcheck that folds all variables. What
is asked of it are the hypotheses of `LdFoldD.IsGrp`: laws and distances of three codes, bounds on
their lists and on their correlated agreement at the radius, an injective map of challenges, degree
at least 2, the two laws of the packing, a fresh mask whose code hides t positions, the laws of the
arrangement and of the kept slots. (not all hypotheses are named here: see `LdFoldD.IsGrp`) No tower
and no tail of a test stands there: the folded word stays open and is closed by the one sending and
the locations.

Limits: the bounds on lists and on correlated agreement are properties of codes, asked, not derived
from parameters of a code here. What still speaks of more than data: `more.Hyp` (the list of further
first sendings and steps, as it is); and, inside `IsStd` and `IsGrp`: `Y.OK t` (`priv`, `hides`),
`ListLE`, `Evades`, `Sh.par.Hyp` (`errs`, `zk`), `ListAt`; the evaders' `OK`. This file says nothing
on "does not look" and "Fresh" of the senders (zero knowledge: Cb/Req1/LdReqRefLay.lean), and
nothing on format and errors of the links. This file gives no instance that meets its hypotheses, so
as far as this file shows its theorems may hold of nothing.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqModel
import Cb.Obj.LdObjectSenders
import Cb.Ld.LdGroupSegProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

section
variable (F : Type) {E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The sending is the standard one. -/
def LdSendD.IsStd {a : LdStage E Kc} (d : LdSendD a) : Prop :=
  ∃ (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 ∧
    Y.OK d.t ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧
    (∀ i, (d.N.om i).C.Laws) ∧
    d.Sd.Fair ∧
    (∀ i, (d.N.om i).ListLE (d.L i)) ∧
    ∀ i, (d.N.om i).Evades

end

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The move "fold" is the group's own. -/
def LdFoldD.IsGrp (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) : Prop :=
  ∃ (_ : Fintype D.B) (_ : Nonempty D.G.P) (Sh : GShape D.G) (Hd : GHeld Sh D.kp)
      (Z : Evader E (D.G.Row D.B)) (hc : ∀ o, D.G.mem o ∨ D.kp o) (dw : D.S.Wit × D.Wp) (d t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (L : ℕ),
    (⟨D, l⟩ : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) =
      ⟨Hd.foldD D.Sb D.sl Z D.A₀, Hd.link D.Sb D.sl Z D.A₀ hc dw d t Lst mC mS mW L⟩ ∧
    Sh.OK ∧ Hd.Laws ∧
    Sh.par.Hyp d D.G.e t Lst mC mS mW ∧
    Z.OK ∧
    D.G.C.ListAt D.G.e L ∧
    D.G.Fits

end

section
variable (F : Type) {E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

structure LdRefD.ProtoS {I : LdRefIx E} (A : LdRefD E Kc I) (pp : ℕ) : Prop where
  front  : A.V.Proto pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : A.Xa.Q.D.d1.IsStd F
  send3  : A.Xa.Q.D.d3.IsStd F
  tabQ   : A.Xa.Q.D.p.q ≤ 2 ^ A.Xa.Q.d
  tabH   : A.Xa.Q.D.p.H ≤ 2 ^ A.Xa.Q.d
  keys   : A.Xa.Q.K ≤ 2 ^ A.Xa.Q.v
  tags   : A.Xa.Q.tag 0 ≠ A.Xa.Q.tag 1
  inj    : Function.Injective A.Xa.ι
  named  : A.Xa.A.PlacesIn (fun j => j ∈ Set.range A.Xa.ι)
  adm    : A.Xa.A.H.lkb.Adm pp
  bits   : A.Xa.Bits
  reads  : A.Gr.Reads
  deg    : 2 ≤ A.nt
  ev     : A.Zt.OK

structure LdRefS.ProtoS {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (pp : ℕ) :
    Prop where
  body  : S.A.ProtoS F pp
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : S.K.R.c1.fold.IsGrp S.l
  snd   : S.Qc.snd.IsStd F

def LdRefL.ProtoS {I : LdRefIx E} {a : LdStage E Kc} (pp : ℕ) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.ProtoS pp ∧ S.ProtoS F pp

end

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The protocol's side, with `IsStd` and `IsGrp` in place of the hypotheses on senders and
links, but for `more.Hyp`. -/
structure LdReqProtoS (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (pp : ℕ) (R : LdORE F E Kc)
    {a a₁ b : LdStage E Kc} (first : LdSendD a) (more : LdProg first.tgt a₁)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : Prop where
  hFirst : first.IsStd Fp
  hMore  : more.Hyp
  segs   : L.ProtoS Fp pp
  tail   : T.A.ProtoS Fp pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie

end

namespace Spec

def ldReqProtoStd_send : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (a : LdStage E Kc) (d : LdSendD a),
    d.IsStd F → d.Hyp

def ldReqProtoStd_fold : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid),
    D.IsGrp l → D.Hyp l

/-- The two equations can be met: the two terms, `LdSendD.std ..` and `(Hd.foldD .., Hd.link ..)`,
meet them by definition. -/
def ldReqProtoStd_selfSend : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (a : LdStage E Kc)
      (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    Y.OK t → (∀ w, bk₀ (dat w) (rst w.2) = w.2) → (∀ i, (N.om i).C.Laws) → Sd.Fair →
    (∀ i, (N.om i).ListLE (L i)) → (∀ i, (N.om i).Evades) →
    (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).IsStd F

def ldReqProtoStd_selfFold : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ),
    Sh.OK → Hd.Laws → Sh.par.Hyp d G.e t Lst mC mS mW → Z.OK → G.C.ListAt G.e L → G.Fits →
    (Hd.foldD Sb sl Z A₀).IsGrp (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L)

def ldReqProtoStd_list : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (I : LdRefIx E)
      (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    L.ProtoS F pp → L.Proto pp

def ldReqProtoStd : Prop :=
  ∀ (Fp F E Kc : Type) [Field Fp] [Fintype Fp] [Field F] [Fintype F] [Field E] [Fintype E]
      [Algebra Fp E] [Algebra F E] (pp : ℕ) (R : LdORE F E Kc) (a a₁ b : LdStage E Kc)
      (first : LdSendD a) (more : LdProg first.tgt a₁) (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b),
    LdReqProtoS Fp pp R first more L T → LdReqProto pp R first more L T

end Spec

theorem ldReqProtoStd_send : Spec.ldReqProtoStd_send := by
  intro F E Kc _ _ _ _ _ a d ⟨Y, dat, rst, bk₀, w0, e, h1, h2, h3, h4, h5, h6⟩
  rw [e]
  exact ldSendD_std F E Kc a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 h1 h2 h3 h4 h5 h6

/-- The move's hypotheses pass along an equation of pairs. -/
theorem ldFoldD_at {E Kc : Type} [Field E] [Fintype E]
    (x x' : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) (e : x = x') (h : x'.1.Hyp x'.2) :
    x.1.Hyp x.2 := e ▸ h

theorem ldReqProtoStd_fold : Spec.ldReqProtoStd_fold := by
  intro E Kc _ _ D l ⟨_, _, Sh, Hd, Z, hc, dw, d, t, Lst, mC, mS, mW, L, e, h1, h2, h3, h4, h5, h6⟩
  exact ldFoldD_at ⟨D, l⟩ _ e
    (ldGroup_seg E D.B Kc D.St₀ D.Wp D.S D.G Sh D.kp Hd D.Sb D.sl Z D.E₀ D.A₀ hc dw d t Lst mC
      mS mW L h1 h2 h3 h4 h5 h6)

theorem ldReqProtoStd_selfSend : Spec.ldReqProtoStd_selfSend :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y dat rst bk₀ w0 h1 h2 h3 h4 h5 h6 =>
    ⟨Y, dat, rst, bk₀, w0, rfl, h1, h2, h3, h4, h5, h6⟩

theorem ldReqProtoStd_selfFold : Spec.ldReqProtoStd_selfFold := fun _ _ _ _ _ _ _ iB _ _ iP Sh _ _ Hd _ _ Z _ _ hc dw d t Lst mC mS mW L h1 h2 h3 h4 h5 h6 =>
  ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, Lst, mC, mS, mW, L, rfl, h1, h2, h3, h4, h5, h6⟩

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem LdRefD.ProtoS.toProto {I : LdRefIx E} {A : LdRefD E Kc I} {pp : ℕ} (h : A.ProtoS F pp) :
    A.Proto pp :=
  ⟨h.front, h.ok, h.places, h.uniq, ldReqProtoStd_send F E Kc _ _ h.send1,
    ldReqProtoStd_send F E Kc _ _ h.send3, h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm,
    h.bits, h.reads, h.deg, h.ev⟩

theorem LdRefS.ProtoS.toProto
    {I : LdRefIx E} {a : LdStage E Kc} {S : LdRefS E Kc I a} {pp : ℕ} (h : S.ProtoS F pp) :
    S.Proto pp :=
  ⟨h.body.toProto, h.ev, h.named, ldReqProtoStd_fold E Kc _ _ h.fold,
    ldReqProtoStd_send F E Kc _ _ h.snd⟩

end

theorem ldReqProtoStd_list : Spec.ldReqProtoStd_list := by
  intro F E Kc _ _ _ _ _ I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.Proto]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.ProtoS] at h
      rw [LdRefL.Proto]
      exact ⟨ih h.1, h.2.toProto⟩

theorem ldReqProtoStd : Spec.ldReqProtoStd := fun Fp _ E Kc _ _ _ _ _ _ _ _ pp _ _ _ _ _ _ L _ h =>
  ⟨ldReqProtoStd_send Fp E Kc _ _ h.hFirst, h.hMore, ldReqProtoStd_list Fp E Kc _ _ _ L pp h.segs,
    h.tail.toProto, h.deg, h.ev, h.tie⟩

end Cb
