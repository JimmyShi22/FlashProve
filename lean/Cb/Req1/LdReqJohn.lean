-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqJohn.lean: the protocol's side of the reference request below the Johnson radius: no
hypothesis on a list, none on "two members of one list agree at few seeds"; agreement is asked of
the three codes of each closing's shape, "whatever the number of rows", and nowhere else.

Oracle messages may be tested at a radius beyond unique decoding; the record of the reference
request has hypotheses on the sizes of lists and on correlated agreement. Below the Johnson radius
the bound on lists is a theorem, from the code's laws and distance; this file puts it in the place
of the hypotheses on lists.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: an assembly of
Cb/Ld/LdRelJohnson.lean, Cb/Ld/LdSig.lean, Cb/Ld/LdWfThird.lean, Cb/Ld/LdGroupJohn.lean on
Cb/Req1/LdReqStdAny.lean. Generic: any finite field, any codes read under a transformation. No
assumed theorem. No soundness theorem of its own.
Oracle messages o: `OMsg` (Cb/Ld/LdSig.lean). In `d.IsStd`, `d.IsStdJ`, `d.IsStdAny` d is a sending
(`LdSendD a`), elsewhere a distance; `D : LdFoldD E Kc` with `l : Link Kc D.src.J D.mid` is a move
"fold" (Cb/Req1/LdSegKit.lean; `Link`: Ior/KnowCollRulesChain.lean); S, T, A are a segment, the last
segment and a body of the reference request (Cb/Req1/LdReqRef.lean, Cb/Req1/LdSegRefAll.lean); L is
the list of segments in `L.ProtoJ` and `LdReqRefDJ`, elsewhere the bound on lists. Below the Johnson
radius: `InJohnson n d e`, for n positions, distance d, radius e, with the bound `listMax n d e` on
lists (Cb/Gen/JohnsonList.lean). Agreement: `C.MCArows e b` (Cb/Ld/LdRelRows.lean): every
interleaving of C has mutual correlated agreement on lines under the transformation, at the radius
e, with at most b exceptional coefficients (`MCAat`, Cb/Ld/LdRel.lean).

Where the record of the reference request (Cb/Req1/LdReqStdAny.lean: `LdReqRefDSA`, its clause
"std") speaks of lists, agreement or list members: at two kinds of places only.
  (a) Every sending (the first one; the two of each body; the one sending of each closing):
      `d.IsStd` asks, of each oracle message sent, a bound on its lists at its own radius, and
      "evades": two different members of one list have the same answers at few seeds.
  (b) Every closing's link bridge-to-fold: `D.IsGrp l` asks the fold's own hypotheses (lists at its
      stages; agreement of three codes) and a bound on the lists of the group's complex.
A segment has no other group: the last segment has no closing; its rows go to the batch test.

Main names:
  `o.Half d L`: an oracle message within unique decoding: laws, distance d as read, 2 e below d, the
    bound is 1. None of these names its sample. (No
    difference from this protocol's technical report (lean/CREDITS.md) is declared here; for leaving
    a sample out that report follows the paper that this protocol builds on.)
  `o.John d L`: an oracle message over E below the Johnson radius: laws, distance d as read,
    `InJohnson |P| d e`, the bound is `listMax |P| d e`, and its sample is a zero-evader (`o.Z.OK`,
    Cb/Gen/OodDec.lean: a vector other than 0 has the answers 0 at no more than `Z.err` seeds): a
    condition on the sample's public coefficients alone: no code, no list.
  `o.NearJ d L`: one or the other, message by message.
  `Spec.ldReqJohn_msg`: `o.NearJ d L` ⇒ laws, `o.ListLE L`, `o.Evades`.
  `d.IsStdJ`: for some pads' field Fp: `d.IsStd Fp` with "∀ i, NearJ" (for some distances) in the
    place of laws, lists, "evades". `Spec.ldReqJohn_send`: ⇒ `d.IsStdAny`.
  `D.IsGrpJ l`: `D.IsGrp l` with: all bounds on lists in the link are `listMax |G.P| d G.e`; the
    counts of agreement are three numbers bC, bZ, bW; `Sh.par.John d G.e t bC bZ bW`
    (Cb/Obj/LdObjectTowerJohn.lean: laws, distance d as read, `InJohnson`, `MCArows` of the three
    codes; challenges, degree, packing, the fresh mask's encoding) in the place of the fold's
    hypotheses and of the list of the complex. `Spec.ldReqJohn_fold`: ⇒ `D.IsGrp l`.
  `A.ProtoJ pp`, `S.ProtoJ pp`, `L.ProtoJ pp`: `ProtoSA` with these.
  `LdReqRefDJ ..`: `LdReqRefDSA` with `std : first.IsStdJ ∧ L.ProtoJ pp ∧ T.A.ProtoJ pp`; all other
    clauses as they are there. `Spec.ldReqRefJ`: ⇒ `LdReqRefDSA ..`.
The counts bC, bZ, bW are bound by "there are": any numbers for which the three codes have
`MCArows`.

Limits: the one kind of premise on agreement that is left: `C.MCArows e b` (Cb/Ld/LdRelRows.lean),
of the base code with its kept slots, the mask code and the fresh mask's code of each closing's
shape. (At the write-up's reference parameters a segment's group has one mask row and no
mask variable is folded: there the counts of the two mask codes enter no error.)
A declared difference. All oracle messages are words over E; at a radius not below half the distance
with one pad entry of E for each answer (`o.John` asks a zero-evader on all vectors over E; with
"private over the pads" that leaves pads in E). Of the pads Lean does not say as much here:
`LdSendD.IsStdJ` binds the pads' field `Fp` and the layout `Y` by ∃, no clause ties them to
`o.John`, and no statement of this file draws them from `o.Z.OK` and `Sig.StdL.OK.priv`. In the
write-up most rows of a segment (packed cells, digits, re-encoded kept messages) are over
the base field, with pads and encoding randomness in the base field; there the sample is a
zero-evader on vectors over the base field only, and the members of a list are shown to be over the
base field. That lemma is proved (Cb/Req1/LdReqJohnSub.lean: `ld_subfield_member`), but it has no
user here: the standard sender's data and free entries are elements of E by type, so under a
standard layout in order a message whose format is over a proper subfield holds pad entries alone (a
theorem, under its hypotheses:
Cb/Req1/LdReqJohnSubNo.lean: `ld_subfield_noData`). What would cover such messages: a layout whose
data, free entries, pads and encoding randomness lie in a field chosen member by member. (The pads'
field is chosen sending by sending here; it can differ from E where a sending stands within unique
decoding.) (The form of mask rows is no difference of this generic record: its codes are any codes
read under a transformation, so native rows (short words read by repetition) and copied rows (long
words in which nothing forces the copies to agree) are both instances. Which forms the records at a
given field let in is said there.) So this record is not the write-up's reference point in
that one respect.
What stays asked and could be taken for derived. "The public coefficients of a batching annihilate a
vector other than 0 at few seeds" (`Evader.OK`: of each front's, each body's, each closing's two and
the final batching's evaders) and the same of a sample beyond unique decoding (`Sample.OK`):
conditions on public data. What the senders' layouts ask (`Y.OK t`: among it "private over the pads"
and what the encodings hide).
This file does not say that `LdReqRefDJ` can be met: no instance in this file. It does not say that
any code has `MCArows` beyond a third of the distance. It does not say that the errors are small:
the numbers' clauses are `LdReqRefDSA`'s, read at these bounds on lists. On zero knowledge: what
`Spec.ldReqJohn_send` assumes (`d.IsStdJ`: a premise) and what it concludes (`d.IsStdAny`: a
conclusion) have, nested in them, `priv`, `hides` (`Sig.StdL.OK`, Cb/Ld/LdSendStdL.lean); what
`Spec.ldReqJohn_fold` assumes (`D.IsGrpJ l`: a premise) has, nested in it, `zk` (`SumPar.John`,
Cb/Obj/LdObjectTowerJohn.lean), and what it concludes (`D.IsGrp l`: a conclusion) has `zk`
(`SumPar.Hyp`, Cb/Ld/LdTowerSumMain.lean); `Spec.ldReqRefJ` assumes `LdReqRefDJ` (a premise) and
concludes `LdReqRefDSA` (Cb/Req1/LdReqStdAny.lean: a conclusion), both with the fields `lay`,
`layT`, `layB`: lay, layT, layB stand as in `LdReqRefDSA`. The model's duty stands as there. No
statement of this file names the request's `ZkS` (`Spec.ldReqRefLayJ`, Cb/Req1/LdReqRefLayJ.lean).
This file says nothing between the Johnson radius and capacity.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdReqStdAny
import Cb.Ld.LdGroupJohn
import Cb.Ld.LdRelJohnsonProofs
import Cb.Obj.LdObjectThirdTestsProofs
import Cb.Ld.LdWfThird

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

section
variable {E : Type} [Field E] [Fintype E]

/-- An oracle message within unique decoding. -/
structure OMsg.Half (o : OMsg E) (d L : ℕ) : Prop where
  laws : o.C.Laws
  dist : o.C.Dist d
  lt   : 2 * o.e < d
  isL  : L = 1

/-- An oracle message below the Johnson radius, its sample a zero-evader. -/
structure OMsg.John (o : OMsg E) (d L : ℕ) : Prop where
  laws : o.C.Laws
  dist : o.C.Dist d
  inJ  : InJohnson (Fintype.card o.P) d o.e
  isL  : L = listMax (Fintype.card o.P) d o.e
  smp  : o.Z.OK

/-- One or the other. -/
def OMsg.NearJ (o : OMsg E) (d L : ℕ) : Prop := o.Half d L ∨ o.John d L

end

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The sending is the standard one, for some pads' field; every message sent is within unique
decoding or below the Johnson radius. -/
def LdSendD.IsStdJ {a : LdStage E Kc} (d : LdSendD a) : Prop :=
  ∃ (Fp : Type) (_ : Field Fp) (_ : Fintype Fp) (_ : Algebra Fp E) (Y : d.N.StdL Fp)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (dd : d.N.O → ℕ),
    d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 ∧
    Y.OK d.t ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧
    d.Sd.Fair ∧
    ∀ i, (d.N.om i).NearJ (dd i) (d.L i)

end

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The move "fold" is the group's own, below the Johnson radius. -/
def LdFoldD.IsGrpJ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) : Prop :=
  ∃ (_ : Fintype D.B) (_ : Nonempty D.G.P) (Sh : GShape D.G) (Hd : GHeld Sh D.kp)
      (Z : Evader E (D.G.Row D.B)) (hc : ∀ o, D.G.mem o ∨ D.kp o)
      (dw : D.S.Wit × D.Wp) (d t bC bZ bW : ℕ),
    (⟨D, l⟩ : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) =
      ⟨Hd.foldD D.Sb D.sl Z D.A₀,
        Hd.link D.Sb D.sl Z D.A₀ hc dw d t (fun _ => listMax (Fintype.card D.G.P) d D.G.e)
          (fun _ => bC) (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card D.G.P) d D.G.e)⟩ ∧
    Sh.OK ∧ Hd.Laws ∧
    Sh.par.John d D.G.e t bC bZ bW ∧
    Z.OK ∧ D.G.Fits

end

section
variable {E Kc : Type} [Field E] [Fintype E]

structure LdRefD.ProtoJ {I : LdRefIx E} (A : LdRefD E Kc I) (pp : ℕ) : Prop where
  front  : A.V.Proto pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : A.Xa.Q.D.d1.IsStdJ
  send3  : A.Xa.Q.D.d3.IsStdJ
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

structure LdRefS.ProtoJ {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (pp : ℕ) :
    Prop where
  body  : S.A.ProtoJ pp
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : S.K.R.c1.fold.IsGrpJ S.l
  snd   : S.Qc.snd.IsStdJ

def LdRefL.ProtoJ {I : LdRefIx E} {a : LdStage E Kc} (pp : ℕ) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.ProtoJ pp ∧ S.ProtoJ pp

end

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record of the reference request, below the Johnson radius. -/
structure LdReqRefDJ (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : first.IsStdJ ∧ L.ProtoJ pp ∧ T.A.ProtoJ pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  lay    : L.LayJ pp (ldReqRef1 R first b L T).base₀
  layT   : T.A.ZkAt pp (fun f =>
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

namespace Spec

/-- One oracle message: laws, its lists, "evades". -/
def ldReqJohn_msg : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (o : OMsg E) (d L : ℕ),
    o.NearJ d L → o.C.Laws ∧ o.ListLE L ∧ o.Evades

def ldReqJohn_send : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (d : LdSendD a), d.IsStdJ → d.IsStdAny

def ldReqJohn_fold : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid),
    D.IsGrpJ l → D.IsGrp l

def ldReqJohn_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (pp : ℕ),
    A.ProtoJ pp → A.ProtoSA pp

def ldReqJohn_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc)
      (S : LdRefS E Kc I a) (pp : ℕ),
    S.ProtoJ pp → S.ProtoSA pp

/-- A list of segments. -/
def ldReqJohn_list : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (pp : ℕ),
    L.ProtoJ pp → L.ProtoSA pp

/-- The record below the Johnson radius gives the record with lists and agreement as hypotheses. -/
def ldReqRefJ : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefDJ pp R core first b L T qφ q κ → LdReqRefDSA pp R core first b L T qφ q κ

end Spec

theorem ldReqJohn_msg : Spec.ldReqJohn_msg := by
  intro E _ _ o d L h
  rcases h with h | h
  · have hl : o.ListLE 1 := ldT3_list E o d h.laws h.dist h.lt
    refine ⟨h.laws, ?_, ldWfThird_evades o hl⟩
    rw [h.isL]
    exact hl
  · refine ⟨h.laws, ?_, sig_evades_of_ok E o h.smp⟩
    rw [h.isL]
    exact sig_list_of_code E o _ (ld_list_johnson E o.P o.C d o.e h.laws h.dist h.inJ)

theorem ldReqJohn_send : Spec.ldReqJohn_send := by
  intro E Kc _ _ a d ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, dd, e, h1, h2, h3, h4⟩
  exact ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, e, h1, h2, fun i => (ldReqJohn_msg E _ _ _ (h4 i)).1,
    h3, fun i => (ldReqJohn_msg E _ _ _ (h4 i)).2.1, fun i => (ldReqJohn_msg E _ _ _ (h4 i)).2.2⟩

theorem ldReqJohn_fold : Spec.ldReqJohn_fold := by
  intro E Kc _ _ D l ⟨i1, i2, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, h1, h2, h3, h4, h5⟩
  exact ⟨i1, i2, Sh, Hd, Z, hc, dw, d, t, _, _, _, _, _, e, h1, h2, h3.hyp, h4,
    ldGroupJohn_list Sh h1 h3, h5⟩

theorem ldReqJohn_body : Spec.ldReqJohn_body := fun E Kc _ _ _ _ _ h =>
  ⟨h.front, h.ok, h.places, h.uniq, ldReqJohn_send E Kc _ _ h.send1,
    ldReqJohn_send E Kc _ _ h.send3, h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm,
    h.bits, h.reads, h.deg, h.ev⟩

theorem ldReqJohn_seg : Spec.ldReqJohn_seg := fun E Kc _ _ I _ S pp h =>
  ⟨ldReqJohn_body E Kc I S.A pp h.body, h.ev, h.named,
    ldReqJohn_fold E Kc _ _ h.fold, ldReqJohn_send E Kc _ _ h.snd⟩

theorem ldReqJohn_list : Spec.ldReqJohn_list := by
  intro E Kc _ _ I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.ProtoSA]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.ProtoJ] at h
      rw [LdRefL.ProtoSA]
      exact ⟨ih h.1, ldReqJohn_seg E Kc I _ S pp h.2⟩

theorem ldReqRefJ : Spec.ldReqRefJ := fun _ E Kc _ _ _ _ _ pp _ _ _ _ L T _ _ _ h =>
  { duty := h.duty,
    std := ⟨ldReqJohn_send E Kc _ _ h.std.1,
        ldReqJohn_list E Kc _ _ _ L pp h.std.2.1,
        ldReqJohn_body E Kc _ T.A pp h.std.2.2⟩,
    deg := h.deg, ev := h.ev, tie := h.tie, own := h.own
    lay := h.lay, layT := h.layT, layB := h.layB, fmt := h.fmt, bFirst := h.bFirst,
      bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

end Cb
