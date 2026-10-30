-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlReqJohn.lean: conditions on the codes and sample maps of a
request's part of the protocol, for Reed-Solomon codes over the field with p = 2^64 - 2^32 + 1
elements, read over its cubic extension E (Cb/Gl/GlField.lean), each oracle within unique decoding
or below the Johnson radius. From them the generic conditions on list decoding follow, and, with one
named hypothesis more, those on mutual correlated agreement.

No bound on a list, no agreement, and no clause "two members of one list agree at few seeds"
(`OMsg.Evades`) is asked; agreement comes from the one hypothesis BCHKS46F F, by name. Still asked:
that the public coefficients of each batching are a zero-evader (`Evader.OK`).
Definitions and statements (`Cb.Spec.padE_ok`; the others in `Cb.Gl.Spec`); the proofs, an assembly,
are in Cb/GlVal/GlReqJohnProofs.lean; `NearGl.half`, `NearGl.john` (how to give `NearGl`) are proved
here.
Cb/Req1/LdReqJohn.lean has the generic records (`o.NearJ`, `d.IsStdJ`, `D.IsGrpJ l`, `ProtoJ` of A,
S, L): laws, distances, the Johnson condition, "the sample is a zero-evader", and agreement of a
closing's three codes whatever the number of rows, as premises on agreement. Here, at this field,
these become conditions on families of plain Reed-Solomon codes (`GlC`, `GlJ`: Cb/Gl/GlLd.lean,
Cb/Gl/GlLdJ.lean), on the samples' form, and numbers.
A sample map (`Sample`, Cb/Gen/OodDec.lean) gives a matrix for each seed; it is a zero-evader
(`Sample.OK`) if each vector other than 0 has all answers 0 at no more than `err` seeds. The data of
a sending are `LdSendD`, of a closing's move `LdFoldD` (Cb/Req1/LdSegKit.lean), of a list of
segments `LdRefL` (Cb/Req1/LdReqRef.lean). e is below the Johnson radius if `InJohnson` n d e holds:
n (n - d) < (n - e)^2; `listMax` n d e is the Johnson bound on lists (Cb/Gen/JohnsonList.lean).
`Cb.BCHKS46F` is defined in Cb/Gen/CodeListRSF.lean.

Main names, generic (any subfield Fp of E):
  `Y.PadE a`: the sample of the member a, on the layout's names, is the row with a pad
    (Cb/Gen/OodDecPad.lean), the entries proper are at different corners of the cube, the factor
    is injective, the pad's weights are independent over E. (`Y.PadSmpE` of Cb/Gl/GlObjMixPad.lean
    asks this, and more, of all members at once.)
  `Spec.padE_ok`: `Y.PadE a` → the sample of a is a zero-evader on all vectors (`(N.om a).Z.OK`).
Main names, at this field (F, E: Cb/Gl/GlField.lean):
  `NearGl Y a d L`: one member, one of two: 2 e below the distance d and the bound L on its lists is
    1; or e below the Johnson radius, L is `listMax` |P| d e, and `Y.PadE a`.
  `MsgsGl N Y L t d`: the oracle messages of one family N with a layout Y (pads in Fp): the format's
    three clauses; every member's sample is the row with a pad, the weights a basis of E over Fp,
    the factor never 0 (`Y.PadSmp`: what makes the answers private); every member's code is `GlC` at
    (d a, t a); `NearGl` of every member.
  `Spec.glReqJohn_msgs`: `MsgsGl N Y L t d` → `Y.OK t`, and every member is `o.NearJ (d a) (L a)`.
    Nothing assumed beyond the hypotheses of the statement and whatever the arguments hold as
    proofs.
  `IsStdGl d`: one sending: for some pads' field Fp (sending by sending): d is the standard sending
    of a layout Y with pads in Fp (one equation); the extractor undoes what the sender reads; fair
    seeds; `MsgsGl` of its family.
  `IsGrpGl D l`: one closing's move "bridge, arrangement, fold": (D, l) is the group's own (one
    equation, all bounds on lists := `listMax` |P| d e, the counts bC, bZ, bW parameters); the
    shape's clauses that do not speak of the base and the mask code alone; the held messages' laws;
    base code, mask code and the fresh mask's code are `GlJ` at (d, e) with the counts bC, bZ, bW;
    the Johnson condition; challenges distinct, degree at least 2, the packing's law and degrees;
    the bridge's evader evades; `Fits`.
  `ProtoGlA A pp`, `ProtoGlS S pp`, `ProtoGlL pp L`: `ProtoJ` of A, S, L with these two in the place
    of `IsStdJ`, `IsGrpJ`; all other clauses as they stand there.
  `Spec.glReqJohn_send`: `IsStdGl d` → `d.IsStdJ`. Nothing assumed beyond the hypotheses of the
    statement and whatever the arguments hold as proofs.
  `Spec.glReqJohn_fold`: BCHKS46F F → `IsGrpGl D l` → `D.IsGrpJ l`.
  `Spec.glReqJohn_body`: `ProtoGlA A pp` → `A.ProtoJ pp` (nothing assumed beyond the hypotheses of
    the statement and whatever the arguments hold as proofs).
  `Spec.glReqJohn_seg`, `Spec.glReqJohn_list`: BCHKS46F F → `ProtoGlS S pp` → `S.ProtoJ pp`;
    BCHKS46F F → `ProtoGlL pp L` → `L.ProtoJ pp`.

The counts bC, bZ, bW are parameters, bounded from below through `GlJ` (which is closed upwards): no
equation ties them to the count of the statement on codes.
Where BCHKS46F F enters: the agreement of the three codes of each closing's fold. Nowhere else:
every list is the proved Johnson bound or unique decoding; "evades" comes from the sample's form or
from a list of one member. It is a case of the Theorem 4.6 that the lines at the top name, for which
the source gives an outline of a proof; a hypothesis by name, no axiom. (The source of the statement
on codes: the head of Cb/Gen/CodeListRS.lean.)

Limits:
Still asked as they stand. On public coefficients alone (no code, no list): `Evader.OK` of each
closing's bridge, of each front's, each body's and each closing's batching. Speaking of the codes'
words, though of no list and no agreement, so not "families and numbers": `D.G.Fits`, `Hd.Laws`,
`Sh.view.Laws`.
This file does not say that these records can be met (a guard: not in this file; for `MsgsGl`,
`IsStdGl`, `IsGrpGl`, `ProtoGlA`, `ProtoGlS`,
`ProtoGlL` none
is named here),
or that the counts are small against the field.
Not said either: Whether the source proves what it states.
It says nothing on zero knowledge of the request, formats, numbers: other clauses of the request's
record.
Declared difference: beyond half the distance every oracle message is over E, with one pad entry of
E for each answer, and so are all messages of the same sending. The pads' field is one for a sending
("there is Fp" in `IsStdGl`), where this protocol's technical report (lean/CREDITS.md) gives each
oracle message a field of its own.
As soon as one member of a sending stands in the second case, `Y.PadSmp` and `Y.PadE` together force
one pad entry and Fp of dimension 1 under E.
In the report most rows of a segment are over the base field, with as many pad entries of the
base field for an answer as E has dimension; there the sample is a zero-evader on vectors over the
base field only, and the members of a list are over the base field.
Why not otherwise: in the standard sender's layout the data and the free entries of a message are
elements of E by type, and any such vector can stand in the message; so a format over a proper
subfield can be met only by a member that holds pad entries alone (proved, for a layout in order and
a code with laws whose generator is over the subfield: Cb/Req1/LdReqJohnSubNo.lean:
Cb.ld_subfield_noData). (The theorem holds at every radius below the distance: all messages of the
standard senders are words over E, offline too; only the pads may lie in a subfield, within unique
decoding.)
The lemma on lists itself (a member of the list of a word over a subfield is over the subfield)
stands, generic, beside: Cb/Req1/LdReqJohnSub.lean; nothing above uses it (but for the proof of
`Cb.ld_subfield_noData`).
This file says nothing on more than one answer a sample (the row with a pad has one): the report has
"at least one", a public parameter (by a reading of a print of the technical report;
not held against the report's latest edition).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqJohn
import Cb.Gl.GlGroupJohn
import Cb.Gl.GlObjMixPad

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {Fp E : Type} [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E] {N : Sig E}

/-- The sample of one member is the row with a pad, a zero-evader over E. -/
def Sig.StdL.PadE (Y : N.StdL Fp) (a : N.O) : Prop :=
  ∃ (μ B : Type) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B) (_ : Nonempty B)
      (pl : Y.Dt a ⊕ Y.Fr a → μ → Bool) (w : Y.Pd a → E) (b : B → E),
    (N.om a).Z.comap (Y.ν a).symm = Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b ∧
    Function.Injective pl ∧
    Function.Injective b ∧
    Function.Injective (padVal (F := E) w)

end

def Spec.padE_ok : Prop :=
  ∀ (Fp E : Type) [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E] (N : Sig E)
      (Y : N.StdL Fp) (a : N.O),
    Y.PadE a → (N.om a).Z.OK

end Cb

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR Cb.Ood Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

section
variable {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] {N : Sig E}

/-- One member: within half the distance, or below the Johnson radius with a sample that is a
zero-evader by its form. -/
def NearGl (Y : N.StdL Fp) (a : N.O) (d L : ℕ) : Prop :=
  (2 * (N.om a).e < d ∧ L = 1) ∨
  (InJohnson (Fintype.card (N.om a).P) d (N.om a).e ∧
    L = listMax (Fintype.card (N.om a).P) d (N.om a).e ∧
    Y.PadE a)

theorem NearGl.half {Y : N.StdL Fp} {a : N.O} {d L : ℕ} (h : 2 * (N.om a).e < d) (hL : L = 1) :
    NearGl Y a d L := .inl ⟨h, hL⟩

theorem NearGl.john {Y : N.StdL Fp} {a : N.O} {d L : ℕ}
    (h : InJohnson (Fintype.card (N.om a).P) d (N.om a).e)
    (hL : L = listMax (Fintype.card (N.om a).P) d (N.om a).e) (hs : Y.PadE a) : NearGl Y a d L :=
  .inr ⟨h, hL, hs⟩

end

/-- The oracle messages of one family with a layout, at this field. -/
structure MsgsGl {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E)
    (Y : N.StdL Fp) (L t d : N.O → ℕ) : Prop where
  fmt  : Y.Fmt
  smp  : Y.PadSmp
  code : ∀ a, GlC (N.om a).C (d a) (t a)
  near : ∀ a, NearGl Y a (d a) (L a)

section
variable {Kc : Type}

/-- One sending, at this field: for some pads' field. -/
def IsStdGl {a : LdStage E Kc} (d : LdSendD a) : Prop :=
  ∃ (Fp : Type) (_ : Field Fp) (_ : Fintype Fp) (_ : Algebra Fp E) (Y : d.N.StdL Fp)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (dd : d.N.O → ℕ),
    d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧
    d.Sd.Fair ∧
    MsgsGl d.N Y d.L d.t dd

/-- One closing's move "bridge, arrangement, fold", at this field. -/
def IsGrpGl (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) : Prop :=
  ∃ (_ : Fintype D.B) (_ : Nonempty D.G.P) (Sh : GShape D.G) (Hd : GHeld Sh D.kp)
      (Z : Evader E (D.G.Row D.B)) (hc : ∀ o, D.G.mem o ∨ D.kp o)
      (dw : D.S.Wit × D.Wp) (d t bC bZ bW : ℕ),
    (⟨D, l⟩ : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) =
      ⟨Hd.foldD D.Sb D.sl Z D.A₀,
        Hd.link D.Sb D.sl Z D.A₀ hc dw d t (fun _ => listMax (Fintype.card D.G.P) d D.G.e)
          (fun _ => bC) (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card D.G.P) d D.G.e)⟩ ∧
    (Sh.view.Laws ∧
      (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
      (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
      (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
      1 ≤ Sh.h + Sh.g) ∧
    Hd.Laws ∧
    (GlJ Sh.Cb d 0 D.G.e bC ∧
      GlJ Sh.Zb d 0 D.G.e bZ ∧
      GlJ Sh.par.Zw d t D.G.e bW ∧
      InJohnson (Fintype.card D.G.P) d D.G.e) ∧
    (Function.Injective Sh.val ∧ 2 ≤ Sh.n ∧ Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
    Z.OK ∧ D.G.Fits

/-- A body. -/
structure ProtoGlA {I : LdRefIx E} (A : LdRefD E Kc I) (pp : ℕ) : Prop where
  front  : A.V.Proto pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : IsStdGl A.Xa.Q.D.d1
  send3  : IsStdGl A.Xa.Q.D.d3
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

/-- A segment with its closing. -/
structure ProtoGlS {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (pp : ℕ) : Prop where
  body  : ProtoGlA S.A pp
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : IsGrpGl S.K.R.c1.fold S.l
  snd   : IsStdGl S.Qc.snd

/-- The list of segments. -/
def ProtoGlL {I : LdRefIx E} {a : LdStage E Kc} (pp : ℕ) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => ProtoGlL pp L ∧ ProtoGlS S pp

end

namespace Spec

def glReqJohn_msgs : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E)
      (Y : N.StdL Fp) (L t d : N.O → ℕ),
    MsgsGl N Y L t d → Y.OK t ∧ ∀ a, (N.om a).NearJ (d a) (L a)

def glReqJohn_send : Prop := ∀ (Kc : Type) (a : LdStage E Kc) (d : LdSendD a), IsStdGl d → d.IsStdJ

def glReqJohn_fold : Prop :=
  Cb.BCHKS46F F →
  ∀ (Kc : Type) (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid), IsGrpGl D l → D.IsGrpJ l

def glReqJohn_body : Prop :=
  ∀ (Kc : Type) (I : LdRefIx E) (A : LdRefD E Kc I) (pp : ℕ), ProtoGlA A pp → A.ProtoJ pp

def glReqJohn_seg : Prop :=
  Cb.BCHKS46F F →
  ∀ (Kc : Type) (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a) (pp : ℕ),
    ProtoGlS S pp → S.ProtoJ pp

/-- A list of segments, under the premise `Cb.BCHKS46F F`, which this file does not prove. -/
def glReqJohn_list : Prop :=
  Cb.BCHKS46F F →
  ∀ (Kc : Type) (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    ProtoGlL pp L → L.ProtoJ pp

end Spec
end Cb.Gl
