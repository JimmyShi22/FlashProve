-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RuleValues.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the hidden values that are sent by themselves
(Johnson/Desc/K5/Honest/Alone.lean), READ IN A FIELD, ARE THE LIBRARY's RULE VALUES of the named
scalars of the key forms (`rv`, Inst/Model/Att/KeyForms.lean), where the prover's points and pieces'
weights read as the library's. Two definitions of premises, and statements with their proofs.

Main names:
  `PiecesRead`, `sum_pieces`
                     the premise on a unit's pieces: one for each pair, in the pairs' order, with
                     the library's weights of a family; a sum over the pieces is then the library's
                     sum over the pairs
  `YReads`           the premise on three cuts of a list's inner point: head, token, channel
  `planeOf_rule`     R and PV: `rv (.cell fam x)`
  `maxAt_rule_below`, `maxAt_rule_on`   MV: `rv (.ms .M)`, `rv (.ms .D)`
  `rhAt_rule`, `rhpAt_rule`, `ibAt_rule`, `rh2At_rule`, `rhp2At_rule`
                     RH, RHP, IB_k, RH2, RHP2: `rv` at `.rh`, `.rh'`, `.ib k`, `.rg`, `.rg'`
  `lonePts_iff`      the premise `LonePts` of Law/Starts.lean is `PiecesRead` and `YReads` at one
                     list

EVERY STATEMENT ON A VALUE IS CONDITIONAL: on the shape's numbers (`Sized`, public) where it is
named, on `PiecesRead` of the value's list, and on the premises that the value's points read as the
library's. These premises have the form of those of the tree's statements on the verifier's claims
on the same scalars (Johnson/Desc/First/Att/Claims/KeysLin.lean, LinZc.lean). Whoever calls a
statement here has to show them: they hang on what the lookup hands on.
Limits. ZC and ACC are not here: Law/Starts.lean has them (`zc_reads`, `acc_reads`). The three other
scalars of the key forms (the two scores, the denominator times the output) are sums over cubes:
Law/ReadKM.lean, Law/ReadKD.lean and Law/ReadSE.lean have them. For RH2 and RHP2 `YReads` asks that
the points of the high parts' list read as (y_g | y_i | y_n), which the library cuts from the inner
point of the list of the remainders' low bits; that the two lists' inner points agree is not proved
in the library (Inst/Model/Att/Points.lean, at `u4`). A plan
in which the layers of the group have more than one shift is not reached: `PiecesRead` fails there
of a softmax-table unit. Nothing here says that a premise holds at any place. No property is claimed
by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadAlone
import Johnson.Desc.K5.Honest.Law.Starts
import Inst.Model.Att.KeyForms
import Johnson.Road.Rows.AttLin
import Johnson.Desc.First.Att.Claims.WeightsKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 RemP ScoreP DivP eqTab tok)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Pieces -/

/-- **The premises on a unit's pieces**: one for each pair, in the pairs' order, with the library's
weights of the family. -/
structure PiecesRead (P : Pub5) (C : Calls) (z : ℕ → K) (fam : Fam) (pw : Array W1) : Prop where
  size : pw.size = P.D.nb
  w : ∀ b < P.D.nb, ρ.val (pw.getD b ⟨0, 0, zeroE⟩).wp = wp P.D C z fam b
  pairs : PairsAre P.g pw

variable {P : Pub5}

/-- **A sum over the pieces is the library's sum over the pairs.** CONDITIONAL on `PiecesRead`. -/
theorem sum_pieces {C : Calls} {z : ℕ → K} {fam : Fam} {pw : Array W1}
    (R : PiecesRead ρ P C z fam pw) (F : ℕ → K) :
    (pw.toList.map fun p => ρ.val p.wp * F (pairNo P.g p)).sum =
      ∑ b ∈ range P.D.nb, wp P.D C z fam b * F b := by
  rw [sum_toList, R.size]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  rw [R.w b hb', show pairNo P.g (pw.getD b ⟨0, 0, zeroE⟩) = b from R.pairs.pair hb']

variable (w : K5In) (C : Calls) (p : Pub K)

/-! ## Planes and maxima -/

/-- **R and PV are their rule values.** CONDITIONAL on: the unit's region and the length of its
inner point are the family's; the inner point reads as the library's; `PiecesRead`. -/
theorem planeOf_rule {u : RemP} {fam : Fam} (hr : regOf u.isD = fam.reg)
    (hs : u.z.size = fam.l P.D) (hz : ∀ j < fam.l P.D, pt ρ u.z j = inn P.D C p.z fam j)
    (R : PiecesRead ρ P C p.z fam u.pw) (x : ℕ) :
    ρ.val (planeOf P.g w u x) = rv P.D C p (tOf ρ w) (.cell fam x) := by
  refine (read_planeOf ρ P.g w u x).trans ((sum_pieces ρ R fun b =>
    Blocks.ext u.z.size (fun n => tOf ρ w (.c (regOf u.isD) x b n)) (pt ρ u.z)).trans ?_)
  show _ = ∑ b ∈ range P.D.nb, wp P.D C p.z fam b *
    Blocks.ext (fam.l P.D) (fun y => tOf ρ w (.c fam.reg x b y)) (inn P.D C p.z fam)
  refine sum_congr rfl fun b _ => ?_
  rw [hs, hr]
  exact congrArg _ (Blocks.ext_congr_point hz _)

/-- **MV of the unit below the diagonal is its rule value.** CONDITIONAL on: `Sized`; `PiecesRead`;
the unit's head point, tile rows' weights and point of the query's place in a tile read as the
library's. -/
theorem maxAt_rule_below (H : Sized P) {k : ScoreP} (R : PiecesRead ρ P C p.z .m2 k.pw)
    (sg : k.zg.size = P.D.lg) (hg : ∀ j < P.D.lg, pt ρ k.zg j = zg P.D C p.z j)
    (hI : ∀ I < P.D.nBlk, ρ.val (k.wI.getD I zeroE) = blkRow P.D (zP P.D C p.z) (zs P.D C p.z) I)
    (si : k.zi.size = P.D.lB) (hi : ∀ j < P.D.lB, pt ρ k.zi j = zi' P.D C p.z j) :
    ρ.val (maxAt P.g w k) = rv P.D C p (tOf ρ w) (.ms .M) := by
  have ht := tok_reads ρ H hI si hi
  refine (read_rows ρ (f := w.mx) (a := mxV (tOf ρ w))
    (Ψ := psiRow P.D (zP P.D C p.z) (zs P.D C p.z) (zi' P.D C p.z)) sg hg ht.1 ht.2
    (read_mx ρ w)).trans ?_
  exact sum_pieces ρ R fun b => rd2 P.D (zg P.D C p.z)
    (psiRow P.D (zP P.D C p.z) (zs P.D C p.z) (zi' P.D C p.z)) (mxV (tOf ρ w) b)

/-- **MV of the unit on the diagonal is its rule value.** CONDITIONAL as `maxAt_rule_below`. -/
theorem maxAt_rule_on (H : Sized P) {k : ScoreP} (R : PiecesRead ρ P C p.z .d2 k.pw)
    (sg : k.zg.size = P.D.lg) (hg : ∀ j < P.D.lg, pt ρ k.zg j = zgD P.D C p.z j)
    (hI : ∀ I < P.D.nBlk, ρ.val (k.wI.getD I zeroE) = Blocks.eqN (P.D.lP + 1) 0 (zID P.D C p.z) I)
    (si : k.zi.size = P.D.lB) (hi : ∀ j < P.D.lB, pt ρ k.zi j = zi' P.D C p.z j) :
    ρ.val (maxAt P.g w k) = rv P.D C p (tOf ρ w) (.ms .D) := by
  have ht := tok_reads ρ H hI si hi
  refine (read_rows ρ (f := w.mx) (a := mxV (tOf ρ w))
    (Ψ := eqT P.D (cat (P.D.lP + 1) (zID P.D C p.z) (zi' P.D C p.z))) sg hg ht.1
    (fun i hi' => (ht.2 i hi').trans (K5Law.eqT_tile P.D _ _ i)) (read_mx ρ w)).trans ?_
  exact sum_pieces ρ R fun b => rd2 P.D (zgD P.D C p.z)
    (eqT P.D (cat (P.D.lP + 1) (zID P.D C p.z) (zi' P.D C p.z))) (mxV (tOf ρ w) b)

/-! ## The division's scalars -/

/-- **The premises on three cuts of a list's inner point**: head, token, channel: they have their
lengths and read as the library's (y_g | y_i | y_n). -/
structure YReads (P : Pub5) (C : Calls) (z : ℕ → K) (zg zi zc : Array E) : Prop where
  sg : zg.size = P.D.lg
  g : ∀ j < P.D.lg, pt ρ zg j = yg P.D C z j
  si : zi.size = P.D.lT
  i : ∀ j < P.D.lT, pt ρ zi j = yi P.D C z j
  sc : zc.size = P.D.ln
  n : ∀ j < P.D.ln, pt ρ zc j = yn P.D C z j

/-- The equality weights of a token point that agrees with v. -/
theorem read_eqT {zi : Array E} {v : ℕ → K} (si : zi.size = P.D.lT)
    (hi : ∀ j < P.D.lT, pt ρ zi j = v j) {i : ℕ} (h : i < P.D.T) :
    ρ.val ((eqTab zi).getD i zeroE) = eqT P.D v i :=
  read_eqTab ρ si hi (by rw [← Dim.T_eq]; exact h)

/-- A value of (pair, head, token, channel) at points that read as (y_g | y_i | y_n), under the
weights of a family: the library's extension at the lookup's point. -/
theorem atChan_rule {fam : Fam} {pw : Array W1} {zg zi zc : Array E}
    (R : PiecesRead ρ P C p.z fam pw) (Y : YReads ρ P C p.z zg zi zc) {f : ℕ → ℕ → ℕ → ℕ → E}
    {a : ℕ → ℕ → ℕ → ℕ → K} (hf : ∀ b g i n, ρ.val (f b g i n) = a b g i n) :
    ρ.val (atChan P.g pw zg zi zc f) =
      ∑ b ∈ range P.D.nb, wp P.D C p.z fam b * atY P.D C p (a b) := by
  refine (read_chans ρ (f := f) (a := a) (Ψ := eqT P.D (yi P.D C p.z)) Y.sg Y.g
    (size_eqTab_tok Y.si) (fun i h => read_eqT ρ Y.si Y.i h) Y.sc Y.n hf).trans ?_
  refine (sum_pieces ρ R fun b =>
    rd3 P.D (yg P.D C p.z) (eqT P.D (yi P.D C p.z)) (yn P.D C p.z) (a b)).trans ?_
  exact sum_congr rfl fun b _ => by rw [OnBytes.Road.Rows.rd3_atY]

/-- **RH is its rule value.** CONDITIONAL on `PiecesRead` and `YReads` of the list of the
remainders' low bits. -/
theorem rhAt_rule {d : DivP} (R : PiecesRead ρ P C p.z .w3 d.pwW)
    (Y : YReads ρ P C p.z d.zgW d.ziW d.zcW) :
    ρ.val (rhAt P.g w d) = rv P.D C p (tOf ρ w) .rh :=
  atChan_rule ρ C p R Y (f := w.rh) (a := fun b g i n => tOf ρ w (.qh b g i n)) fun _ _ _ _ => rfl

/-- **RHP is its rule value.** CONDITIONAL on `PiecesRead` and `YReads` of the list of the
remainders' low bits. -/
theorem rhpAt_rule {d : DivP} (R : PiecesRead ρ P C p.z .w3 d.pwW)
    (Y : YReads ρ P C p.z d.zgW d.ziW d.zcW) :
    ρ.val (rhpAt P.g w d) = rv P.D C p (tOf ρ w) .rh' :=
  atChan_rule ρ C p R Y (f := w.rhp) (a := fun b g i n => tOf ρ w (.qh' b g i n))
    fun _ _ _ _ => rfl

/-- **RH2 is its rule value.** CONDITIONAL on `PiecesRead` and `YReads` of the list of the high
parts. -/
theorem rh2At_rule {d : DivP} (R : PiecesRead ρ P C p.z .f4 d.pwH)
    (Y : YReads ρ P C p.z d.zgH d.ziH d.zcH) :
    ρ.val (rh2At P.g w d) = rv P.D C p (tOf ρ w) .rg :=
  atChan_rule ρ C p R Y (f := w.rh) (a := fun b g i n => tOf ρ w (.qh b g i n)) fun _ _ _ _ => rfl

/-- **RHP2 is its rule value.** CONDITIONAL as `rh2At_rule`. -/
theorem rhp2At_rule {d : DivP} (R : PiecesRead ρ P C p.z .f4 d.pwH)
    (Y : YReads ρ P C p.z d.zgH d.ziH d.zcH) :
    ρ.val (rhp2At P.g w d) = rv P.D C p (tOf ρ w) .rg' :=
  atChan_rule ρ C p R Y (f := w.rhp) (a := fun b g i n => tOf ρ w (.qh' b g i n))
    fun _ _ _ _ => rfl

/-- **IB_k is its rule value.** CONDITIONAL on: `Sized`; `PiecesRead` of the list of the indices;
its head point and token point read as the library's. -/
theorem ibAt_rule (H : Sized P) {d : DivP} (R : PiecesRead ρ P C p.z .x3 d.pwX)
    (sg : d.zgX.size = P.D.lg) (hg : ∀ j < P.D.lg, pt ρ d.zgX j = xg P.D C p.z j)
    (si : d.ziX.size = P.D.lT) (hi : ∀ j < P.D.lT, pt ρ d.ziX j = xi P.D C p.z j) {k : ℕ}
    (hk : k < P.D.lT) :
    ρ.val ((ibAt P.g w d).getD k zeroE) = rv P.D C p (tOf ρ w) (.ib k) := by
  rw [ibAt_getD w P.g d (by rw [H.lt]; exact hk)]
  refine (read_rows ρ (f := w.ibit k) (a := Inst.Model.AttSeg.ibV (tOf ρ w) k)
    (Ψ := eqT P.D (xi P.D C p.z)) sg hg (size_eqTab_tok si) (fun i h => read_eqT ρ si hi h)
    (read_ibit ρ w k)).trans ?_
  exact sum_pieces ρ R fun b => rd2 P.D (xg P.D C p.z) (eqT P.D (xi P.D C p.z))
    (Inst.Model.AttSeg.ibV (tOf ρ w) k b)

/-! ## The premise of the file on the sumchecks' starts -/

/-- The premise on the points of the division's scalars (`LonePts`, Law/Starts.lean) is the two
premises of this file at the list of the remainders' low bits. -/
theorem lonePts_iff {d : DivP} : LonePts ρ P C p d ↔
    PiecesRead ρ P C p.z .w3 d.pwW ∧ YReads ρ P C p.z d.zgW d.ziW d.zcW :=
  ⟨fun L => ⟨⟨L.nW, L.hw, L.pairs⟩, ⟨L.nG, L.hg, L.nI, L.hi, L.nC, L.hn⟩⟩,
    fun h => ⟨h.1.size, h.1.w, h.1.pairs, h.2.sg, h.2.g, h.2.si, h.2.i, h.2.sc, h.2.n⟩⟩

end H2K5.Honest

#print axioms H2K5.Honest.sum_pieces
#print axioms H2K5.Honest.planeOf_rule
#print axioms H2K5.Honest.maxAt_rule_below
#print axioms H2K5.Honest.maxAt_rule_on
#print axioms H2K5.Honest.read_eqT
#print axioms H2K5.Honest.atChan_rule
#print axioms H2K5.Honest.rhAt_rule
#print axioms H2K5.Honest.rhpAt_rule
#print axioms H2K5.Honest.rh2At_rule
#print axioms H2K5.Honest.rhp2At_rule
#print axioms H2K5.Honest.ibAt_rule
#print axioms H2K5.Honest.lonePts_iff
