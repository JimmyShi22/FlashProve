-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxView.lean: the decision's clause of the lax verifier's yes, at the typed string
that the typing makes of what the strict reader has read: the protocol's verifier accepts, if the
decision says yes on the reader's own view.



The field `accept` of the record `LaxDebts` (OnBytes/K/Left/Lax.lean), its part "the view". The
typed transcript that the lax verifier builds of the string has the strict reader's view
(`viewX_cols_at`, OnBytes/K/Left/LaxViewAt.lean, after `viewX_cols_tr`,
OnBytes/TypedOracleCompiler/Run/ViewERead.lean): the chain's own trees' columns by `own_cols`
(OnBytes/K/Left/LaxViewOwn.lean), the stored tables' by `sto_half` (OnBytes/K/Left/LaxViewSto.lean).
The protocol's verdict at such a transcript is the decision on that view (`accept_cols`).

The typed description D and the statement st under which the reader has read stand apart: at an
entry file D's own statement is empty.

Main theorem.
 `accept_view`   the clause, in `LaxDebts`' letters.

Asked by `accept_view`. Of the description: the test of OnBytes/TypedOracleCompiler `PQ.ok D.base`; the format's
test on D's two parts with st put in; all stored tables have the depth D.a and items 0 or 1;
each of the two tables is opened at most once; `okX`. Of what was read: the typing's yes; the rounds
as read are the own parts joined with the stored openings; the own parts, stripped, are a lenient
reading's rounds at the description, with as many roots as trees; each stored opening's facts; the
numbers of drawn positions. Of the chain: it draws what the reader drew; all tests of work pass.
`ListedX` (the record's own field). Two rows of the typing's own table under one key have one
column. The decision says yes on the reader's view, at any description S with D's stored tables and
D's number of the first tree (the view reads no more of a description).

Not claimed. That any of these holds at a file or at a description: none is shown at any description
here. That the decision at the instance x is the program's (the record's part "the keys"). Nothing
on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.Left.LaxViewOwn
import OnBytes.K.Left.LaxViewSto
import OnBytes.K.Left.LaxViewAt
import OnBytes.TypedOracleCompiler.Run.StretchRead
import OnBytes.TypedOracleCompiler.Run.LaxThin
import OnBytes.TypedOracleCompiler.Run.StoredTop

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (roundWithStoredOpenings StoredFact)
open TypedOracleCompiler.Slice (OpAt opsOf tabOf opLS lookE ListedX assembleS assembleS_some PSXE wqXE)

/-- The decision's clause: the protocol's verifier accepts the typed transcript, if the decision
says yes on the reader's view. -/
theorem _root_.OnBytes.K.Left.accept_view {X : Type} (h : HId) (D : XD)
    (hok : PQ.ok D.base = true) (st : ByteArray) (dec : X → View → Bool) (x : X) (o :
    _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (PSXE D dec).up) (hπ : assembleS D dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : passSL D.C D.ds ρ.2 = true) (c : _root_.Fmt.Chain)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (htr : TraceL h D.base.plan D.base.rounds (rc.map fun p => stripR p.1) c #[])
    (hsent : List.Forall₂ SentR D.ds (rc.map fun p => stripR p.1))
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg st p.1.drawn.poss) ts p.2) D.stored rc)
    (hlen : List.Forall₂ (fun (z : _root_.Fmt.Round × List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      p.1.drawn.poss.length = z.1.entry.poss) (D.base.rounds.zip D.stored) rc)
    (hSok : (⟨{ D.base with statement := st }, D.stored⟩ : _root_.Fmt.SpecX).ok = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (okx : okX D.ds D.a D.xs = true)
    (listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXE D dec).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)))
    (hA : ∀ tab, tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) =
      some tab → Agree tab)
    (hbase : ({ D.base with statement := st } : _root_.Fmt.Spec).ok = true)
    (S : _root_.Fmt.SpecX) (hsto : S.stored = D.stored)
    (hft : S.base.firstTree = D.base.firstTree) (hdec : dec x (_root_.Fmt.viewX S o) = true) :
    (PSXE D dec).up.loc.accept x
      ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
        ((none, some []), rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true := by
  have ev : _root_.Fmt.viewX S o = _root_.Fmt.viewX ⟨D.base, D.stored⟩ o := by
    unfold _root_.Fmt.viewX
    rw [hsto, hft]
  rw [ev] at hdec
  have hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TabGood D.base x n :=
    fun r hr x hx => tab_good D.base (tab_limits D.base hok) r hr x hx
  have hown := OnBytes.K.Left.hown_of h D hg rc c htr
  obtain ⟨hy, hcar, hfull⟩ := OnBytes.K.Left.sto_half h D st dec x o π hπ ρ hd rc ho hS hlen hSok hD
    honce hown okx listed
  obtain ⟨run, pl, tab, tx, -, hpl0, htab, -, -, -, hplains, hopens, -, -⟩ :=
    assembleS_some D dec hπ
  have hsame := same5_strip_joined rc
  have hpl : plainsSL D.C D.ds (rc.map fun p => stripR p.1) = some pl := by
    rw [plainsSL_same D.C D.ds _ _ hsame, ← ho]
    exact hpl0
  have hrt : rtSL D.C D.ds o.rounds.toList = rtSL D.C D.ds (rc.map fun p => stripR p.1) := by
    rw [ho]
    exact (rtSL_same D.C D.ds _ _ hsame).symm
  have hd' : drawnSL D.C D.ds ρ.2 = (rc.map fun p => stripR p.1).map (·.drawn) := by
    rw [hd, ho]
    exact (drawn_same _ _ hsame).symm
  have hcol := hcol_of_op D.C D.K (chalP D.base.plan.field D.K) D.ds
    (rc.map fun p => stripR p.1) pl ρ.2 (fun q => π.opens (.inr q)) D.base.firstTree hsent
    (fun ro hro y hy' zc hzc => by
      obtain ⟨q, z, h1, h2, h3⟩ := OnBytes.K.Left.own_cols h D o c rc ho htr hg run tab htab
        (hA tab htab) ro hro y hy' zc hzc
      exact ⟨q, z, h1, (hopens q).trans h2, h3⟩)
  have hview := OnBytes.K.Left.viewX_cols_at h D st D.K (chalP D.base.plan.field D.K) hbase hg
    (rc.map fun p => stripR p.1) o c htr pl ρ.2 (fun q => π.opens (.inr q)) hpl hd' rc rfl ho hS hD
    ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym) hy hcol
  have ht : trP (PSXE D dec).S (PSXE D dec).ann (wqXE D dec).sh
      ((none, some []), rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens =
      mkTr (up (PSXE D dec).S) (PSXE D dec).ann (wqXE D dec).sh
        ((none, some []), rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens :=
    (trP_eq _ _ _ _ _ _ _).trans (mkTrT_eq 256 (D.K + 1) _ _ _ _ _ _ _)
  show (skeletonOverBothExternalStrings D.C D.ds D.a D.xs (dec x)).accept () _
    (mkTr (up (PSXE D dec).S) (PSXE D dec).ann (wqXE D dec).sh
      ((none, some []), rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true
  rw [← ht, hplains, hrt]
  obtain ⟨c0, ρ'⟩ := ρ
  exact (accept_cols D D.K (chalP D.base.plan.field D.K) (dec x) _ pl ρ'
    (fun q => π.opens (.inr q)) _ _ _ c0 hpass hfull hcar hview).trans hdec

end TypedOracleCompiler.Run.PQ
