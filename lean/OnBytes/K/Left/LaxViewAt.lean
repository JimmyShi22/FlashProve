-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxViewAt.lean: the typed view of one chain is the strict reader's view, with the
typed description and the reader's statement apart.



OnBytes/TypedOracleCompiler/Run/ViewERead.lean's `viewX_cols_tr` speaks of one description D and asks the stored
openings' facts (`StoredFact`) at D's own statement. At an entry file the typed description has an
empty statement (`entryXD`, OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean), and the reader has read under the
description with the two tables' statement put in; `StoredFact` holds that the statement's item has
the opening's root, so at the empty statement it fails. Here the same conclusion stands with these
facts at any statement st. The lemma is called at D with st put in; the rounds' data of the two
descriptions are equal by `rds_congr`. For proofs only; the program does not import this file.

Main theorems.
 `tabGood_st`      `TabGood` does not look at the statement.
 `viewX_cols_at`   `viewX_cols_tr` with the stored openings' facts at a statement st.

What is not claimed. Nothing on soundness; no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ViewERead
import OnBytes.TypedOracleCompiler.Run.AllRoots

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (roundWithStoredOpenings StoredFact)

/-- `TabGood` does not look at the statement. -/
theorem _root_.OnBytes.K.Left.tabGood_st (B : _root_.Fmt.Spec) (st : ByteArray)
    (x : _root_.Fmt.Shape × _root_.Fmt.Src) (n : ℕ) (g : TabGood B x n) :
    TabGood { B with statement := st } x n :=
  ⟨g.src, g.lt, g.tree, g.plain, by
    rw [rds_congr { B with statement := st } B rfl rfl]
    exact g.sh⟩

/-- The typed view is the strict reader's view, with the stored openings' facts at a statement
st of the reader's. All else as in `viewX_cols_tr`; `hbase` is asked at D's own part with st put in.
-/
theorem _root_.OnBytes.K.Left.viewX_cols_at (h : HId) (D : XD) (st : ByteArray) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (hbase : ({ D.base with statement := st } : _root_.Fmt.Spec).ok = true)
    (hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TabGood D.base x n)
    (ros : List _root_.Fmt.RoundOut) (o : _root_.Fmt.ChainOut) (c : _root_.Fmt.Chain)
    (htr : TraceL h D.base.plan D.base.rounds ros c #[])
    (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (op : (p : OPos (uL D.C D.ds)) → Option (Opening 256 (OSym (uL D.C D.ds) p)))
    (hpl : plainsSL D.C D.ds ros = some pl) (hd : drawnSL D.C D.ds ρ = ros.map (·.drawn))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : ros = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg st p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (y : (twoExternalStrings (2 ^ D.a) SgX).Str)
    (hy : ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd y q = (xc.1, xc.2))
    (hcol : ∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      colAtS D.C D.ds (trL D.C K chal D.ds (rtSL D.C D.ds ros) pl ρ op)
        (x.1.tree - D.base.firstTree) zc.1 = some zc.2) :
    PQ.viewX D.C D.ds D.a D.xs y (trL D.C K chal D.ds (rtSL D.C D.ds ros) pl ρ op) =
      _root_.Fmt.viewX ⟨D.base, D.stored⟩ o := by
  have e : rds ({ D.base with statement := st } : _root_.Fmt.Spec) = D.ds :=
    rds_congr _ _ rfl rfl
  have hq : ∀ (pl : Plains (uL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec))))
      (ρ : Rho (uL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec))))
      (op : (p : OPos (uL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)))) →
        Option (Opening 256
          (OSym (uL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec))) p))),
      plainsSL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)) ros = some pl →
      drawnSL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)) ρ =
        ros.map (·.drawn) →
      (∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
        colAtS D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec))
          (trL D.C K chal (rds ({ D.base with statement := st } : _root_.Fmt.Spec))
            (rtSL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)) ros) pl ρ op)
          (x.1.tree - D.base.firstTree) zc.1 = some zc.2) →
      PQ.viewX D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)) D.a D.xs y
          (trL D.C K chal (rds ({ D.base with statement := st } : _root_.Fmt.Spec))
            (rtSL D.C (rds ({ D.base with statement := st } : _root_.Fmt.Spec)) ros) pl ρ op) =
        _root_.Fmt.viewX ⟨D.base, D.stored⟩ o :=
    fun pl ρ op hpl hd hcol =>
      viewX_cols_tr h ⟨{ D.base with statement := st }, D.stm, D.stored⟩ K chal hbase
        (fun r hr x hx => (hg r hr x hx).imp fun n g => OnBytes.K.Left.tabGood_st D.base st x n g)
        ros o c htr pl ρ op hpl hd rc hoo ho hS hD y hy hcol
  rw [e] at hq
  exact hq pl ρ op hpl hd hcol

end TypedOracleCompiler.Run.PQ
