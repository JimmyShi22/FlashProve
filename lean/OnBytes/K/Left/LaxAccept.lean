-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxAccept.lean: the decision's clause of the lax verifier's yes, from one yes of the
strict reader and the decision's yes on the reader's view.



The field `accept` of the record `LaxDebts` (OnBytes/K/Left/Lax.lean), its part "the view". What
`accept_view` (OnBytes/K/Left/LaxView.lean) asks of what was read is paid from the reader's own yes,
by `view_feed` (OnBytes/K/Left/LaxViewFeed.lean) and `agree_read`
(OnBytes/K/Left/LaxViewAgree.lean).

Main theorem.
 `accept_read`   the clause, in `LaxDebts`' letters.

Asked. Of the typed description D: the test of OnBytes/TypedOracleCompiler `PQ.ok D.base`; the chain has random
bytes; all stored tables have the depth D.a and items 0 or 1; each of the two tables is opened at
most once; `okX`. Of D with the reader's statement st put in: the test of OnBytes/TypedOracleCompiler, with the
random bytes counted as standing in the file. The strict reader's yes, at the hash over any function
O, under D's two parts with st put in. The typing's yes. Of the chain: it draws what the reader
drew; all tests of work pass. `ListedX` (the record's own field). The decision says yes on the
reader's view, at any description with D's stored tables and D's number of the first tree.

Not claimed. That any of these holds at a file or at a description: none is shown at any description
here. That the decision at the instance x is the program's (the record's part "the keys"). Nothing
on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.Left.LaxView
import OnBytes.K.Left.LaxViewFeed
import OnBytes.K.Left.LaxViewAgree

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open TypedOracleCompiler.Slice (opsOf ListedX assembleS PSXE wqXE)

/-- The decision's clause, from the strict reader's yes and the decision's yes on the reader's
view. -/
theorem _root_.OnBytes.K.Left.accept_read {X : Type} (D : XD) (hok : PQ.ok D.base = true)
    (st : ByteArray) (O : ByteArray → ByteArray)
    (hokb : PQ.ok (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
      ⟨{ D.base with statement := st }, D.stored⟩ seen b i = some (o, j))
    (dec : X → View → Bool) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : passSL D.C D.ds ρ.2 = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (okx : okX D.ds D.a D.xs = true)
    (listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXE D dec).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)))
    (S : _root_.Fmt.SpecX) (hsto : S.stored = D.stored)
    (hft : S.base.firstTree = D.base.firstTree) (hdec : dec x (_root_.Fmt.viewX S o) = true) :
    (PSXE D dec).up.loc.accept x
      ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
        ((none, some []), rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true := by
  obtain ⟨c, rc, ho, htr, hsent, hS, hlen, hSok⟩ :=
    OnBytes.K.Left.view_feed D st O hokb hn seen b i o j e
  have hbase : ({ D.base with statement := st } : _root_.Fmt.Spec).ok = true := by
    have h' := hSok
    unfold _root_.Fmt.SpecX.ok at h'
    simp only [Bool.and_eq_true] at h'
    exact h'.1.1
  exact OnBytes.K.Left.accept_view (_root_.Fmt.HO O) D hok st dec x o π hπ ρ hd hpass c rc ho htr
    hsent hS hlen hSok hD honce okx listed
    (OnBytes.K.Left.agree_read (_root_.Fmt.HO O) ⟨{ D.base with statement := st }, D.stored⟩ hokb
      seen b i o j e)
    hbase S hsto hft hdec

end TypedOracleCompiler.Run.PQ
