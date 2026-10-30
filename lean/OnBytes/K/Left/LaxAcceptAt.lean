-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxAcceptAt.lean: the field `accept` of what OnBytes/K/Left/LaxAt.lean lists as still
owed at a ground (`LaxRest`): the written link's verifier accepts the typed transcript, at
`entryXD G c` and at what the strict reader read under the program's own description at two tables,
if the decision says yes on the reader's view.

`accept_view` (OnBytes/K/Left/LaxView.lean) shows the clause for any typed description D, from what
`view_feed` (LaxViewFeed.lean) draws out of the reader's yes, `agree_read` (LaxViewAgree.lean), the
field `listed`, and conditions on D. Here these are paid at a ground.

Main names:
  `stored_of`: all stored tables have the description's depth and name the statement's item 0 or 1.
  `accept_at`: the clause for any decision and instance.
  `accept_rest`: the clause in the letters of `LaxRest`.

Hypotheses of `accept_at`: the limits of OnBytes/TypedOracleCompiler at `entryXD G c`; the line's limits test at the
empty statement; among the description's openings of stored tables at most one names the
statement's item 1 and at most one another item (at the two grounds:
OnBytes/K/Left/LaxReal.lean); the reader's equation; the typing's yes; the verifier messages draw
what the reader drew and pass all tests of work; the decision's yes on the reader's view.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxRestAt
import OnBytes.K.Left.LaxView
import OnBytes.K.Left.LaxViewFeed
import OnBytes.K.Left.LaxViewAgree

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (EntryGround linkAtCfg AskedE withinX)
open _root_.Compile TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View)

/-- All stored tables have the description's depth and name the statement's item 0 or 1. -/
theorem stored_of (G : EntryGround) (c : ByteArray)
    (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true) :
    ∀ t ∈ (entryXD G c).stored.flatten, t.sh.a = (entryXD G c).a ∧ t.item ≤ 1 := by
  intro t ht
  have hD := xdok_of G c hw
  simp only [PQ.XD.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hD
  exact ⟨(hD.2 t ht).1.1, (hD.2 t ht).2⟩

section
variable (G : EntryGround) (c : ByteArray) (first further : Params.TableName)
  (hok : PQ.ok (entryXD G c).base = true)
  (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)
  (honce : ((entryXD G c).stored.flatten.map (·.item == 1)).Nodup)
  (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : Fmt.ChainOut)
  (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
    (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) seen b i =
      some (o, j))

include hok hw honce e in
/-- The field `accept` at a ground. -/
theorem accept_at {X : Type} (dec : X → View → Bool) (x : X)
    (π : OneProtocolProof 256 (PSXE (entryXD G c) dec).up) (hπ : assembleS (entryXD G c) dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true)
    (hdec : dec x (Fmt.viewX (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)) o) = true) :
    (PSXE (entryXD G c) dec).up.loc.accept x
      ((wqXE (entryXD G c) dec).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE (entryXD G c) dec).up.loc.shape (PSXE (entryXD G c) dec).up.ann
        (wqXE (entryXD G c) dec).sh
        ((none, some []), PQ.rtSL (entryXD G c).C (entryXD G c).ds o.rounds.toList) π.plains ρ
        π.opens) = true := by
  have hSok := OnBytes.Tie.readX_ok _ _ seen b i _ e
  have hokb := okb_at G c first further hok hSok
  obtain ⟨c0, rc, ho, htr, hsent, hS, hlen, hSok'⟩ := view_feed (entryXD G c)
    (Params.Link.statement first further) Fmt.oracle hokb rfl seen b i o j e
  have hbase : ({ (entryXD G c).base with
      statement := Params.Link.statement first further } : Fmt.Spec).ok = true := by
    have h2 := hSok'
    unfold Fmt.SpecX.ok at h2
    simp only [Bool.and_eq_true] at h2
    exact h2.1.1
  exact accept_view (Fmt.HO Fmt.oracle) (entryXD G c) hok (Params.Link.statement first further)
    dec x o π hπ ρ hd hpass c0 rc ho htr hsent hS hlen hSok' (stored_of G c hw) honce
    (descr_of G c hw).2 (listed_at G c first further hok seen b i j o e hw dec x ρ hd)
    (agree_read _ _ hokb seen b i o j e) hbase
    (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) rfl rfl hdec

end

/-- `LaxRest.accept`. -/
theorem accept_rest (G : EntryGround) (c : ByteArray) (hok : PQ.ok (entryXD G c).base = true)
    (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)
    (honce : ((entryXD G c).stored.flatten.map (·.item == 1)).Nodup) (a : AskedE)
    (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement a.first a.further)) seen b
        i = some (a.out, j))
    (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up)
    (hπ : assembleS (entryXD G c) (decAt G c) a.out = some π)
    (hdec : decAt G c (xOfAskedC _ _ a) (Fmt.viewX (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement a.first a.further)) a.out) = true)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true) :
    (PSXE (entryXD G c) (decAt G c)).up.loc.accept (xOfAskedC _ _ a)
      ((wqXE (entryXD G c) (decAt G c)).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE (entryXD G c) (decAt G c)).up.loc.shape (PSXE (entryXD G c) (decAt G c)).up.ann
        (wqXE (entryXD G c) (decAt G c)).sh (rtsAt G c a.out) π.plains ρ π.opens) = true :=
  accept_at G c a.first a.further hok hw honce seen b i j a.out e (decAt G c) _ π hπ ρ hd hpass
    hdec

end OnBytes.K.Left
