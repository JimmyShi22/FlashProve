-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Lands.lean: the twin's checks of a key file and of a proof file over the
monad of trees of queries, with the hash that asks the one oracle. Run at f each is the same check
at the identity monad and the hash over the function that f induces; none tosses a coin. After the
pattern of Entry/RoadLands.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Model.SpineKeeps

set_option autoImplicit false

namespace OnBytes.TwoPort.M.Lands

open _root_.ZKCP
open _root_.Run
open OnBytes.Params (TableName KeyChains ProofChains)

/-! ## The key file -/

theorem keyCheck_det (f : _root_.ZKCP.Oracle 256) (k : KeyChains) (file : ByteArray) :
    (M.Key.check (Fmt.HM askB) k file).det f = M.Key.check (m := Id) (Fmt.HO (oB f)) k file := by
  have e := KeyHom.app_check (detHom f) (Fmt.HM askB) k file
  rw [detHom_on_HM] at e
  exact e

theorem keyCheck_noCoin (k : KeyChains) (file : ByteArray) :
    (M.Key.check (Fmt.HM askB) k file).NoCoin :=
  KeyHom.ok_check (Fmt.HM askB) (RoadLands.noCoinKeeps 256)
    (fun n t i s b => noCoin_HM n t i s b) k file

theorem readKey_det (f : _root_.ZKCP.Oracle 256) (k : KeyChains) (table : TableName)
    (file : ByteArray) (j : Nat) (s : Session) :
    (M.Key.readKey (Fmt.HM askB) k table file j s).run.det f =
      (M.Key.readKey (m := Id) (Fmt.HO (oB f)) k table file j s).run := by
  have e := KeyHom.rel_readKey (detHom f) (Fmt.HM askB) k table file j s
  rw [detHom_on_HM] at e
  exact e

theorem readKey_noCoin (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    (s : Session) : (M.Key.readKey (Fmt.HM askB) k table file j s).run.NoCoin :=
  KeyHom.okR_readKey (Fmt.HM askB) (RoadLands.noCoinKeeps 256)
    (fun n t i s b => noCoin_HM n t i s b) k table file j s

/-! ## The proof file -/

theorem proofCheck_det (f : _root_.ZKCP.Oracle 256) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (reply : E) (links : Blk OnBytes.Proof.LinksResult)
    (file : ByteArray) :
    (M.Proof.check (Fmt.HM askB) c table copy request words reply links file).det f =
      M.Proof.check (m := Id) (Fmt.HO (oB f)) c table copy request words reply links file := by
  have e := SpineHom.app_proofCheck (detHom f) (Fmt.HM askB) c table copy request words reply links
    file
  rw [detHom_on_HM] at e
  exact e

theorem proofCheck_noCoin (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk OnBytes.Proof.LinksResult) (file : ByteArray) :
    (M.Proof.check (Fmt.HM askB) c table copy request words reply links file).NoCoin :=
  SpineKeeps.ok_proofCheck (RoadLands.noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) c table copy request words reply links file

theorem readProof_det (f : _root_.ZKCP.Oracle 256) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (block : Blk OnBytes.Proof.FirstEnd) (file : ByteArray)
    (s : Session) :
    (M.Proof.readProof (Fmt.HM askB) c table copy request words block file s).run.det f =
      (M.Proof.readProof (m := Id) (Fmt.HO (oB f)) c table copy request words block file s).run :=
        by
  have e := SpineHom.rel_readProof (detHom f) (Fmt.HM askB) c table copy request words block file s
  rw [detHom_on_HM] at e
  exact e

theorem readProof_noCoin (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (block : Blk OnBytes.Proof.FirstEnd) (file : ByteArray) (s : Session) :
    (M.Proof.readProof (Fmt.HM askB) c table copy request words block file s).run.NoCoin :=
  SpineKeeps.okR_readProof (RoadLands.noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) c table copy request words block file s

/-! ## The entry file's reading, and the table's key (for the check itself: Entry/RoadLands.lean)
-/

theorem entryRead_det (f : _root_.ZKCP.Oracle 256) (p : Params.Link) (first : TableName)
    (file : ByteArray) :
    (M.Entry.read (Fmt.HM askB) p first file).det f =
      M.Entry.read (m := Id) (Fmt.HO (oB f)) p first file := by
  have e := RoadHom.app_read (detHom f) (Fmt.HM askB) p first file
  rw [detHom_on_HM] at e
  exact e

theorem entryRead_noCoin (p : Params.Link) (first : TableName) (file : ByteArray) :
    (M.Entry.read (Fmt.HM askB) p first file).NoCoin :=
  RoadKeeps.ok_read (RoadLands.noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) p first file

theorem tableKey_det (f : _root_.ZKCP.Oracle 256) (fl : Fmt.Fld) (cfg : ByteArray)
    (s : Params.IndexShape) (table : TableName) (item : Nat) :
    (M.tableKey (Fmt.HM askB) fl cfg s table item).det f =
      M.tableKey (m := Id) (Fmt.HO (oB f)) fl cfg s table item := by
  have e := RoadHom.app_tableKey (detHom f) (Fmt.HM askB) fl cfg s table item
  rw [detHom_on_HM] at e
  exact e

theorem tableKey_noCoin (fl : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : TableName) (item : Nat) : (M.tableKey (Fmt.HM askB) fl cfg s table item).NoCoin :=
  RoadKeeps.ok_tableKey (RoadLands.noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) fl cfg s table item

end OnBytes.TwoPort.M.Lands
