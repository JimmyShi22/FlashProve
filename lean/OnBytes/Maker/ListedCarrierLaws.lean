-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedCarrierLaws.lean: the proof string that is laid of an outside parser's carrier
(File.toBPrf, OnBytes/Maker/CarrierTyping.lean) holds an opening only at the places that
OnBytes/Maker/ListedCarrier.lean lists off the same carrier.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

These are the two premises on the string and the lists under which the verifier along lists is the
compiled verifier at a whole file (verifyWholeL_eq, OnBytes/Maker/ListedWholeTop.lean): ListedOK
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedStrict.lean) for the file's own trees, and the like for the stored
table.

Over OnBytes/Maker/ListedTypedLaws.lean: its laws on the look-ups hold for all tables (KeysHold,
listedOK_lo, listedOK_sh, listedOK_app, length_ownChain, atT_row); mem_of_lookup is
OnBytes/Maker/TablesLaws.lean's. The proof of listedOK_carrier says that of listedOK_toBPrfW again
at the carrier's tables: File.toBPrf lays the field opens by toBPrfW's text at the carrier's tables,
and no equation between the two is stated.

Main theorems.
  keysHold_carrier: leavesOfCarrier k holds the place of every row that the two look-ups find in
    the carrier's tables (File.tabs).
  listedOK_carrier: if a string is laid of the carrier, ListedOK holds of its openings at
    ownOfCarrier.
  ext_listed_carrier: if a string is laid of the carrier, each position of the stored table at which
    it holds an opening is in listedOfCarrier.
  toBPrf_of_At: a string that File.toBPrfAt lays at the binding tree's shape s is the string that
    File.toBPrf lays at 2 ^ s.logLeaves places: so the two laws above hold of it.

Limits. The carrier is any carrier: nothing is asked of the tool that wrote it. Nothing is said
where no string is laid. The converse is not claimed: a listed place need not hold an opening.
None of the tests that the typing of a file as read makes on its tables (tabsWFull, extTabWFull,
OnBytes/Maker/Tables.lean) stands at a carrier, and no law ties File.toBPrf to toBPrfW or typeFile.
Nothing on what an opening holds, on hashes, on what is read, on time or memory, or on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedCarrier
import OnBytes.Maker.CarrierTyping
import OnBytes.Maker.ListedTypedLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-- **The leaves listed off the carrier hold the place of every row of the carrier's tables.** -/
theorem keysHold_carrier (D : WholeD) (k : Carrier.File) :
    KeysHold (k.tabs D) (leavesOfCarrier k) := by
  intro j tab x v hj hx
  have h1 : (j, tab) ∈ k.trees.map fun t =>
      (t.tree, t.rows.map (Carrier.Row.row3 (k.runOf (Carrier.senderOf D t.tree)))) :=
    mem_of_lookup _ j tab hj
  obtain ⟨t, ht, e⟩ := List.mem_map.1 h1
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  subst e1
  subst e2
  obtain ⟨row, hr, er⟩ := List.mem_map.1 (mem_of_lookup _ x v hx)
  have ex : row.leaf = x := congrArg Prod.fst er
  exact List.mem_flatMap.2 ⟨t, List.mem_filter.2 ⟨ht, beq_self_eq_true _⟩,
    List.mem_map.2 ⟨row, hr, ex⟩⟩

section
variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The carrier's string holds an opening of the file's own trees only at the leaves listed off
the carrier.** -/
theorem listedOK_carrier (k : Carrier.File) (cfg : ByteArray) (places : ℕ) (pF : TF) (pJ : TJ)
    (p3 : T3)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : k.toBPrf C D tF tJ t3 silent run cfg places pF pJ p3 = some π) :
    ListedOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh π.opens (ownOfCarrier D k) := by
  have hk := keysHold_carrier D k
  unfold Carrier.File.toBPrf at h
  split at h
  · cases h
    refine ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), ?_⟩
    refine listedOK_app (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ
      (opensT C D.ds₁ 0 (k.tabs D)) _ (ownChain false (leavesOfCarrier k) 0 D.ds₁) _
      (length_ownChain C false (leavesOfCarrier k) D.ds₁ 0) (listedOK_lo C K chal hk D.ds₁ 0) ?_
    refine ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), ?_⟩
    refine listedOK_app (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃
      (opensT C D.ds₂ D.t₁ (k.tabs D)) _ (ownChain true (leavesOfCarrier k) D.t₁ D.ds₂) _
      (length_ownChain C true (leavesOfCarrier k) D.ds₂ D.t₁)
      (listedOK_sh C K chal hk D.ds₂ D.t₁) ?_
    exact ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h),
      listedOK_lo C K chal hk D.ds₃ (D.t₁ + D.t₂)⟩
  · cases h

/-- **The carrier's string holds an opening of the stored table only at the positions listed off the
carrier.** -/
theorem ext_listed_carrier (k : Carrier.File) (cfg : ByteArray) (places : ℕ) (pF : TF) (pJ : TJ)
    (p3 : T3) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : k.toBPrf C D tF tJ t3 silent run cfg places pF pJ p3 = some π) :
    ∀ p, π.ext p ≠ none → p ∈ listedOfCarrier D.a k := by
  unfold Carrier.File.toBPrf at h
  split at h
  · cases h
    intro p hp
    obtain ⟨v, hv⟩ := atT_row _ (k.stored.map (Carrier.Row.row3 cfg)) p.val hp
    obtain ⟨row, hr, er⟩ := List.mem_map.1 (mem_of_lookup _ p.val v hv)
    have ex : row.leaf = p.val := congrArg Prod.fst er
    exact List.mem_filterMap.2 ⟨p.val, List.mem_map.2 ⟨row, hr, ex⟩, dif_pos p.isLt⟩
  · cases h

/-- A string of File.toBPrfAt is File.toBPrf's at the shape's number of places. -/
theorem toBPrf_of_At (k : Carrier.File) (cfg : ByteArray) (s : Params.LinBindingShape) (pF : TF)
    (pJ : TJ) (p3 : T3) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3 = some π) :
    k.toBPrf C D tF tJ t3 silent run cfg (2 ^ s.logLeaves) pF pJ p3 = some π := by
  unfold Carrier.File.toBPrfAt at h
  split at h
  · exact h
  · cases h

end

end OnBytes.Maker

#print axioms OnBytes.Maker.keysHold_carrier
#print axioms OnBytes.Maker.listedOK_carrier
#print axioms OnBytes.Maker.ext_listed_carrier
#print axioms OnBytes.Maker.toBPrf_of_At
