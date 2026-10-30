-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedTypedLaws.lean: the proof string that the typing of a whole file makes
(typeFile, OnBytes/Maker/TypeFile.lean) holds an opening only at the places that
OnBytes/Maker/ListedTyped.lean lists off the file as read.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

ListedOK (OnBytes/TypedOracleCompiler/Compile/Batch/ListedStrict.lean), for the file's own trees, is the premise hO,
and the like for the stored table the premise hE, of verifyWholeL_eq
(OnBytes/Maker/ListedWholeTop.lean): the two premises that are left there. verifyTyped_eq
(OnBytes/Maker/ListedTypedTop.lean) lays these theorems in.

Main definition.
  KeysHold tabs keys: keys holds the place of every row that the two look-ups can find in tabs.

Main theorems.
  atT_row, atTT_row: where a look-up gives an opening, the table has a row.
  opensT_key, mem_of_posAtT: where the typing's look-up gives an opening, the leaf is among the keys
    of its tree, if KeysHold.
  opensT_inr: the look-up behind a first round is the look-up of the rounds behind it.
  getD_range_keys: the member number k of a list made over the numbers below n.
  length_ownChain: a chain's list has one member for each written round.
  keysHold_read: KeysHold of the typing's tables at the listed positions of the file as read.
  listedOK_app: ListedOK of two stretches of rounds in a row, from ListedOK of each, if the first
    list has one member for each round of the first stretch.
  listedOK_lo, listedOK_sh: ListedOK of a chain's written rounds (local; shared) at the typing's
    look-up opensT, for every keys with KeysHold.
  listedOK_toBPrfW: ListedOK of a whole file's string at ownWhole, for such keys.
  listedOK_typeFile: if typeFile returns a string, ListedOK holds of its openings at ownOfRead.
  ext_listed_typeFile: if typeFile returns a string, each position of the stored table at which it
    holds an opening is in listedOfRead.

Limits. Nothing is said where typeFile returns nothing. The converse is not claimed: a listed place
need not hold an opening. Nothing on what an opening holds, on hashes, on what is read, on time or
memory, or on soundness. The program does not import this file.


-/
import OnBytes.Maker.ListedTyped
import OnBytes.Maker.TypeFile
import OnBytes.Maker.TablesBack
import OnBytes.Maker.TypingTLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-! ## Look-ups -/

/-- Where the look-up in one table gives an opening, the table has a row. -/
theorem atT_row {σ : Type} (sym : List UInt64 → Option σ) (tab : List (ℕ × Row3)) (x : ℕ)
    (h : atT sym tab x ≠ none) : ∃ v, tab.lookup x = some v := by
  cases e : tab.lookup x with
  | none => exact absurd (by simp only [atT, e]) h
  | some v => exact ⟨v, rfl⟩

/-- Where the look-up in the tables of all trees gives an opening, the tree has a table with a
row. -/
theorem atTT_row {σ : Type} (sym : List UInt64 → Option σ) (tabs : List (ℕ × List (ℕ × Row3)))
    (t x : ℕ) (h : atTT sym tabs t x ≠ none) :
    ∃ tab v, tabs.lookup t = some tab ∧ tab.lookup x = some v := by
  cases e : tabs.lookup t with
  | none => exact absurd (by simp only [atTT, e]) h
  | some tab =>
    have h' : atT sym tab x ≠ none := by
      intro hn
      exact h (by simp only [atTT, e]; exact hn)
    obtain ⟨v, hv⟩ := atT_row sym tab x h'
    exact ⟨tab, v, rfl, hv⟩

/-- keys holds the place of every row that the two look-ups can find. -/
def KeysHold (tabs : List (ℕ × List (ℕ × Row3))) (keys : ℕ → List ℕ) : Prop :=
  ∀ j tab x v, tabs.lookup j = some tab → tab.lookup x = some v → x ∈ keys j

/-- Where the typing's look-up gives an opening, the position's leaf is among the keys of its
tree. -/
theorem opensT_key (C : CK) (ds : List RDT) (b : ℕ) {tabs : List (ℕ × List (ℕ × Row3))}
    {keys : ℕ → List ℕ} (hk : KeysHold tabs keys) (p : OPos (uLT C ds))
    (h : opensT C ds b tabs p ≠ none) : leafAt C ds p ∈ keys (b + treeAt C ds p) := by
  obtain ⟨tab, v, h1, h2⟩ := atTT_row _ tabs _ _ h
  exact hk _ tab _ v h1 h2

/-- The look-up behind a first round is the look-up of the rounds behind it, from the number of
their first tree. -/
theorem opensT_inr (C : CK) (d : RDT) (ds : List RDT) (b : ℕ)
    (tabs : List (ℕ × List (ℕ × Row3))) :
    (fun q : OPos (uLT C ds) => opensT C (d :: ds) b tabs (.inr q)) =
      opensT C ds (b + d.trees.length) tabs := by
  funext q
  show atTT (symT' C ds q) tabs (b + (d.trees.length + treeAt C ds q)) (leafAt C ds q) =
    atTT (symT' C ds q) tabs (b + d.trees.length + treeAt C ds q) (leafAt C ds q)
  rw [Nat.add_assoc]

/-- The member number k of a list made over the numbers below n. -/
theorem getD_range_keys (f : ℕ → List ℕ) (n k : ℕ) (h : k < n) :
    ((List.range n).map f).getD k [] = f k := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## Stretches of rounds -/

/-- A chain's list has one member for each written round. -/
theorem length_ownChain (C : CK) (shared : Bool) (keys : ℕ → List ℕ) :
    ∀ (ds : List RDT) (b : ℕ), (ownChain shared keys b ds).length = (uLT C ds).length
  | [], _ => rfl
  | d :: ds, b => congrArg (· + 1) (length_ownChain C shared keys ds (b + d.trees.length))

/-- **Two stretches in a row.** -/
theorem listedOK_app {lam K : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B)
    (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (g : (p : OPos u) → Option (Opening lam (OSym u p))) (o₁ o₂ : Leaves),
    o₁.length = s.length → ListedOK s A W f o₁ → ListedOK u B V g o₂ →
    ListedOK (s ++ u) (RoundSplits.app A B) (WireSB.app W V) (opensApp f g) (o₁ ++ o₂)
  | [], _, _, _, _, _, _, _, [], _, _, _, h => h
  | [], _, _, _, _, _, _, _, _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, _, (_, _), _, (_, _), _, _, _, [], _, hl, _, _ => by cases hl
  | _ :: _, _, (_, _), _, (_, W), V, f, g, _ :: o₁, o₂, hl, h₁, h₂ =>
    ⟨h₁.1, h₁.2.1,
      listedOK_app W V (fun q => f (.inr q)) g o₁ o₂ (Nat.succ.inj hl) h₁.2.2 h₂⟩

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  {tabs : List (ℕ × List (ℕ × Row3))} {keys : ℕ → List ℕ}

/-- The leaf of a position of a written round at which the look-up gives an opening. -/
theorem mem_of_posAtT (hk : KeysHold tabs keys) (d : RDT) (ds : List RDT) (b k j : ℕ)
    (p : PosT d.trees) (h : posAtT d.trees k j = some p)
    (hf : opensT C (d :: ds) b tabs (.inl p) ≠ none) :
    j ∈ ((List.range d.trees.length).map fun k => keys (b + k)).getD k [] := by
  obtain ⟨h1, h2⟩ := in_posAtT d.trees k j p h
  have hlt : k < d.trees.length := h1 ▸ treeIn_lt d.trees p
  have h3 : leafIn d.trees p ∈ keys (b + treeIn d.trees p) :=
    opensT_key C (d :: ds) b hk (.inl p) hf
  rw [h1, h2] at h3
  rw [getD_range_keys (fun k => keys (b + k)) _ k hlt]
  exact h3

/-- **Written rounds that are local.** -/
theorem listedOK_lo (hk : KeysHold tabs keys) : ∀ (ds : List RDT) (b : ℕ),
    ListedOK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) (opensT C ds b tabs)
      (ownChain false keys b ds)
  | [], _ => trivial
  | d :: ds, b =>
    ⟨fun _ _ _ _ h => (by cases h),
      fun k _ j p h hf => mem_of_posAtT C hk d ds b k j p h hf,
      opensT_inr C d ds b tabs ▸ listedOK_lo hk ds (b + d.trees.length)⟩

/-- **Written rounds that are shared.** -/
theorem listedOK_sh (hk : KeysHold tabs keys) : ∀ (ds : List RDT) (b : ℕ),
    ListedOK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
      (opensT C ds b tabs) (ownChain true keys b ds)
  | [], _ => trivial
  | d :: ds, b =>
    ⟨fun k _ j p h hf => mem_of_posAtT C hk d ds b k j p h hf,
      fun _ _ _ _ h => (by cases h),
      opensT_inr C d ds b tabs ▸ listedOK_sh hk ds (b + d.trees.length)⟩

end

/-! ## The whole file -/

section
variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The string of a whole file, at tables whose rows' places keys holds.** -/
theorem listedOK_toBPrfW (pF : TF) (pJ : TJ) (p3 : T3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ D.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π)
    (keys : ℕ → List ℕ) (hk : KeysHold tabs keys) :
    ListedOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh π.opens (ownWhole D keys) := by
  unfold toBPrfW at h
  split at h
  · cases h
    refine ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), ?_⟩
    refine listedOK_app (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ
      (opensT C D.ds₁ 0 tabs) _ (ownChain false keys 0 D.ds₁) _
      (length_ownChain C false keys D.ds₁ 0) (listedOK_lo C K chal hk D.ds₁ 0) ?_
    refine ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), ?_⟩
    refine listedOK_app (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃
      (opensT C D.ds₂ D.t₁ tabs) _ (ownChain true keys D.t₁ D.ds₂) _
      (length_ownChain C true keys D.ds₂ D.t₁) (listedOK_sh C K chal hk D.ds₂ D.t₁) ?_
    exact ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h),
      listedOK_lo C K chal hk D.ds₃ (D.t₁ + D.t₂)⟩
  · cases h

end

/-- The listed positions of the trees' openings hold the place of every row that the two look-ups
can find in the tables. -/
theorem keysHold_read {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : tabsWFull W sb r = some tabs) :
    KeysHold tabs (leavesUnder (ownRowsW W r)) := by
  intro j tab x v hj hx
  obtain ⟨c, s, pt⟩ := v
  obtain ⟨z, _, _, hz, hm, _⟩ := tabsWFull_back h j tab x c s pt hj hx
  exact List.mem_flatMap.2 ⟨(j, z), List.mem_filter.2 ⟨hz, beq_self_eq_true j⟩,
    (List.of_mem_zip hm).1⟩

section
variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (a : ℕ) (W : Three.Whole) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The typing's string holds an opening of the file's own trees only at the leaves listed off the
file as read.** -/
theorem listedOK_typeFile (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r = some π) :
    ListedOK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh π.opens (ownOfRead a W r) := by
  obtain ⟨tabs, ext, ht, _, hπ⟩ :=
    typeFile_some C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r π h
  exact listedOK_toBPrfW C K chal (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs ext salt path r
    π hπ _ (keysHold_read ht)

/-- **The typing's string holds an opening of the stored table only at the positions listed off the
file as read.** -/
theorem ext_listed_typeFile (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r = some π) :
    ∀ p, π.ext p ≠ none → p ∈ listedOfRead a W r := by
  obtain ⟨tabs, ext, _, he, hπ⟩ :=
    typeFile_some C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r π h
  have e : π.ext = ext := by
    unfold toBPrfW at hπ
    split at hπ
    · cases hπ
      rfl
    · cases hπ
  obtain ⟨tab, htab, rfl⟩ := Option.map_eq_some_iff.1 he
  intro p hp
  rw [e] at hp
  obtain ⟨⟨c, s, pt⟩, hv⟩ := atT_row _ tab p.val hp
  obtain ⟨t, z, _, hz, hm, _⟩ := extTabWFull_back htab p.val c s pt hv
  refine List.mem_filterMap.2 ⟨p.val, List.mem_flatMap.2 ⟨(t, z), hz, (List.of_mem_zip hm).1⟩, ?_⟩
  exact dif_pos p.isLt

end

end OnBytes.Maker

#print axioms OnBytes.Maker.listedOK_typeFile
#print axioms OnBytes.Maker.ext_listed_typeFile
