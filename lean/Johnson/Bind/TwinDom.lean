-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinDom.lean: the committer that runs (Johnson/Bind/Twin.lean) gives one value at two
hashes that agree on the domain of the format's hash. BOTH HASHES ARE LETTERS: this file names no
hash function. Statements and proofs, in the form of the library's own laws of that kind
(`Run.queryW_dom`, Run/StrictDomProofs.lean; `Run.leavesW_dom`, Run/OpenDomProofs.lean).

Why. The committer is one text over a variable hash. What is evaluated takes it at one hash, what is
proved takes it at another form of a hash; the two forms are known to agree on a domain alone
(`Fmt.hDom`, Fmt/Rules23.lean). So every call that the committer makes has to be shown to lie in it.

Main names (namespace `Bind.Twin`).
  `Fits S files`: the shapes and public files at which every call lies in the domain: a salt of 40,
    48, 56 or 64 bytes; fewer than 2^24 rows; a leaf's index below 2^63; the public files' string
    and the commitment ID's string within the hash's bound on lengths.
  `fits_full`, `fits_small`: two members: the full size's shape and the small stored example's;
    `files_three`: three public files of at most 2^31 bytes together are within the bound.
  **`commitW_dom`**: at two hashes h and h' that agree on the domain, h's answers having the
    format's lengths, and at every table: `commitW h' S files T = commitW h S files T`, where
    `Fits S files`.
Limits. An equation between two values of one Lean text. No binding of the commitment (the opening
form, `BindsWith`, VerifiableInference/MoreStatements.lean), no correctness of extraction and no
index privacy is stated here. Nothing on any hash function and nothing on any program.

-/
import Johnson.Bind.TwinTree
import Run.StrictDomProofs
import Run.PageXStmSize
import OnBytes.Slice.SeedsAtOracle
import OnBytes.Tie.DigestPoint
import OnBytes.Tie.IdKey
import Fmt.RecordSeedsLaws
import Fmt.ChainStmLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
open Fmt (Ext hDom dlen)
open Compile (pairUpF levelsF rootOf)

/-! ### The predicate, and two members -/

/-- **The shapes and public files at which every call of the committer lies in the domain of the
format's hash.** -/
structure Fits (S : Shape) (files : List ByteArray) : Prop where
  salt : Fmt.saltLenOK S.sigma = true
  rows : S.v < 24
  places : S.a ≤ 62
  files : (Fmt.configBytes files).size ≤ 2 ^ 32 - 144
  id : 176 + 24 * (S.s * (S.cube + 1)) + 24 * (2 ^ S.v * S.s) ≤ 2 ^ 32 - 144

/-- The full size's shape is a member, at all public files within the bound. -/
theorem fits_full (files : List ByteArray) (hf : (Fmt.configBytes files).size ≤ 2 ^ 32 - 144) :
    Fits ⟨32, 402653184, 44040191, 11, 1, 40⟩ files :=
  ⟨by decide, by decide, by decide, hf, by decide +kernel⟩

/-- The small stored example's shape is a member, at all public files within the bound. -/
theorem fits_small (files : List ByteArray) (hf : (Fmt.configBytes files).size ≤ 2 ^ 32 - 144) :
    Fits ⟨23, 524288, 65535, 8, 1, 40⟩ files :=
  ⟨by decide, by decide, by decide, hf, by decide +kernel⟩

/-- Three public files of at most 2^31 bytes together are within the bound. -/
theorem files_three (pol lay KL : ByteArray) (h : pol.size + lay.size + KL.size ≤ 2 ^ 31) :
    (Fmt.configBytes [pol, lay, KL]).size ≤ 2 ^ 32 - 144 := by
  have e : (Fmt.configBytes [pol, lay, KL]).size = 32 + pol.size + lay.size + KL.size := by
    simp only [Fmt.configBytes, Fmt.cat, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil, ByteArray.size_append, Fmt.size_u64n, Fmt.size_text, ByteArray.size_empty]
    omega
  rw [e]
  omega

/-! ### Trees over lists, at two node functions that agree on a set that is closed under them -/

section
variable {D : Type} (G : D → Prop) (hN hN' : D → D → D)

/-- One depth up, at two node functions that agree on G: the same list, if all entries are in G. -/
theorem pairUpF_congr (hc : ∀ a b, G a → G b → hN' a b = hN a b) :
    ∀ l : List D, (∀ x ∈ l, G x) → pairUpF hN' l = pairUpF hN l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, hl => by
    rw [Compile.pairUpF_cons₂, Compile.pairUpF_cons₂,
      hc a b (hl a (by simp)) (hl b (by simp)),
      pairUpF_congr hc t fun x hx => hl x (by simp [hx])]

/-- One depth up stays in G, if G is closed under the node function. -/
theorem pairUpF_all (hg : ∀ a b, G a → G b → G (hN a b)) :
    ∀ l : List D, (∀ x ∈ l, G x) → ∀ x ∈ pairUpF hN l, G x
  | [], _ => fun _ hx => absurd hx List.not_mem_nil
  | [_], hl => hl
  | a :: b :: t, hl => fun x hx => by
    rw [Compile.pairUpF_cons₂] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hg a b (hl a (by simp)) (hl b (by simp))
    · exact pairUpF_all hg t (fun y hy => hl y (by simp [hy])) x hx

/-- All depths, at two node functions that agree on G, which is closed under one of them. -/
theorem levelsF_congr (hc : ∀ a b, G a → G b → hN' a b = hN a b)
    (hg : ∀ a b, G a → G b → G (hN a b)) :
    ∀ (d : Nat) (l : List D), (∀ x ∈ l, G x) → levelsF hN' d l = levelsF hN d l
  | 0, _, _ => rfl
  | d + 1, l, hl => by
    rw [Compile.levelsF_succ, Compile.levelsF_succ, pairUpF_congr G hN hN' hc l hl,
      levelsF_congr hc hg d _ (pairUpF_all G hN hg l hl)]

/-- The root of a tree over a list that is not empty lies in G. -/
theorem rootOf_all [Inhabited D] (hg : ∀ a b, G a → G b → G (hN a b)) :
    ∀ (d : Nat) (l : List D), l ≠ [] → (∀ x ∈ l, G x) → G (rootOf (levelsF hN d l))
  | 0, [], h, _ => absurd rfl h
  | 0, a :: _, _, hl => hl a (by simp)
  | d + 1, l, h, hl => by
    rw [rootOf_levelsF_succ]
    exact rootOf_all hg d _ (pairUpF_ne_nil hN l h) (pairUpF_all G hN hg l hl)

end

/-! ### Lengths -/

/-- Numbering keeps the length. -/
theorem length_numbered {β : Type} : ∀ (k : Nat) (l : List β), (Fmt.numbered k l).length = l.length
  | _, [] => rfl
  | k, _ :: xs => congrArg (· + 1) (length_numbered (k + 1) xs)

/-- Lists of one length c, one behind the other: as many entries as lists times c. -/
theorem length_flatMap_const {α β : Type} (f : α → List β) (c : Nat) (hf : ∀ a, (f a).length = c) :
    ∀ l : List α, (l.flatMap f).length = l.length * c
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hf a, length_flatMap_const f c hf l,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- There are as many answers as rows times seeds. -/
theorem length_answers (S : Shape) (T : Table) (seeds : List (List Ext × Ext)) :
    (answers S T seeds).length = 2 ^ S.v * seeds.length := by
  unfold answers
  rw [length_flatMap_const _ seeds.length fun b => by
    rw [List.length_map, length_numbered, List.length_map]]
  rw [List.length_range]
  rfl

/-- A column has as many words as the table has rows. -/
theorem length_column (S : Shape) (T : Table) (x : Nat) :
    (columnOf S (laid S T) x).length = 2 ^ S.v := by
  unfold columnOf laid
  rw [List.length_map, List.length_map, List.length_range]
  rfl

/-- The length of the commitment ID's string. -/
theorem size_published (cfg name : ByteArray) (seeds given : List Ext) :
    (Fmt.publishedBytes cfg name seeds given []).size =
      cfg.size + name.size + 32 + 24 * seeds.length + 24 * given.length := by
  unfold Fmt.publishedBytes
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
    Fmt.size_text, _root_.Run.PQ.size_listExt, _root_.Run.PQ.size_listExt]
  have e : (Fmt.list id ([] : List ByteArray)).size = 8 := rfl
  rw [e]
  omega

/-! ### The committer's steps at two hashes -/

section
variable (h h' : _root_.Run.HId)
  (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

include ha in
/-- A leaf's call lies in the domain: so the two hashes give one value there. -/
theorem leafId_dom (S : Shape) (cfg : ByteArray) (col : Nat → List UInt64) (salt : Nat → ByteArray)
    (x : Nat) (hs : Fmt.saltLenOK S.sigma = true) (hc : cfg.size = 32) (hx : 2 ^ S.a + x < 2 ^ 63)
    (h1 : 1 ≤ (col x).length) (h2 : (col x).length < 2 ^ 24) :
    leafId h' S (fun _ => cfg) col salt x = leafId h S (fun _ => cfg) col salt x :=
  ha _ _ _ _ _ (_root_.Run.domLeaf true 0 _ cfg (col x) (Fmt.fit S.sigma (salt x)) (by decide) hx hc
    h1 h2 (by rw [OnBytes.Tie.size_fit]; exact hs) rfl)

include hz in
/-- A leaf's value has 32 bytes. -/
theorem size_leafId (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) (x : Nat) : (leafId h S start col salt x).size = 32 :=
  hz _ _ _ _ _

include ha in
/-- A vertex's call over two values of 32 bytes lies in the domain. -/
theorem vertexId_dom (cfg l r : ByteArray) (hc : cfg.size = 32) (hl : l.size = 32)
    (hr : r.size = 32) : vertexId h' cfg l r = vertexId h cfg l r :=
  ha _ _ _ _ _ (_root_.Run.domVertex cfg l r hc hl hr)

include hz in
/-- A vertex's value has 32 bytes. -/
theorem size_vertexId (cfg l r : ByteArray) : (vertexId h cfg l r).size = 32 := hz _ _ _ _ _

include ha hz in
/-- The root at two hashes; it has 32 bytes. -/
theorem rootW_dom (S : Shape) (cfg : ByteArray) (col : Nat → List UInt64) (salt : Nat → ByteArray)
    (hs : Fmt.saltLenOK S.sigma = true) (hc : cfg.size = 32) (hp : S.a ≤ 62)
    (h1 : ∀ x, 1 ≤ (col x).length) (h2 : ∀ x, (col x).length < 2 ^ 24) :
    Id.run (rootW h' S cfg (fun _ => cfg) col salt) =
        Id.run (rootW h S cfg (fun _ => cfg) col salt) ∧
      (Id.run (rootW h S cfg (fun _ => cfg) col salt)).size = 32 := by
  have hpow : 2 ^ S.a + 2 ^ S.a ≤ 2 ^ 63 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    have e : (2 : Nat) ^ 63 = 2 ^ 62 + 2 ^ 62 := by decide
    omega
  have hl : (List.range (2 ^ S.a)).map (leafId h' S (fun _ => cfg) col salt) =
      (List.range (2 ^ S.a)).map (leafId h S (fun _ => cfg) col salt) :=
    List.map_congr_left fun x hx => leafId_dom h h' ha S cfg col salt x hs hc
      (by have := List.mem_range.1 hx; omega) (h1 x) (h2 x)
  have hall : ∀ y ∈ (List.range (2 ^ S.a)).map (leafId h S (fun _ => cfg) col salt),
      y.size = 32 := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
    exact size_leafId h hz S _ col salt x
  have hne : (List.range (2 ^ S.a)).map (leafId h S (fun _ => cfg) col salt) ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [List.length_map, List.length_range, List.length_nil] at this
    exact absurd this (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  rw [rootW_id, rootW_id, hl,
    levelsF_congr (fun y : ByteArray => y.size = 32) (vertexId h cfg) (vertexId h' cfg)
      (fun a b ha' hb' => vertexId_dom h h' ha cfg a b hc ha' hb')
      (fun a b _ _ => size_vertexId h hz cfg a b) S.a _ hall]
  exact ⟨rfl, rootOf_all (fun y : ByteArray => y.size = 32) (vertexId h cfg)
    (fun a b _ _ => size_vertexId h hz cfg a b) S.a _ hne hall⟩

include ha in
/-- The drawing of the seeds at two hashes. -/
theorem recordSeedsW_dom (f : Fmt.Fld) (name : ByteArray) (v a : Nat) (hn : name.size ≤ 2 ^ 31) :
    Id.run (Fmt.recordSeedsW h' f name v a) = Id.run (Fmt.recordSeedsW h f name v a) := by
  have e0 : Id.run (Fmt.recordFirstW h' name) = Id.run (Fmt.recordFirstW h name) :=
    ha _ _ _ _ _ (OnBytes.Slice.seedFirst_dom name hn)
  rw [Fmt.recordSeedsW_run, Fmt.recordSeedsW_run, e0,
    _root_.Run.queryW_dom h h' ha ⟨Fmt.recordLabel, Id.run (Fmt.recordFirstW h name), 0⟩
      ByteArray.empty .seeds 0 0 _ (show 0 + 1 < 2 ^ 63 by decide)
      (show ByteArray.empty.size + 16 ≤ 2 ^ 32 - 144 by decide)]

include ha in
/-- The committer's seeds at two hashes, at a name of at most 2^31 bytes. -/
theorem seedsW_dom (S : Shape) (name : ByteArray) (hn : name.size ≤ 2 ^ 31) :
    Id.run (seedsW h' S name) = Id.run (seedsW h S name) := by
  unfold seedsW
  split
  · rfl
  · show (Id.run (Fmt.recordSeedsW h' .two name S.cube S.s)).getD [] =
      (Id.run (Fmt.recordSeedsW h .two name S.cube S.s)).getD []
    rw [recordSeedsW_dom h h' ha .two name S.cube S.s hn]

/-- What is drawn is no longer than the shape says. -/
theorem seedsW_le (S : Shape) (name : ByteArray) :
    (Id.run (seedsW h S name)).length ≤ S.s ∧
      (Fmt.flatSeeds (Id.run (seedsW h S name))).length ≤ S.s * (S.cube + 1) := by
  unfold seedsW
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · show ((Id.run (Fmt.recordSeedsW h .two name S.cube S.s)).getD []).length ≤ S.s ∧
      (Fmt.flatSeeds ((Id.run (Fmt.recordSeedsW h .two name S.cube S.s)).getD [])).length ≤
        S.s * (S.cube + 1)
    cases e : Id.run (Fmt.recordSeedsW h .two name S.cube S.s) with
    | none => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    | some l =>
      have hsh := Fmt.recordSeedsW_shaped h .two name S.cube S.s l e
      exact ⟨Nat.le_of_eq hsh.1, Nat.le_of_eq (Fmt.flatSeeds_ok .two S.cube S.s l hsh).1⟩

/-- The committer's last steps, written out. -/
theorem closeW_id (S : Shape) (cfg root : ByteArray)
    (answersAt : List (List Ext × Ext) → List Ext) :
    Id.run (closeW h S cfg root answersAt) =
      ⟨root, nameOf S root cfg, Id.run (seedsW h S (nameOf S root cfg)),
        answersAt (Id.run (seedsW h S (nameOf S root cfg))),
        Id.run (Fmt.publishedIDW h cfg (nameOf S root cfg)
          (Fmt.flatSeeds (Id.run (seedsW h S (nameOf S root cfg))))
          (answersAt (Id.run (seedsW h S (nameOf S root cfg)))) [])⟩ := rfl

include ha in
/-- The committer's last steps at two hashes: the ID's string is within the hash's bound. -/
theorem closeW_dom (S : Shape) (T : Table) (cfg root : ByteArray) (hc : cfg.size = 32)
    (hr : root.size = 32)
    (hid : 176 + 24 * (S.s * (S.cube + 1)) + 24 * (2 ^ S.v * S.s) ≤ 2 ^ 32 - 144) :
    Id.run (closeW h' S cfg root (answers S T)) = Id.run (closeW h S cfg root (answers S T)) := by
  have hname : (nameOf S root cfg).size = 112 := by
    unfold nameOf
    rw [OnBytes.Tie.size_tableName, hr, hc]
  have hn : (nameOf S root cfg).size ≤ 2 ^ 31 := by
    rw [hname]
    decide
  obtain ⟨b1, b2⟩ := seedsW_le h S (nameOf S root cfg)
  have b3 : 2 ^ S.v * (Id.run (seedsW h S (nameOf S root cfg))).length ≤ 2 ^ S.v * S.s :=
    Nat.mul_le_mul_left _ b1
  rw [closeW_id, closeW_id, seedsW_dom h h' ha S _ hn]
  have e : Id.run (Fmt.publishedIDW h' cfg (nameOf S root cfg)
      (Fmt.flatSeeds (Id.run (seedsW h S (nameOf S root cfg))))
      (answers S T (Id.run (seedsW h S (nameOf S root cfg)))) []) =
      Id.run (Fmt.publishedIDW h cfg (nameOf S root cfg)
        (Fmt.flatSeeds (Id.run (seedsW h S (nameOf S root cfg))))
        (answers S T (Id.run (seedsW h S (nameOf S root cfg)))) []) :=
    ha _ _ _ _ _ (_root_.Run.dom0 179 0 _ (by decide) (by decide) (by decide) (by
      rw [size_published, length_answers, hc, hname]
      omega))
  rw [e]

include ha hz in
/-- **AT TWO HASHES THAT AGREE ON THE DOMAIN THE COMMITTER GIVES ONE VALUE.** The section's two
premises: h and h' agree wherever `hDom` says yes (ha); h's answers have the format's lengths (hz).
-/
theorem commitW_dom (S : Shape) (files : List ByteArray) (T : Table) (fits : Fits S files) :
    commitW (m := Id) h' S files T = commitW (m := Id) h S files T := by
  have e0 : Id.run (Fmt.configDigestW h' files) = Id.run (Fmt.configDigestW h files) :=
    ha _ _ _ _ _ (_root_.Run.dom0 169 2 _ (by decide) (by decide) (by decide) fits.files)
  have hc : (Id.run (Fmt.configDigestW h files)).size = 32 := hz _ _ _ _ _
  have hv : (2 : Nat) ^ S.v < 2 ^ 24 := Nat.pow_lt_pow_right (by decide) fits.rows
  obtain ⟨r1, r2⟩ := rootW_dom h h' ha hz S (Id.run (Fmt.configDigestW h files))
    (columnOf S (laid S T)) T.salt fits.salt hc fits.places
    (fun x => by rw [length_column]; exact Nat.two_pow_pos _)
    (fun x => by rw [length_column]; exact hv)
  show Id.run (closeW h' S (Id.run (Fmt.configDigestW h' files))
      (Id.run (rootW h' S (Id.run (Fmt.configDigestW h' files))
        (fun _ => Id.run (Fmt.configDigestW h' files)) (columnOf S (laid S T)) T.salt))
      (answers S T)) =
    Id.run (closeW h S (Id.run (Fmt.configDigestW h files))
      (Id.run (rootW h S (Id.run (Fmt.configDigestW h files))
        (fun _ => Id.run (Fmt.configDigestW h files)) (columnOf S (laid S T)) T.salt))
      (answers S T))
  rw [e0, r1]
  exact closeW_dom h h' ha S T _ _ hc r2 fits.id

end

end Bind.Twin

#print axioms Bind.Twin.fits_full
#print axioms Bind.Twin.fits_small
#print axioms Bind.Twin.files_three
#print axioms Bind.Twin.pairUpF_congr
#print axioms Bind.Twin.pairUpF_all
#print axioms Bind.Twin.levelsF_congr
#print axioms Bind.Twin.rootOf_all
#print axioms Bind.Twin.length_numbered
#print axioms Bind.Twin.length_flatMap_const
#print axioms Bind.Twin.length_answers
#print axioms Bind.Twin.length_column
#print axioms Bind.Twin.size_published
#print axioms Bind.Twin.leafId_dom
#print axioms Bind.Twin.size_leafId
#print axioms Bind.Twin.vertexId_dom
#print axioms Bind.Twin.size_vertexId
#print axioms Bind.Twin.rootW_dom
#print axioms Bind.Twin.recordSeedsW_dom
#print axioms Bind.Twin.seedsW_dom
#print axioms Bind.Twin.seedsW_le
#print axioms Bind.Twin.closeW_id
#print axioms Bind.Twin.closeW_dom
#print axioms Bind.Twin.commitW_dom
