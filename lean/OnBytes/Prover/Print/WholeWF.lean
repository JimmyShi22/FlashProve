-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/WholeWF.lean: the parsed file that is printed of a typed proof string of a
whole file (`carrierOf`, OnBytes/Prover/Print/Carrier.lean) is one that the reader of bytes takes
(`File.WF`, OnBytes/Prover/Print/Bytes.lean); so its bytes are read back.

Main names (namespace `OnBytes.Prover.Print`).
  `okItem_itemsOf`, `wf_roundsOf`, `length_roundsOf`   a stretch's rounds
  `rise_filterMap`   rows that are made place by place, each under its own place, rise
  `mem_treeShT`      a stretch's tree number n is a tree of one of its rounds
  `wf_rowsOf`, `wf_treesOf`, `tree_treesOf`   a stretch's trees; their numbers
  `wf_storedOf`      the stored table
  `wf_carrierOf`     RootsFit D → SizesFit D s → Printable ... cfg s π → Canon ... π →
                     root.size = 32 → (magic = magicKey → the copy's number is 0) →
                     (carrierOf ... root π).WF magic
  `read_carrierOf`   so, at a magic of 8 bytes, `read magic` gives the printed file back from its
                     bytes

Limits. That a prover's string meets `Printable` and `Canon`, and the data `RootsFit` and
`SizesFit`, is not shown here. Nothing here says that the typing lays the string again of the
printed file. No prover, no oracle, no verifier.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Canon
import OnBytes.Prover.Print.Items
import Run.CodingBitsLaws
import Run.CodingPage160

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open OnBytes.Maker OnBytes.Maker.Carrier
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)

/-! ## Rounds -/

theorem okItem_itemsOf : ∀ (l : List _root_.Fmt.Item) (rts : List ByteArray) (x : PlainOf l),
    CanonI l x → l.countP (· == .root) ≤ rts.length → (∀ r ∈ rts, r.size = 32) →
    ∀ g ∈ itemsOf l rts x, okItem g
  | [], _, _, _, _, _, g, hg => nomatch hg
  | .root :: l, [], _, _, h, _, _, _ => by
    rw [List.countP_cons_of_pos (by rfl)] at h
    exact absurd h (by simp)
  | .root :: l, r :: rts, x, hc, h, hr, g, hg => by
    rw [List.countP_cons_of_pos (by rfl)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hr r List.mem_cons_self
    · exact okItem_itemsOf l rts x hc (Nat.le_of_succ_le_succ h)
        (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) g hg
  | .f :: l, rts, (x : UInt64 × PlainOf l), hc, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hc.1
    · exact okItem_itemsOf l rts x.2 hc.2 h hr g hg
  | .word :: l, rts, (x : UInt64 × PlainOf l), hc, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact trivial
    · exact okItem_itemsOf l rts x.2 hc h hr g hg
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), hc, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hc.1
    · exact okItem_itemsOf l rts x.2 hc.2 h hr g hg
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), hc, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hc.1
    · exact okItem_itemsOf l rts x.2 hc.2 h hr g hg

theorem length_roundsOf (C : CK) : ∀ (ds : List RDT) (rts : List (Dig 256))
    (pl : Plains (uLT C ds)), (roundsOf C ds rts pl).length = ds.length
  | [], _, _ => rfl
  | d :: ds, rts, (_, r) => congrArg (· + 1) (length_roundsOf C ds (rts.drop d.trees.length) r)

theorem wf_roundsOf (C : CK) : ∀ (ds : List RDT) (rts : List (Dig 256)) (pl : Plains (uLT C ds)),
    (∀ d ∈ ds, d.items.countP (· == .root) = d.trees.length) →
    rts.length = (ds.map (·.trees.length)).sum → (∀ d ∈ ds, d.items.length < 2 ^ 64) →
    CanonP C ds pl → ∀ r ∈ roundsOf C ds rts pl, r.WF
  | [], _, _, _, _, _, _, r, hr => nomatch hr
  | d :: ds, rts, (pl, rest), hf, h, hi, hc, r, hr => by
    have hd : d.items.countP (· == .root) = d.trees.length := hf d List.mem_cons_self
    have hs : rts.length = d.trees.length + (ds.map (·.trees.length)).sum := h
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨?_, ?_, hc.2.1⟩
      · show (itemsOf d.items _ _).length < 2 ^ 64
        rw [length_itemsOf]
        exact hi d List.mem_cons_self
      · refine okItem_itemsOf d.items _ _ hc.1 ?_ ?_
        · rw [hd, List.length_map, List.length_take]
          omega
        · intro b hb
          obtain ⟨e, -, rfl⟩ := List.mem_map.1 hb
          exact size_digToBytes e
    · exact wf_roundsOf C ds _ rest (fun e he => hf e (List.mem_cons_of_mem _ he))
        (by rw [List.length_drop]; omega) (fun e he => hi e (List.mem_cons_of_mem _ he)) hc.2.2 r hr

/-! ## Opened leaves -/

/-- Rows that are made place by place, each under its own place, rise. -/
theorem rise_filterMap (G : ℕ → Option Carrier.Row) (hG : ∀ y r, G y = some r → r.leaf = y)
    (N : ℕ) : fallFrom 0 (((List.range N).filterMap G).map fun r => r.leaf) = none := by
  rw [fallFrom_eq_none, List.pairwise_map]
  refine List.Pairwise.filterMap G (fun a a' hlt b hb b' hb' => ?_) List.pairwise_lt_range
  rw [hG a b hb, hG a' b' hb']
  exact hlt

theorem two_pow_lt {n : ℕ} (h : n < 64) : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) h

theorem size_ownSalt_le {start : ByteArray} {s : Rom.Bits} (h : SaltFrom start s)
    (hl : s.length ≤ 256 + 8 * 64) : (ownSalt s).size ≤ 64 := by
  obtain ⟨n, hn⟩ := (whole_iff _).1 h.2
  have e : (ownSalt s).size = n := size_bitsToBytes _ n hn
  rw [List.length_drop] at hn
  omega

/-- an opening's row -/
theorem wf_row {start : ByteArray} {x : ℕ} {col : List UInt64} {salt : Rom.Bits}
    {path : List (Dig 256)} (hx : x < 2 ^ 64) (hs : SaltFrom start salt)
    (hc : CanonO col salt path) :
    (⟨x, col, ownSalt salt, path.map digToBytes⟩ : Carrier.Row).WF :=
  ⟨hx, hc.2.1, hc.1, size_ownSalt_le hs hc.2.2.1, by
    show (path.map digToBytes).length < 2 ^ 64
    rw [List.length_map]
    exact hc.2.2.2, fun d hd => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
    exact size_digToBytes e⟩

/-- A stretch's tree number n is a tree of one of its rounds. -/
theorem mem_treeShT : ∀ (ds : List RDT) (n : ℕ) (s : _root_.Fmt.Shape), treeShT ds n = some s →
    ∃ d ∈ ds, s ∈ d.trees
  | [], _, _, h => nomatch h
  | d :: ds, n, s, h => by
    rw [treeShT_cons] at h
    by_cases hn : n < d.trees.length
    · rw [if_pos hn] at h
      exact ⟨d, List.mem_cons_self, List.mem_of_getElem? h⟩
    · rw [if_neg hn] at h
      obtain ⟨e, he, hs⟩ := mem_treeShT ds _ s h
      exact ⟨e, List.mem_cons_of_mem _ he, hs⟩

section
variable (C : CK) (ds : List RDT)
  (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))

/-- One tree's entry. -/
theorem wf_rowsOf (start : ByteArray) (hd : ∀ d ∈ ds, ∀ t ∈ d.trees, t.a < 64)
    (hs : ∀ q op, opens q = some op → SaltFrom start op.salt)
    (hc : ∀ q op, opens q = some op → CanonO (colOfSym C ds q op.sym) op.salt op.path)
    (tree chain n : ℕ) (ht : tree < 2 ^ 64) (hch : chain ≤ 2) :
    (⟨tree, chain, rowsOf C ds opens n⟩ : Carrier.TreeRows).WF := by
  unfold rowsOf
  cases hsh : treeShT ds n with
  | none => exact ⟨ht, hch, Nat.two_pow_pos 64, (fun r hr => nomatch hr), rfl⟩
  | some s =>
    obtain ⟨d, hdm, hsm⟩ := mem_treeShT ds n s hsh
    have ha := two_pow_lt (hd d hdm s hsm)
    refine ⟨ht, hch, ?_, ?_, ?_⟩
    · refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
      rw [List.length_range]
      exact ha
    · intro r hr
      obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.1 hr
      obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.1 hxr
      obtain ⟨op, hop, rfl⟩ := Option.map_eq_some_iff.1 hp
      exact wf_row (Nat.lt_trans (List.mem_range.1 hx) ha) (hs p op hop) (hc p op hop)
    · refine rise_filterMap _ (fun y r hy => ?_) _
      obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hp
      rfl

theorem length_treesOf (chain base : ℕ) :
    (treesOf C ds chain base opens).length = (ds.map (·.trees.length)).sum := by
  unfold treesOf
  rw [List.length_map, List.length_range]

theorem tree_treesOf (chain base : ℕ) :
    (treesOf C ds chain base opens).map (fun t => t.tree) =
      (List.range (ds.map (·.trees.length)).sum).map (base + ·) := by
  unfold treesOf
  rw [List.map_map]
  rfl

theorem wf_treesOf (start : ByteArray) (hd : ∀ d ∈ ds, ∀ t ∈ d.trees, t.a < 64)
    (hs : ∀ q op, opens q = some op → SaltFrom start op.salt)
    (hc : ∀ q op, opens q = some op → CanonO (colOfSym C ds q op.sym) op.salt op.path)
    (chain base : ℕ) (hb : base + (ds.map (·.trees.length)).sum < 2 ^ 64) (hch : chain ≤ 2) :
    ∀ t ∈ treesOf C ds chain base opens, t.WF := by
  intro t ht
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ht
  have hn' := List.mem_range.1 hn
  exact wf_rowsOf C ds opens start hd hs hc _ chain n (by omega) hch

end

theorem wf_storedOf (a : ℕ) (ha : a < 64) (cfg : ByteArray)
    (ext : Fin (2 ^ a) → Option (Opening 256 SgX))
    (hs : ∀ q op, ext q = some op → SaltFrom cfg op.salt)
    (hc : ∀ q op, ext q = some op → CanonO op.sym.2 op.salt op.path) :
    (storedOf a ext).length < 2 ^ 64 ∧ (∀ r ∈ storedOf a ext, r.WF) ∧
      fallFrom 0 ((storedOf a ext).map fun r => r.leaf) = none := by
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
    rw [List.length_range]
    exact two_pow_lt ha
  · intro r hr
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hr
    by_cases hlt : x < 2 ^ a
    · rw [dif_pos hlt] at hx
      obtain ⟨op, hf, rfl⟩ := Option.map_eq_some_iff.1 hx
      exact wf_row (Nat.lt_trans hlt (two_pow_lt ha)) (hs _ op hf) (hc _ op hf)
    · rw [dif_neg hlt] at hx
      cases hx
  · refine rise_filterMap _ (fun y r hy => ?_) _
    by_cases hlt : y < 2 ^ a
    · rw [dif_pos hlt] at hy
      obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl
    · rw [dif_neg hlt] at hy
      cases hy

/-! ## The parsed file -/

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)

/-- **What is printed is well formed.** -/
theorem wf_carrierOf :
  ∀ (cfg root : ByteArray) (s : Params.LinBindingShape) (magic : String)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch),
    RootsFit D → SizesFit D s → Printable C D tF tJ t3 silent run cfg s π →
    Canon C D tF tJ t3 silent run π → root.size = 32 →
    (magic = magicKey → (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy = 0) →
    (carrierOf C D tF tJ t3 silent run root π).WF magic := by
  intro cfg root s magic π hf hz hp hc hroot hcopy
  have m1 : ∀ d ∈ D.ds₁, d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃) := fun d h => List.mem_append_left _ h
  have m2 : ∀ d ∈ D.ds₂, d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃) := fun d h =>
    List.mem_append_right _ (List.mem_append_left _ h)
  have m3 : ∀ d ∈ D.ds₃, d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃) := fun d h =>
    List.mem_append_right _ (List.mem_append_right _ h)
  have hT : π.roots.length = D.t₁ + D.t₂ + (D.ds₃.map (·.trees.length)).sum := hp.roots
  have hN : D.t₁ + D.t₂ + (D.ds₃.map (·.trees.length)).sum < 2 ^ 64 := hz.trees
  have e1 : D.t₁ = (D.ds₁.map (·.trees.length)).sum := rfl
  have e2 : D.t₂ = (D.ds₂.map (·.trees.length)).sum := rfl
  have st := wf_storedOf D.a hz.stored cfg π.ext (fun q op h => (hp.ext q op h).1) hc.ext
  obtain ⟨sl, hsl, hrs⟩ := hp.rsalt
  exact
    { root := hroot
      answersCount := by
        show (List.map _ _).length < 2 ^ 64
        rw [List.length_map]
        exact hc.count
      answers := fun e he => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact hc.answers e' he'
      run1 := size_bitsToBytes _ 32 hp.salt
      copy := hc.copy
      keyCopy := hcopy
      rounds1Count := by
        show (roundsOf C D.ds₁ _ _ ++ [_]).length < 2 ^ 64
        rw [List.length_append, length_roundsOf]
        exact hz.rounds.1
      rounds1 := fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · exact wf_roundsOf C D.ds₁ _ _ (fun d h => hf d (m1 d h))
            (by rw [List.length_take]; omega) (fun d h => hz.items d (m1 d h)) hc.plain₁ r hr
        · obtain rfl := List.mem_singleton.1 hr
          exact ⟨Nat.two_pow_pos 64, (fun x hx => nomatch hx), Nat.two_pow_pos 64⟩
      run2 := hp.run2
      rounds2Count := by
        show (roundsOf C D.ds₂ _ _).length < 2 ^ 64
        rw [length_roundsOf]
        exact hz.rounds.2.1
      rounds2 := wf_roundsOf C D.ds₂ _ _ (fun d h => hf d (m2 d h))
        (by rw [List.length_take, List.length_drop]; omega) (fun d h => hz.items d (m2 d h))
        hc.plain₂
      run3 := hp.run3
      rounds3Count := by
        show (roundsOf C D.ds₃ _ _).length < 2 ^ 64
        rw [length_roundsOf]
        exact hz.rounds.2.2
      rounds3 := wf_roundsOf C D.ds₃ _ _ (fun d h => hf d (m3 d h))
        (by rw [List.length_drop, List.length_drop]; omega) (fun d h => hz.items d (m3 d h))
        hc.plain₃
      treesCount := by
        show (treesOf C D.ds₁ 0 0 _ ++ (treesOf C D.ds₂ 1 D.t₁ _ ++
          treesOf C D.ds₃ 2 (D.t₁ + D.t₂) _)).length < 2 ^ 64
        rw [List.length_append, List.length_append, length_treesOf, length_treesOf,
          length_treesOf]
        omega
      trees := fun t ht => by
        rcases List.mem_append.1 ht with ht | ht
        · exact wf_treesOf C D.ds₁ _ _ (fun d h => hz.depths d (m1 d h)) hp.own₁ hc.own₁ 0 0
            (by omega) (by omega) t ht
        · rcases List.mem_append.1 ht with ht | ht
          · exact wf_treesOf C D.ds₂ _ _ (fun d h => hz.depths d (m2 d h)) hp.own₂ hc.own₂ 1 D.t₁
              (by omega) (by omega) t ht
          · exact wf_treesOf C D.ds₃ _ _ (fun d h => hz.depths d (m3 d h)) hp.own₃ hc.own₃ 2
              (D.t₁ + D.t₂) (by omega) (by omega) t ht
      treesRise := by
        show fallFrom 0 ((treesOf C D.ds₁ 0 0 _ ++ (treesOf C D.ds₂ 1 D.t₁ _ ++
          treesOf C D.ds₃ 2 (D.t₁ + D.t₂) _)).map fun t => t.tree) = none
        rw [List.map_append, List.map_append, tree_treesOf, tree_treesOf, tree_treesOf, ← e1, ← e2,
          fallFrom_eq_none]
        have h := List.pairwise_lt_range (n := D.t₁ + (D.t₂ + (D.ds₃.map (·.trees.length)).sum))
        rw [List.range_add, List.range_add, List.map_append, List.map_map] at h
        simpa [Function.comp_def, Nat.add_assoc] using h
      storedCount := st.1
      stored := st.2.1
      storedRise := st.2.2
      bindRoot := size_digToBytes _
      place := Nat.lt_trans hp.slot (two_pow_lt hz.binding.1)
      places := by
        show 2 ^ π.path.length < 2 ^ 64
        rw [hp.path]
        exact two_pow_lt hz.binding.1
      slotSalt := by
        show (bitsToBytes (π.rsalt.take (π.rsalt.length - 64))).size ≤ 64
        rw [hrs, slotSalt_rsOf, hsl]
        exact hz.binding.2
      slotDepth := by
        show (π.path.map digToBytes).length < 2 ^ 64
        rw [List.length_map, hp.path]
        exact Nat.lt_trans hz.binding.1 (by omega)
      slotPath := fun d hd => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
        exact size_digToBytes e }

/-- So the reader of bytes gives the printed file back. -/
theorem read_carrierOf (cfg root : ByteArray) (s : Params.LinBindingShape) (magic : String)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (hm : magic.toUTF8.size = 8)
    (hf : RootsFit D) (hz : SizesFit D s) (hp : Printable C D tF tJ t3 silent run cfg s π)
    (hc : Canon C D tF tJ t3 silent run π) (hroot : root.size = 32)
    (hcopy : magic = magicKey → (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy = 0) :
    Carrier.read magic (wrFile magic (carrierOf C D tF tJ t3 silent run root π)) =
      .ok (carrierOf C D tF tJ t3 silent run root π) :=
  read_wrFile magic _ hm (wf_carrierOf C D tF tJ t3 silent run cfg root s magic π hf hz hp hc hroot
    hcopy)

end

end OnBytes.Prover.Print
