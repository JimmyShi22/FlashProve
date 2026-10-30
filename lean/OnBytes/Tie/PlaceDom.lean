-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PlaceDom.lean: the reading of a request's place in the binding tree, and the making of a
table's key, written over a monad with the hash as a letter (OnBytes/ChecksWithHashAsArgument/M/Proof/Place.lean,
OnBytes/ChecksWithHashAsArgument/M/Entry/Table.lean), give at `Fmt.HO Fmt.oracle`, the hash over the realised oracle
on strings, what the verifier program's own functions give, where the configuration's digest (and
for the key the table's root) has 32 bytes.

Statements and proofs. `Fmt.HO Fmt.oracle` is `Fmt.formatHash` on the hash's domain (`Fmt.HO_oracle`,
Fmt/Rules23Laws.lean). So it is shown that the calls of the two functions lie in the domain. The
place: one leaf under the number 173 and one vertex under the number 178 for each level. The key:
OnBytes/Slice/SeedsAtOracle.lean has the seeds' text at the realised oracle; here that text is shown
to be the twin's.

Main names:
  `slice_len`: a slice of n bytes has n bytes.
  `domVertexB`, `domBindLeaf`: the two kinds of call lie in the domain. After `domVertex` and
    `domLeaf` of Run/OpenDomProofs.lean, which have the numbers 166, 164 and 174.
  `climbM_dom`, `readPlaceM_dom`: at two hashes of which the second agrees with the first on the
    domain, and the first's digests have the format's lengths.
  `readPlaceM_O`: the twin's reading of a place at `Fmt.HO Fmt.oracle` is the program's `readPlace`.
  `recordSeedsM_W`: the twin's `recordSeeds` at the identity monad is `Slice.recordSeedsW`.
  `tableKeyM_O`: the twin's `tableKey` at `Fmt.HO Fmt.oracle` is the program's `tableKey`.
Premises: 32 bytes of the configuration's digest; for the key also 32 bytes of the table's root.
The numbers 173 and 178 are written as in `Fmt.bindLeafW` and `Fmt.vertexBW` (Fmt/Rules7.lean),
which have no names for them.
Limits: nothing at a drawn function. Nothing on soundness. Written for this library; it follows no
outside text.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Reading
import OnBytes.Slice.SeedsAtOracle
import Run.OpenDomProofs

set_option autoImplicit false

namespace OnBytes.Tie

open _root_.Run
open _root_.Fmt (hDom dlen)
open OnBytes.TwoPort

/-- A slice of n bytes has n bytes. -/
theorem slice_len {b : ByteArray} {i n : ℕ} {x : ByteArray} (e : Fmt.slice b i n = some x) :
    x.size = n := by
  unfold Fmt.slice at e
  split at e
  · cases e
    rw [ByteArray.size_extract]
    omega
  · cases e

/-- A vertex of the binding tree over two digests of 32 bytes lies in the hash's domain. -/
theorem domVertexB (cfg l r : ByteArray) (hc : cfg.size = 32) (hl : l.size = 32)
    (hr : r.size = 32) : hDom 178 0 0 cfg (l ++ r) = true := by
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    ByteArray.size_append, hl, hr]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, Or.inr trivial⟩, by decide⟩, by decide⟩, hc⟩,
      Or.inl (by decide)⟩,
    Fmt.leafOK_other _ _ _ rfl⟩

/-- A leaf of the binding tree, as `Fmt.leafW` spells it under the number 173 and the tree 0, lies
in the hash's domain. -/
theorem domBindLeaf (idx : ℕ) (start : ByteArray) (col : List UInt64) (salt : ByteArray)
    (hi : idx < 2 ^ 63) (hs : start.size = 32) (hW1 : 1 ≤ col.length) (hW : col.length < 2 ^ 24)
    (hsalt : Fmt.saltLenOK salt.size = true) :
    hDom 173 (Fmt.leafPlace 0 col.length (salt.size / 8)) idx start (Fmt.leafBytes col salt) =
      true := by
  simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsalt
  have ht : (0 : ℕ) < 2 ^ 16 := by decide
  have h8 : 8 * (salt.size / 8) = salt.size := by omega
  have hb : (Fmt.leafBytes col salt).size ≤ 2 ^ 32 - 144 := by
    have := size_leafBytes col salt; omega
  have hlt : Fmt.leafPlace 0 col.length (salt.size / 8) < 2 ^ 48 :=
    Fmt.leafPlace_lt _ _ _ ht hW (by omega)
  have hn : (!((173 : ℕ) == 173 || (173 : ℕ) == 174) || (0 : ℕ) == 0) = true := by decide
  have hok : Fmt.leafOK 173 (Fmt.leafPlace 0 col.length (salt.size / 8))
      (Fmt.leafBytes col salt) = true := by
    unfold Fmt.leafOK
    rw [Fmt.placeW_leafPlace _ _ _ ht hW, Fmt.placeS_leafPlace _ _ _ ht hW,
      Fmt.placeTree_leafPlace _ _ _ ht, h8, hn]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
    refine Or.inr ⟨⟨⟨⟨hW1, by omega⟩, by omega⟩, size_leafBytes' col salt⟩, ?_⟩
    have := Fmt.extract_mid (Fmt.colBytes col)
      (Fmt.zeroBytes (Fmt.fillLen col.length salt.size)) salt
    rw [size_colBytes, Fmt.size_zeros] at this
    exact congrArg ByteArray.data this
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, hlt⟩, Or.inl (by decide)⟩, ?_⟩, hb⟩, hs⟩, Or.inl (by decide)⟩, hok⟩
  simp only [Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨⟨hi, Or.inl (by decide)⟩, Or.inl (by decide)⟩

section
variable (h h' : HId) (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

include ha hz in
/-- Going up from a vertex of 32 bytes gives one result at both hashes. -/
theorem climbM_dom (cfg b : ByteArray) (hc : cfg.size = 32) :
    ∀ (levels : ℕ) (x : ByteArray) (p i : ℕ), x.size = 32 →
      M.Proof.climb (m := Id) h' cfg b levels x p i = M.Proof.climb (m := Id) h cfg b levels x p i
  | 0, _, _, _, _ => rfl
  | levels + 1, x, p, i, hx => by
    unfold M.Proof.climb
    cases hs : Fmt.slice b i 32 with
    | none => rfl
    | some sib =>
      have hsib : sib.size = 32 := slice_len hs
      dsimp only
      by_cases hp : (p % 2 == 1) = true
      · simp only [if_pos hp]
        show M.Proof.climb (m := Id) h' cfg b levels (h' 178 0 0 cfg (sib ++ x)) (p / 2) (i + 32) =
          M.Proof.climb (m := Id) h cfg b levels (h 178 0 0 cfg (sib ++ x)) (p / 2) (i + 32)
        rw [ha _ _ _ _ _ (domVertexB cfg sib x hc hsib hx)]
        exact climbM_dom cfg b hc levels _ _ _ (hz 178 0 0 cfg (sib ++ x))
      · simp only [if_neg hp]
        show M.Proof.climb (m := Id) h' cfg b levels (h' 178 0 0 cfg (x ++ sib)) (p / 2) (i + 32) =
          M.Proof.climb (m := Id) h cfg b levels (h 178 0 0 cfg (x ++ sib)) (p / 2) (i + 32)
        rw [ha _ _ _ _ _ (domVertexB cfg x sib hc hx hsib)]
        exact climbM_dom cfg b hc levels _ _ _ (hz 178 0 0 cfg (x ++ sib))

include ha hz in
/-- The reading of a place gives one result at both hashes. -/
theorem readPlaceM_dom (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : ℕ)
    (hc : cfg.size = 32) :
    M.Proof.readPlace (m := Id) h' s cfg closing b i =
      M.Proof.readPlace (m := Id) h s cfg closing b i := by
  unfold M.Proof.readPlace
  by_cases hb : (!Proof.bindingOk s) = true
  · simp only [if_pos hb]
  · simp only [if_neg hb]
    have hok : Proof.bindingOk s = true := by
      cases hq : Proof.bindingOk s with
      | true => rfl
      | false => rw [hq] at hb; exact absurd rfl hb
    unfold Proof.bindingOk at hok
    obtain ⟨hd, hsl⟩ := Bool.and_eq_true_iff.1 hok
    have hd' : s.logLeaves ≤ 48 := of_decide_eq_true hd
    cases Fmt.rdWord b i with
    | none => rfl
    | some y =>
      obtain ⟨w, i1⟩ := y
      dsimp only
      by_cases hw : 2 ^ s.logLeaves ≤ w.toNat
      · simp only [if_pos hw]
      · simp only [if_neg hw]
        cases hs : Fmt.slice b i1 s.saltBytes with
        | none => rfl
        | some salt =>
          have hsz : salt.size = s.saltBytes := slice_len hs
          have hpow : 2 ^ s.logLeaves ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hd'
          have hleaf : Fmt.bindLeafW (m := Id) h' s.logLeaves w.toNat cfg closing salt =
              Fmt.bindLeafW (m := Id) h s.logLeaves w.toNat cfg closing salt :=
            ha _ _ _ _ _ (domBindLeaf _ cfg _ salt (by omega) hc (by simp) (by simp)
              (by rw [hsz]; exact hsl))
          show Option.map _ (M.Proof.climb (m := Id) h' cfg b s.logLeaves
              (Fmt.bindLeafW (m := Id) h' s.logLeaves w.toNat cfg closing salt) w.toNat
              (i1 + s.saltBytes)) =
            Option.map _ (M.Proof.climb (m := Id) h cfg b s.logLeaves
              (Fmt.bindLeafW (m := Id) h s.logLeaves w.toNat cfg closing salt) w.toNat
              (i1 + s.saltBytes))
          have h32 : ByteArray.size
              (Fmt.bindLeafW (m := Id) h s.logLeaves w.toNat cfg closing salt) = 32 :=
            hz 173 _ _ _ _
          rw [hleaf, climbM_dom h h' ha hz cfg b hc s.logLeaves
            (Fmt.bindLeafW (m := Id) h s.logLeaves w.toNat cfg closing salt) _ _ h32]

end

/-- **The twin's reading of a place at the hash over the realised oracle is the program's.** -/
theorem readPlaceM_O (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : ℕ)
    (hc : cfg.size = 32) :
    M.Proof.readPlace (m := Id) (Fmt.HO Fmt.oracle) s cfg closing b i =
      Proof.readPlace s cfg closing b i := by
  rw [readPlaceM_dom Fmt.formatHash (Fmt.HO Fmt.oracle) (fun n t i s b hd => Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => Fmt.size_H n t i s b) s cfg closing b i hc, ← formatHashFastForm_eq_formatHash]
  exact M.AtPort.readPlace_port s cfg closing b i

/-- The twin's text of the seeds at the identity monad is the text of
OnBytes/Slice/RecordRead.lean, at every hash. -/
theorem recordSeedsM_W (h : HId) (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    M.recordSeeds (m := Id) h f name bits count =
      Slice.recordSeedsW (m := Id) h f name bits count := by
  -- by named equations, and a letter q for the round's value before the two texts are compared:
  -- written so that no checker need compute that value
  rw [Slice.recordSeedsW_pure, M.recordSeeds, M.AtPort.idBind, M.AtPort.idBind]
  generalize Fmt.Chain.queryW (m := Id) _ _ _ _ _ _ _ = q
  cases q with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- **The twin's key of a table at the hash over the realised oracle is the program's.** -/
theorem tableKeyM_O (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : ℕ) (hr : table.root.size = 32) (hc : cfg.size = 32) :
    M.tableKey (m := Id) (Fmt.HO Fmt.oracle) f cfg s table item = tableKey f cfg s table item := by
  unfold M.tableKey OnBytes.tableKey
  simp only [recordSeedsM_W, Slice.recordSeedsW_oracle_table _ _ _ hr hc]
  rfl

end OnBytes.Tie
