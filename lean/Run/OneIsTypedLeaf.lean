-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTypedLeaf.lean: the encoding of leaf queries writes every symbol, if the trees are numbered
one after the other and are small (`leafCL_some`, under its hypotheses).

A part of the proof that the run over a single oracle is the run at typed oracle functions
(`one_is_typed`, Run/OneIsTypedTop.lean, under its hypotheses), for the generic construction. The
encoding of leaf queries is `leafCL` (Run/PageQChain.lean) and `leafQ` (Run/PageQ.lean). The point:
`leafCL` writes a leaf of a later round only if no earlier round's code reads its string. What a
tree's code reads begins with that tree's word (it is a code: what it reads it also writes). Two
trees with different numbers have different words, within the label's bounds: a number below 2^16,
fewer than 2^24 words in a column, fewer than 2^8 words of salt. A round without a tree has no
symbol at all.

Sources. Written against the leaf's label as the format page (docs/format/FORMAT.md, which comes
with the programs) had it in an edition that is not the one that ships (Fmt/Rules23.lean,
leafPlace). The label (FORMAT.md, R2.1) is the same in a second edition, also not the one that
ships.

1. What the file contains.
   `Numbered ft ds`; `SmallTrees ds`.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `leaf1_some`; `leafCL_some`.
   `leaf_fits`: If `OKQ S = true`, `Numbered ft (rds S)`, `SmallTrees (rds S)` and
     `S.plan.salt / 8 < 2^8`, then a leaf query on a symbol of the protocol, with a typed salt of
     256 + 8 · (the plan's salt) bits, passes `fitLeaf` (Run/OneIsTyped.lean).

4. What is not claimed. That a description's trees are numbered so: Run/OneIsTypedTop.lean. No
   statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.OneIsTyped

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Thin Run.Twin

theorem pVec_some : ∀ (W : ℕ) (v : Fin W → UInt64), ((pVec W).1.put v).isSome = true
  | 0, _ => rfl
  | W + 1, v =>
    PCode.cons_some pU64 64 pU64_len (fun _ => (pVec W).1)
      ((Fin.consEquiv fun _ : Fin (W + 1) => UInt64).symm v) (pU64_some _) (pVec_some W _)

theorem pFinAt_some (lo n : ℕ) (x : Fin n) (h : lo + x.val < 2 ^ 64) :
    ((pFinAt lo n).put x).isSome = true := by
  show (pWord.put (lo + x.val)).isSome = true
  rw [pWord_put _ h]
  rfl

/-- The leaves of one tree are all written, if 2^a + x can be spelled (`ht`). -/
theorem leaf1_some (t : Option _root_.Fmt.Shape) (salt : ℕ) (ht : posN t + posN t ≤ 2 ^ 64)
    (y : Fin (posN t) × (Fin (colW t) → UInt64)) :
    ((leaf1 t salt).put y).isSome = true := by
  refine PCode.pre_some _ _ _
    (PCode.cons_some _ _ _ _ (y.1, (y.2, ())) (pFinAt_some _ _ _ (by have := y.1.isLt; omega))
      (PCode.cons_some _ _ _ _ (y.2, ()) (pVec_some _ _) rfl))

/-- What one tree's code reads begins with that tree's word. -/
theorem leaf1_parse (t : Option _root_.Fmt.Shape) (salt : ℕ) (s : List Bool)
    (a : Fin (posN t) × (Fin (colW t) → UInt64)) (h : (leaf1 t salt).parse s = some a) :
    ∃ r, s = leafWord t salt ++ r :=
  leaf1_pre t salt a s ((leaf1 t salt).put_parse s a h)

/-- The trees of some rounds have the numbers ft, ft + 1, .. -/
def Numbered : ℕ → List RD → Prop
  | _, [] => True
  | ft, d :: ds => match d.tree with
    | none => Numbered ft ds
    | some sh => sh.tree = ft ∧ Numbered (ft + 1) ds

/-- Under `Numbered ft ds`: what the code of some rounds' leaves writes begins with the word of a
tree whose number is ft or more. -/
theorem leafCL_word (C : CK) (salt : ℕ) :
    ∀ (ds : List RD) (ft : ℕ), Numbered ft ds →
      ∀ (y : SymAny (uL C ds)) (m : List Bool), (leafCL C salt ds).put y = some m →
        ∃ sh : _root_.Fmt.Shape,
          ft ≤ sh.tree ∧ (∃ d ∈ ds, d.tree = some sh) ∧ ∃ r, m = leafWord (some sh) salt ++ r
  | [], _, _, _, _, h => by cases h
  | d :: ds, ft, hN, y, m, h => by
      have h0 : (((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).sumF
              (leafCL C salt ds)).put
            ((Equiv.sumSigmaDistrib (α := Fin (posN d.tree))
              (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y) = some m := h
      rcases hz : (Equiv.sumSigmaDistrib
          (α := Fin (posN d.tree)) (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y with a | b
      · rw [hz] at h0
        have h1 : (leaf1 d.tree salt).put ((Equiv.sigmaEquivProd _ _) a) = some m := h0
        obtain ⟨r, hr⟩ := leaf1_pre d.tree salt _ m h1
        cases ht : d.tree with
        | none =>
          have a1 : Fin (posN d.tree) := a.1
          rw [ht] at a1
          exact a1.elim0
        | some sh =>
          have hN' : (match d.tree with
            | none => Numbered ft ds
            | some sh => sh.tree = ft ∧ Numbered (ft + 1) ds) := hN
          rw [ht] at hN'
          exact ⟨sh, Nat.le_of_eq hN'.1.symm, ⟨d, List.mem_cons_self, ht⟩, r, ht ▸ hr⟩
      · rw [hz] at h0
        have h1 := PCode.sumF_inr _ _ b m h0
        have hN' : (match d.tree with
          | none => Numbered ft ds
          | some sh => sh.tree = ft ∧ Numbered (ft + 1) ds) := hN
        cases ht : d.tree with
        | none =>
          rw [ht] at hN'
          obtain ⟨sh, h2, ⟨d', hd', e⟩, r⟩ := leafCL_word C salt ds ft hN' b m h1
          exact ⟨sh, h2, ⟨d', List.mem_cons_of_mem _ hd', e⟩, r⟩
        | some sh0 =>
          rw [ht] at hN'
          obtain ⟨sh, h2, ⟨d', hd', e⟩, r⟩ := leafCL_word C salt ds (ft + 1) hN'.2 b m h1
          exact ⟨sh, by omega, ⟨d', List.mem_cons_of_mem _ hd', e⟩, r⟩

/-- Two trees' words differ if their numbers do, within the label's bounds (`h1`, `h2`, `hs`). -/
theorem leafWord_ne (salt : ℕ) (s1 s2 : _root_.Fmt.Shape) (h1 : s1.tree < 2 ^ 16 ∧ s1.W < 2 ^ 24)
    (h2 : s2.tree < 2 ^ 16 ∧ s2.W < 2 ^ 24) (hs : salt / 8 < 2 ^ 8) (hne : s1.tree ≠ s2.tree) :
    leafWord (some s1) salt ≠ leafWord (some s2) salt := by
  intro e
  have b1 : _root_.Fmt.leafPlace s1.tree s1.W (salt / 8) < 2 ^ 48 := by
    unfold _root_.Fmt.leafPlace; omega
  have b2 : _root_.Fmt.leafPlace s2.tree s2.W (salt / 8) < 2 ^ 48 := by
    unfold _root_.Fmt.leafPlace; omega
  have e1 : pWord.put (164 + 65536 * _root_.Fmt.leafPlace s1.tree s1.W (salt / 8)) =
      some (leafWord (some s1) salt) :=
    pWord_put _ (by omega)
  have e2 : pWord.put (164 + 65536 * _root_.Fmt.leafPlace s2.tree s2.W (salt / 8)) =
      some (leafWord (some s1) salt) := by
    rw [e]; exact pWord_put _ (by omega)
  have := pWord.inj e1 e2
  unfold _root_.Fmt.leafPlace at this
  omega

/-- The trees are small: a number below 2^16, fewer than 2^24 words in a column, a depth of at most
63. -/
def SmallTrees (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ sh, d.tree = some sh → (sh.tree < 2 ^ 16 ∧ sh.W < 2 ^ 24) ∧ sh.a ≤ 63

theorem posN_small (t : Option _root_.Fmt.Shape) (h : ∀ sh, t = some sh → sh.a ≤ 63) :
    posN t + posN t ≤ 2 ^ 64 := by
  cases t with
  | none => exact Nat.zero_le _
  | some sh =>
    have h1 : (2 : ℕ) ^ sh.a ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (h sh rfl)
    show 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64
    omega

/-- Every symbol with its position is written, if salt / 8 < 2^8 (`hsalt`), the trees' numbers go up
one by one and the trees are small. -/
theorem leafCL_some (C : CK) (salt : ℕ) (hsalt : salt / 8 < 2 ^ 8) :
    ∀ (ds : List RD) (ft : ℕ), Numbered ft ds → SmallTrees ds →
      ∀ y : SymAny (uL C ds), ((leafCL C salt ds).put y).isSome = true
  | [], _, _, _, y => y.1.elim
  | d :: ds, ft, hN, hS, y => by
      show ((((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).sumF
            (leafCL C salt ds)).put
          ((Equiv.sumSigmaDistrib (α := Fin (posN d.tree))
              (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y)).isSome = true
      have hS' : SmallTrees ds := fun d' hd' => hS d' (List.mem_cons_of_mem _ hd')
      have hN' : (match d.tree with
        | none => Numbered ft ds
        | some sh => sh.tree = ft ∧ Numbered (ft + 1) ds) := hN
      rcases (Equiv.sumSigmaDistrib
          (α := Fin (posN d.tree)) (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y with a | b
      · exact leaf1_some d.tree salt (posN_small _ fun sh e => (hS d List.mem_cons_self sh e).2) _
      · show (((leafCL C salt ds).put b).filter fun s =>
            (((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).parse s).isNone).isSome =
          true
        cases ht : d.tree with
        | none =>
          rw [ht] at hN'
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (leafCL_some C salt hsalt ds ft hN' hS' b)
          rw [hm]
          have hp : (((leaf1 none salt).congr (Equiv.sigmaEquivProd _ _).symm).parse m).isNone =
              true := by
            show (((leaf1 none salt).parse m).map _).isNone = true
            cases hq : (leaf1 none salt).parse m with
            | none => rfl
            | some a => exact a.1.elim0
          simp [Option.filter, hp]
        | some sh0 =>
          rw [ht] at hN'
          obtain ⟨m, hm⟩ :=
            Option.isSome_iff_exists.1 (leafCL_some C salt hsalt ds (ft + 1) hN'.2 hS' b)
          rw [hm]
          have hp : (((leaf1 (some sh0) salt).congr (Equiv.sigmaEquivProd _ _).symm).parse
                m).isNone = true := by
            show (((leaf1 (some sh0) salt).parse m).map _).isNone = true
            cases hq : (leaf1 (some sh0) salt).parse m with
            | none => rfl
            | some a =>
              exfalso
              obtain ⟨r, hr⟩ := leaf1_parse (some sh0) salt m a hq
              obtain ⟨sh, h2, ⟨d', hd', e⟩, r', hr'⟩ := leafCL_word C salt ds (ft + 1) hN'.2 b m hm
              have hw : leafWord (some sh0) salt = leafWord (some sh) salt :=
                List.append_inj_left (hr.symm.trans hr')
                  (by rw [leafWord, leafWord, length_u64n, length_u64n])
              exact leafWord_ne salt sh0 sh (hS d List.mem_cons_self sh0 ht).1 (hS' d' hd' sh e).1
                hsalt (by have := hN'.1; omega) hw
          simp [Option.filter, hp]

section
variable (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (dec : View → Bool) (h : OKQ S = true)

/-- Under `h` (`OKQ S = true`), `hN`, `hS` and `hsalt`: a leaf query on a symbol of the protocol,
with a salt of the format's length (`hl`), fits. -/
theorem leaf_fits (ft : ℕ) (hN : Numbered ft (rds S)) (hS : SmallTrees (rds S))
    (hsalt : S.plan.salt / 8 < 2 ^ 8) (p : OPos (Twin.up (SOf C (rds S))))
    (a : OSym (Twin.up (SOf C (rds S))) p) (salt : Bits)
    (hl : salt.length = 256 + 8 * S.plan.salt) :
    fitLeaf S C K dec h (⟨some (.inr ⟨Tag.onl, ⟨p, a⟩⟩), salt⟩ : LeafIn (LfQ S C dec ())) =
      true := by
  unfold fitLeaf
  show ((if salt.length = 256 + 8 * S.plan.salt then
      ((leafQ S C dec).put ⟨p, a⟩).map fun m =>
        pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)) else none) : Option (List Bool)).isSome =
    true
  rw [if_pos hl]
  have : ((leafQ S C dec).put ⟨p, a⟩).isSome = true := by
    cases p with
    | inl e => exact e.elim
    | inr q =>
      show (((leafCL C S.plan.salt (rds S)).put ⟨q, a⟩).filter fun s =>
          ((PCode.empty (Σ p : Empty, OSym (Twin.up (SOf C (rds S))) (.inl p))).parse
            s).isNone).isSome = true
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.1 (leafCL_some C S.plan.salt hsalt (rds S) ft hN hS ⟨q, a⟩)
      rw [hm]
      rfl
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 this
  rw [hm]
  rfl

end

end Run.PQ
