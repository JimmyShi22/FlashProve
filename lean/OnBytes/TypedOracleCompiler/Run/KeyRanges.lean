-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/KeyRanges.lean: the data of `Chain162G.ChainG` for a typed chain that runs through
THREE chains of a file with four seams: which typed rounds are rounds of a file's chain, and each
one's label and index.

The shape of `Stretches` (OnBytes/TypedOracleCompiler/Slice/Plain3.lean) is: a seam (typed round 0); the first
stretch's n₁ rounds (typed rounds 1 to n₁); two seams (n₁ + 1, n₁ + 2); the second stretch's n₂
rounds (n₁ + 3 to n₁ + 2 + n₂); a seam (n₁ + n₂ + 3); the third stretch's n₃ rounds. In a key file
each stretch is a chain of its own, with a label of its own and its rounds counted from 1. This file
has that arithmetic, and the written round that stands at a typed round.
 - `Three`: three lengths and three labels; `Three.on`, `lab`, `idx`, `back`; `Three.hback`: for
   three different labels, `back l j = some i` exactly if i is on, with the label l and the index j;
 - `rdAt G i`: the written round of G at the typed round i, if there is one; `kindAt`, `workAt`,
   `ordAt`: its kind's number; its bits of work; whether the typed tail of its answer is block 1 of
   the format's row: where it has work, or is of the kind "sealed";
 - `SealsPlain G`: a condition, used by no theorem here: the first two stretches end in a sealed
   round without work, and no other round is sealed;
 - `mkF2`, `selF2`, with both laws: the head `.f2 none ρ`;
 - `keyChain G λ₁ λ₂ λ₃ h rc hrc : ChainG L tg`: the data, for any interface, tag and code rc of
   (roots, plain part).

Main definitions: `Three`, `Three.on`, `Three.lab`, `Three.idx`, `Three.back`, `rdAt`, `kindAt`,
`workAt`, `ordAt`, `SealsPlain`, `keyChain`.
Main theorem: `Three.hback`.

Not claimed. Data alone. That the order `ordAt` is the format's: at a round without work that is not
sealed, and at a round with work, it is the library's own order; at a sealed round without work it
sends the typed tail to the row's block 1, where the format has the seal, and the typed block 0 to
the row's block 0: then what the typed round "draws" is not the seal. A sealed round WITH work,
which the format page does not admit (R5.3: a seal has w = 0; nothing here asks that rule of G's
rounds), would have its seal at block 2. That case is NOT BORNE: `ordAt` would then say "block 1",
which is the chain's next value; the code stays lawful, and the next seam's typed query would not
hold the seal (`SealsPlain` shuts this case out). Nothing ties G to a key file. Nothing on
soundness. The sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.Chain162G
import OnBytes.TypedOracleCompiler.Run.PlainAt

set_option autoImplicit false

namespace TypedOracleCompiler.Run.KeyRanges
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Chain162G
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- Three lengths and three labels. -/
structure Three where
  /-- the first chain's number of rounds -/
  n₁ : ℕ
  /-- the second chain's -/
  n₂ : ℕ
  /-- the third chain's -/
  n₃ : ℕ
  /-- the first chain's label -/
  l₁ : ℕ
  /-- the second chain's -/
  l₂ : ℕ
  /-- the third chain's -/
  l₃ : ℕ

namespace Three
variable (T : Three)

/-- Whether the typed round i is a round of one of the three chains. -/
def on (i : ℕ) : Bool :=
  decide ((1 ≤ i ∧ i ≤ T.n₁) ∨ (T.n₁ + 3 ≤ i ∧ i ≤ T.n₁ + 2 + T.n₂) ∨
    (T.n₁ + T.n₂ + 4 ≤ i ∧ i ≤ T.n₁ + T.n₂ + 3 + T.n₃))

/-- The label of the chain in which the typed round i lies. -/
def lab (i : ℕ) : ℕ := if i ≤ T.n₁ then T.l₁ else if i ≤ T.n₁ + 2 + T.n₂ then T.l₂ else T.l₃

/-- The round's index in its chain. -/
def idx (i : ℕ) : ℕ :=
  if i ≤ T.n₁ then i else if i ≤ T.n₁ + 2 + T.n₂ then i - (T.n₁ + 2) else i - (T.n₁ + T.n₂ + 3)

/-- The typed round of a label and an index. -/
def back (l j : ℕ) : Option ℕ :=
  if l = T.l₁ ∧ 1 ≤ j ∧ j ≤ T.n₁ then some j
  else if l = T.l₂ ∧ 1 ≤ j ∧ j ≤ T.n₂ then some (T.n₁ + 2 + j)
  else if l = T.l₃ ∧ 1 ≤ j ∧ j ≤ T.n₃ then some (T.n₁ + T.n₂ + 3 + j)
  else none

/-- For three different labels, `back` finds exactly the rounds that are on. -/
theorem hback (h12 : T.l₁ ≠ T.l₂) (h13 : T.l₁ ≠ T.l₃) (h23 : T.l₂ ≠ T.l₃) (l j i : ℕ) :
    T.back l j = some i ↔ (T.on i = true ∧ T.lab i = l ∧ T.idx i = j) := by
  unfold back on lab idx
  rw [decide_eq_true_iff]
  constructor
  · intro h
    split_ifs at h with c1 c2 c3
    · obtain rfl := Option.some.inj h
      rw [if_pos c1.2.2, if_pos c1.2.2]
      exact ⟨Or.inl c1.2, c1.1.symm, rfl⟩
    · obtain rfl := Option.some.inj h
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      exact ⟨Or.inr (Or.inl (by omega)), c2.1.symm, by omega⟩
    · obtain rfl := Option.some.inj h
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact ⟨Or.inr (Or.inr (by omega)), c3.1.symm, by omega⟩
  · rintro ⟨ho, hl, hj⟩
    rcases ho with ho | ho | ho
    · rw [if_pos ho.2] at hl hj
      rw [if_pos ⟨hl.symm, by omega, by omega⟩, hj]
    · rw [if_neg (by omega), if_pos ho.2] at hl hj
      rw [if_neg (by rintro ⟨e, -, -⟩; exact h12 (e.symm.trans hl.symm).symm.symm),
        if_pos ⟨hl.symm, by omega, by omega⟩]
      exact congrArg some (by omega)
    · rw [if_neg (by omega), if_neg (by omega)] at hl hj
      rw [if_neg (by rintro ⟨e, -, -⟩; exact h13 (e.symm.trans hl.symm).symm.symm),
        if_neg (by rintro ⟨e, -, -⟩; exact h23 (e.symm.trans hl.symm).symm.symm),
        if_pos ⟨hl.symm, by omega, by omega⟩]
      exact congrArg some (by omega)

end Three

/-! ## The written round at a typed round -/

variable (G : Stretches)

/-- The lengths of G's stretches, with three labels. -/
def threeOf (l₁ l₂ l₃ : ℕ) : Three := ⟨G.ds₁.length, G.ds₂.length, G.ds₃.length, l₁, l₂, l₃⟩

/-- The written round of G at the typed round i, if there is one. -/
def rdAt (i : ℕ) : Option PQ.RD :=
  if i ≤ G.ds₁.length then (if i = 0 then none else G.ds₁[i - 1]?)
  else if i ≤ G.ds₁.length + 2 + G.ds₂.length then
    (if i ≤ G.ds₁.length + 2 then none else G.ds₂[i - (G.ds₁.length + 3)]?)
  else if i = G.ds₁.length + G.ds₂.length + 3 then none
  else G.ds₃[i - (G.ds₁.length + G.ds₂.length + 4)]?

/-- Its kind's number; 0 where there is none. -/
def kindAt (i : ℕ) : ℕ := ((rdAt G i).map fun d => d.kind.num).getD 0

/-- Its bits of work; 0 where there is none. -/
def workAt (i : ℕ) : ℕ := ((rdAt G i).map fun d => d.entry.work).getD 0

/-- Whether the typed tail of its answer is block 1 of the format's row: where the round has work,
or is of the kind "sealed". -/
def ordAt (i : ℕ) : Bool :=
  ((rdAt G i).map fun d => decide (d.entry.work ≠ 0) || decide (d.kind = .sealed)).getD false

/-- The seals are plain: the last round of the first and of the second stretch is of the kind
"sealed" and has no work, and no other round of the three stretches is of that kind. Under this
condition the order `ordAt` sends the typed tail of a sealed round to the block in which the format
has the seal. A sealed round WITH work, which the format page does not admit (R5.3), would have its
seal at the row's block 2, which no order of `Chain162G.ChainG` makes the tail. -/
def SealsPlain : Prop :=
  (∃ r, G.ds₁.getLast? = some r ∧ r.kind = .sealed ∧ r.entry.work = 0) ∧
  (∃ r, G.ds₂.getLast? = some r ∧ r.kind = .sealed ∧ r.entry.work = 0) ∧
  (∀ r ∈ G.ds₁.dropLast ++ (G.ds₂.dropLast ++ G.ds₃), r.kind ≠ .sealed)

/-! ## The head of a later round -/

variable {I X : Type}

/-- The head of a later round's query that holds the chain value ρ and no late instance. -/
def mkF2 (ρ : Bits) : Head 256 X := .f2 none ρ

/-- The chain value of such a head. -/
def selF2 : Head 256 X → Option Bits
  | .f2 none ρ => some ρ
  | _ => none

/-- Reading undoes making. -/
theorem selF2_mkF2 (ρ : Bits) : selF2 (X := X) (mkF2 ρ) = some ρ := rfl

/-- Making undoes reading. -/
theorem mkF2_selF2 (h : Head 256 X) (ρ : Bits) (hs : selF2 h = some ρ) : mkF2 ρ = h := by
  cases h with
  | f2 xl r =>
    cases xl with
    | none => exact congrArg (Head.f2 none) (Option.some.inj hs).symm
    | some _ => cases hs
  | f1 _ _ _ => cases hs
  | f3 _ _ => cases hs
  | f4 _ _ => cases hs
  | f5 _ => cases hs

/-- The data of the one code for all hashes under 162 of a key's typed chain, for three
different labels and any code of (roots, plain part) whose strings hold a nonce's word. -/
def keyChain {L : BatchProtocolWithLeafBody I X} {tg : Tag} (l₁ l₂ l₃ : ℕ) (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃)
    (h23 : l₂ ≠ l₃) (rc : ℕ → PCode (List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)))
    (hrc : ∀ i y s, (rc i).put y = some s → 64 ≤ s.length) : ChainG L tg where
  on := (threeOf G l₁ l₂ l₃).on
  lab := (threeOf G l₁ l₂ l₃).lab
  idx := (threeOf G l₁ l₂ l₃).idx
  back := (threeOf G l₁ l₂ l₃).back
  hback := (threeOf G l₁ l₂ l₃).hback h12 h13 h23
  ord := ordAt G
  kind := kindAt G
  work := workAt G
  rc := rc
  hrc := hrc
  mkH := mkF2
  selH := selF2
  hsel := selF2_mkF2
  hmk := mkF2_selF2

end TypedOracleCompiler.Run.KeyRanges
