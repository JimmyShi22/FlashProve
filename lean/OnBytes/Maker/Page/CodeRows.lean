-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CodeRows.lean: what the walks owe of typed oracle functions g (`CodeOwes`,
OnBytes/Maker/WalksOf.lean), from one law on g at the leaf oracle and one at the node oracle.

OnBytes/Maker/Page/CodeAt.lean pays `CodeOwes` at the family `gJ P O` of a page. It uses two facts
on that family and nothing else of it. Here these two are premises on a letter g, so that the law
can be called at another family that meets them.

  `LeafRow g O bd Ql`   at a leaf query that meets the condition Ql, and whose body and typed salt
                     spell a call (`leafOf bd`, OnBytes/Maker/Page/Trees.lean), g answers with the
                     digest of O at that call's string.
  `leafRow_gJ`       `gJ P O` meets it at every Ql, where the page's field `leaf` is `leafOf bd` and
                     `LeafXAgrees` holds at all bodies.
  `OwnLeafQ bd sb`, `StoredLeafQ bd a sb`   the leaf queries at which the law is used: the body of a
                     symbol of a run's tree, or of a stored table; a typed salt of 32 + sb bytes,
                     for a stored table the digest cfg and then sb bytes.
  `LeafRow.congr`, `LeafRow.mono`   the law hangs on O at the calls' strings alone; it holds at a
                     narrower condition.
  `leaf_own_row`, `leaf_stored_row`   g's answer at such a query, as the format's hash call over O.
  `leafIs_rows`, `leafIsE_rows`       `LeafIs` and `LeafIsE` at g and the hash over O.
  `codeOwes_rows`    **`CodeOwes` at g and the hash over O**, from `LeafRow` and `NodeIs`
                     (OnBytes/Maker/RecNodes.lean).

The other premises of `codeOwes_rows` are those of `codeOwes_gJ`: `BodyIs` at the three stretches,
the stored table's bodies, `TreesFit`, `StoredFitE`, 32 bytes of cfg; and that Ql holds at the
queries
`OwnLeafQ` and `StoredLeafQ`. None names g. `NodeIs` speaks of two digests alone, so it takes no
condition. Without Ql the law on the leaves would ask, wherever a body spells the call of another
oracle, the answer of that oracle's string: a one-to-one coding cannot give that.

The proofs follow those of OnBytes/Maker/Page/LeafAgree.lean and CodeAt.lean.
Not claimed. That any g but `gJ P O` meets `LeafRow`. Nothing on soundness (index binding
included), what a root fixes, opening-form binding, no two openings of a commitment, correctness of
extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.Page.CodeAt

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Maker OnBytes.Flat TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- At a leaf query that meets Ql, and whose body and typed salt spell a call, g answers with the
digest of O at that call's string. -/
def LeafRow (g : Fam (typedOracleFamily 256 K L)) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (Ql : LeafIn L → Prop) : Prop :=
  ∀ (q : LeafIn L) (c : Fmt.OQ), Ql q → leafOf bd q = some c →
    g OracleName.leaf q = bytesToDig (O (strOf c))

/-- The family of a page meets it, at every condition. -/
theorem leafRow_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (hX : ∀ b, LeafXAgrees P b) (Ql : LeafIn L → Prop) :
    LeafRow (gJ P O) O bd Ql :=
  fun q c _ hc => gJ_leaf' P O q c (hP ▸ hc) fun s hs => hX q.body q.salt s c hs (hP ▸ hc)

/-- A leaf query of a run's tree: the body is that of a symbol of a shape sh; the typed salt is a
start of 32 bytes, then sb bytes. The shape is one of data that meet `TreesFit`: so it is unmarked,
and its depth and its place in a label are within that record's bounds. -/
def OwnLeafQ (bd : L.Bd → List Bool) (sb : ℕ) (q : LeafIn L) : Prop :=
  ∃ (sh : Fmt.Shape) (x : Fin (2 ^ sh.a)) (col : Fin sh.W → UInt64) (start s0 : ByteArray)
    (ds : List RDT) (n : ℕ), TreesFit sb ds ∧ treeShT ds n = some sh ∧ start.size = 32 ∧
      s0.size = sb ∧ bd q.body = emb1 sb (some sh) x col ∧
      q.salt = bytesToBits start ++ bytesToBits s0

/-- A leaf query of a stored table of the depth a: the typed salt is the string start, then sb
bytes. -/
def StoredLeafQ (bd : L.Bd → List Bool) (a sb : ℕ) (start : ByteArray) (q : LeafIn L) : Prop :=
  ∃ (y : ℕ × List UInt64) (s0 : ByteArray), TypedOracleCompiler.Run.storedOK a sb y ∧ s0.size = sb ∧
    bd q.body = embStored a sb y ∧ q.salt = bytesToBits start ++ bytesToBits s0

/-- The law hangs on O at the calls' strings alone. -/
theorem LeafRow.congr {g : Fam (typedOracleFamily 256 K L)} {O O' : ByteArray → ByteArray}
    {bd : L.Bd → List Bool} {Ql : LeafIn L → Prop} (h : LeafRow g O bd Ql)
    (e : ∀ c : Fmt.OQ, O (strOf c) = O' (strOf c)) : LeafRow g O' bd Ql :=
  fun q c hq hc => (h q c hq hc).trans (congrArg bytesToDig (e c))

/-- At a narrower condition. -/
theorem LeafRow.mono {g : Fam (typedOracleFamily 256 K L)} {O : ByteArray → ByteArray} {bd : L.Bd → List Bool}
    {Ql Ql' : LeafIn L → Prop} (h : LeafRow g O bd Ql) (e : ∀ q, Ql' q → Ql q) :
    LeafRow g O bd Ql' :=
  fun q c hq hc => h q c (e q hq) hc

section Rows
variable (g : Fam (typedOracleFamily 256 K L)) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
  (Ql : LeafIn L → Prop) (hL : LeafRow g O bd Ql)
include hL

/-- At the body of a symbol of a run's tree. -/
theorem leaf_own_row (sh : Fmt.Shape) (hst : sh.stored = false)
    (hd : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64) (x : Fin (2 ^ sh.a)) (col : Fin sh.W → UInt64)
    (start s0 : ByteArray) (hs : start.size = 32) (sb : ℕ) (es : s0.size = sb) (ds : List RDT)
    (hT : TreesFit sb ds) (n : ℕ) (hn : treeShT ds n = some sh) (b : L.Bd)
    (hb : bd b = emb1 s0.size (some sh) x col) (hQ : ∀ q, OwnLeafQ bd sb q → Ql q) :
    g OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O (Fmt.leafNo sh.stored)
        (Fmt.leafPlace sh.tree (List.ofFn col).length (s0.size / 8)) (2 ^ sh.a + x.val) start
        (Fmt.leafBytes (List.ofFn col) s0)) := by
  have hp := (hT n sh hn).2.2
  rw [← es] at hp
  rw [hL _ _ (hQ _ ⟨sh, x, col, start, s0, ds, n, hT, hn, hs, es, es ▸ hb, rfl⟩) (by
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_own s0.size sh hd hp x col start s0 hs)]
  simp only [Fmt.leafBytes, List.length_ofFn, hst]
  rfl

/-- At the body of a stored table's symbol, at the symbol's own position. -/
theorem leaf_stored_row (a : ℕ) (y : ℕ × List UInt64) (start s0 : ByteArray)
    (hy : TypedOracleCompiler.Run.storedOK a s0.size y) (hs : start.size = 32) (b : L.Bd)
    (hb : bd b = embStored a s0.size y) (hQ : ∀ q, StoredLeafQ bd a s0.size start q → Ql q) :
    g OracleName.leaf ⟨b, bytesToBits start ++ bytesToBits s0⟩ =
      bytesToDig (hO O (Fmt.leafNo true) (Fmt.leafPlace 0 y.2.length (s0.size / 8)) (2 ^ a + y.1)
        start (Fmt.leafBytes y.2 s0)) := by
  rw [hL _ _ (hQ _ ⟨y, s0, hy, rfl, hb, rfl⟩) (by
    show leafCall (bd b) _ = _
    rw [hb]
    exact leafCall_stored a s0.size y hy start s0 hs)]
  rfl

/-- **`LeafIs` at g and the hash over O.** -/
theorem leafIs_rows (sb : ℕ) (C : CK) (ds : List RDT)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (hB : BodyIs bd sb C ds emb)
    (hT : TreesFit sb ds) (hQ : ∀ q, OwnLeafQ bd sb q → Ql q) :
    LeafIs g (Fmt.HO O) sb C ds emb := by
  intro q sh col y start s0 hsh hcol hy hst hs0
  obtain ⟨x, colF, hx, hc, hb⟩ := hB q sh col y hsh hy
  obtain ⟨t1, t2, -⟩ := hT _ sh hsh
  have hb' : bd (emb q y) = emb1 s0.size (some sh) x colF := by rw [hs0]; exact hb
  have key := leaf_own_row g O bd Ql hL sh t1 t2 x colF start s0 hst sb hs0 ds hT _ hsh (emb q y)
    hb' hQ
  rw [hc, hx, hO_eq_HO O _ _ _ _ _ (by rw [t1]; decide)] at key
  exact key

/-- **`LeafIsE` at g and the hash over O.** -/
theorem leafIsE_rows (a sb : ℕ) (cfg : ByteArray) (hcfg : cfg.size = 32) (embE : SgX → Body L)
    (hB : ∀ y, bd (embE y) = embStored a sb y) (W : Three.Whole) (hS : StoredFitE a sb W)
    (hQ : ∀ q, StoredLeafQ bd a sb cfg q → Ql q) : LeafIsE g (Fmt.HO O) cfg embE W := by
  intro d hd t ht x col s0 hx hcol hs0
  obtain ⟨t1, t2, t3, t4, t5⟩ := hS d hd t ht
  have es : s0.size = sb := hs0.trans t4
  have hy : TypedOracleCompiler.Run.storedOK a s0.size (x, col) := by
    rw [es]; exact t5 x col (t3 ▸ hx) hcol
  have hb' : bd (embE (x, col)) = embStored a s0.size (x, col) := by rw [es]; exact hB _
  have key := leaf_stored_row g O bd Ql hL a (x, col) cfg s0 hy hcfg (embE (x, col)) hb'
    (es ▸ hQ)
  rw [hO_eq_HO O _ _ _ _ _ (by decide)] at key
  unfold leafHash
  rw [t1, t2, t3]
  exact key

end Rows

section File
variable (C : CK) (a : ℕ) (W : Three.Whole) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (embS : (p : OPos (chainsOf C (WholeD.of a W) tF tJ t3).sh) →
    OSym (chainsOf C (WholeD.of a W) tF tJ t3).sh p → Body L) (embE : SgX → Body L)

/-- **`CodeOwes` at g and the hash over O.** -/
theorem codeOwes_rows (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray)
    (bd : L.Bd → List Bool) (Ql : LeafIn L → Prop) (hL : LeafRow g O bd Ql) (sb : ℕ)
    (cfg : ByteArray) (hQo : ∀ q, OwnLeafQ bd sb q → Ql q)
    (hQs : ∀ q, StoredLeafQ bd a sb cfg q → Ql q)
    (hN : NodeIs g (Fmt.HO O) cfg) (hcfg : cfg.size = 32)
    (b₁ : BodyIs bd sb C (WholeD.of a W).ds₁ fun p => symb₁ embS (.inr p))
    (b₂ : BodyIs bd sb C (WholeD.of a W).ds₂ fun p => symb₂ embS (.inr p))
    (b₃ : BodyIs bd sb C (WholeD.of a W).ds₃ fun p => symb₃ embS (.inr p))
    (bE : ∀ y, bd (embE y) = embStored a sb y) (f₁ : TreesFit sb (WholeD.of a W).ds₁)
    (f₂ : TreesFit sb (WholeD.of a W).ds₂) (f₃ : TreesFit sb (WholeD.of a W).ds₃)
    (fE : StoredFitE a sb W) : CodeOwes C K a W tF tJ t3 g (Fmt.HO O) embS embE cfg sb where
  node := hN
  leaf₁ := leafIs_rows g O bd Ql hL sb C _ _ b₁ f₁ hQo
  leaf₂ := leafIs_rows g O bd Ql hL sb C _ _ b₂ f₂ hQo
  leaf₃ := leafIs_rows g O bd Ql hL sb C _ _ b₃ f₃ hQo
  leafE := leafIsE_rows g O bd Ql hL a sb cfg hcfg embE bE W fE hQs

end File

end OnBytes.Maker.Page
