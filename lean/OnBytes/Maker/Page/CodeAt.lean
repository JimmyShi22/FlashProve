-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CodeAt.lean: what the walks of a file's forests owe of the oracle functions
(`CodeOwes`, OnBytes/Maker/WalksOf.lean) holds of the functions `gJ P O` that a page and a function
O on the format's strings induce (OnBytes/Maker/Page/Frame.lean).

OnBytes/Maker/Page/Trees.lean, LeafAgree.lean and Request.lean say what `gJ P O` answers at a vertex
and at a leaf's body. OnBytes/Maker/Page/BodiesAt.lean says which string the body of a symbol of a
stretch is. Here these are laid over the five fields of `CodeOwes`, at the hash `Fmt.HO O`.

  `TreesFit sb ds`    a test's content on a stretch's data: no tree is marked as stored; none is
                      deeper than 63; the first word of a leaf's label is below 2^64.
  `leafIs_gJ`         **`LeafIs` at `gJ P O`**, for a stretch.
  `LeafXAgrees P b`   at leaf queries on the body b the spelling `leafX`, which the page takes from
                      elsewhere, writes nothing, or the string of the page's own call.
  `StoredFitE a sb W`   on the stored tables of the data's rounds: marked as stored, tree number 0,
                      depth a, salts of sb bytes; and the bounds of `storedOK` at the table's width.
  `leafIsE_gJ`        **`LeafIsE` at `gJ P O`.**
  `codeOwes_gJ`       **`CodeOwes` at `gJ P O` and `Fmt.HO O`.**

The premises of the last. On the page: its digest is cfg; its field `leaf` is `leafOf bd`;
`LeafXAgrees` at the bodies of the file's own symbols. On the bodies: `BodyIs` at the three
stretches; the body of a stored symbol is
`embStored`. On the data: `TreesFit` three times, `StoredFitE`. cfg has 32 bytes. No premise on O.
None of these is shown here.

Not claimed. `gJ P O` is a function of the typed query, no one-to-one coding (the head of
OnBytes/Maker/Page/Frame.lean). Nothing on soundness.


-/
import OnBytes.Maker.Page.Request
import OnBytes.Maker.Page.LeafAgree
import OnBytes.Maker.Page.BodiesAt
import OnBytes.Maker.WalksOf

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Maker OnBytes.Flat TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- On a stretch's data. -/
def TreesFit (sb : ℕ) (ds : List RDT) : Prop :=
  ∀ n sh, treeShT ds n = some sh → sh.stored = false ∧ 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64 ∧
    164 + 65536 * Fmt.leafPlace sh.tree sh.W (sb / 8) < 2 ^ 64

/-- At leaf queries on the body b the spelling `leafX`, which the page takes from elsewhere, writes
nothing, or the string of the page's own call. -/
def LeafXAgrees (P : PageJ L K) (b : L.Bd) : Prop :=
  ∀ salt s c, P.leafX ⟨b, salt⟩ = some s → P.leaf ⟨b, salt⟩ = some c → bitsToBytes s = strOf c

/-- **`LeafIs` at `gJ P O`.** -/
theorem leafIs_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (sb : ℕ) (C : CK) (ds : List RDT)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (hB : BodyIs bd sb C ds emb)
    (hT : TreesFit sb ds) (hX : ∀ q y, LeafXAgrees P (emb q y)) :
    LeafIs (gJ P O) (Fmt.HO O) sb C ds emb := by
  intro q sh col y start s0 hsh hcol hy hst hs0
  obtain ⟨x, colF, hx, hc, hb⟩ := hB q sh col y hsh hy
  obtain ⟨t1, t2, t3⟩ := hT _ sh hsh
  have t3' : 164 + 65536 * Fmt.leafPlace sh.tree sh.W (s0.size / 8) < 2 ^ 64 := by
    rw [hs0]; exact t3
  have hb' : bd (emb q y) = emb1 s0.size (some sh) x colF := by rw [hs0]; exact hb
  have key := leafIs_own_gJ' P O bd hP sh t1 t2 x colF start s0 hst t3' (emb q y) hb'
    fun s hs => hX q y _ s ⟨0, 164, Fmt.leafPlace sh.tree sh.W (s0.size / 8), 2 ^ sh.a + x.val,
        start, Fmt.colBytes (List.ofFn colF) ++ Fmt.zeroBytes (Fmt.fillLen sh.W s0.size) ++ s0⟩
      hs (by
      rw [hP]
      show leafCall (bd (emb q y)) _ = _
      rw [hb']
      exact leafCall_own s0.size sh t2 t3' x colF start s0 hst)
  rw [hc, hx, hO_eq_HO O _ _ _ _ _ (by rw [t1]; decide)] at key
  exact key

/-- On the stored tables of the data's rounds. -/
def StoredFitE (a sb : ℕ) (W : Three.Whole) : Prop :=
  ∀ d ∈ W.ds₁ ++ (W.ds₂ ++ W.ds₃), ∀ t ∈ d.stored, t.sh.stored = true ∧ t.sh.tree = 0 ∧ t.sh.a = a ∧
    t.salt = sb ∧ ∀ x col, x < 2 ^ a → col.length = t.sh.W →
      TypedOracleCompiler.Run.storedOK a sb (x, col)

/-- **`LeafIsE` at `gJ P O`.** -/
theorem leafIsE_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (a sb : ℕ) (cfg : ByteArray) (hcfg : cfg.size = 32)
    (embE : SgX → Body L) (hB : ∀ y, bd (embE y) = embStored a sb y) (W : Three.Whole)
    (hS : StoredFitE a sb W) (hX : ∀ y, LeafXAgrees P (embE y)) :
    LeafIsE (gJ P O) (Fmt.HO O) cfg embE W := by
  intro d hd t ht x col s0 hx hcol hs0
  obtain ⟨t1, t2, t3, t4, t5⟩ := hS d hd t ht
  have es : s0.size = sb := hs0.trans t4
  have hy : TypedOracleCompiler.Run.storedOK a s0.size (x, col) := by
    rw [es]; exact t5 x col (t3 ▸ hx) hcol
  have hb' : bd (embE (x, col)) = embStored a s0.size (x, col) := by rw [es]; exact hB _
  have key := leafIs_stored_gJ' P O bd hP a (x, col) cfg s0 hy hcfg (embE (x, col)) hb'
    fun s hs => hX _ _ s ⟨0, 174, Fmt.leafPlace 0 col.length (s0.size / 8), 2 ^ a + x, cfg,
        Fmt.colBytes col ++ Fmt.zeroBytes (Fmt.fillLen col.length s0.size) ++ s0⟩ hs (by
      rw [hP]
      show leafCall (bd (embE (x, col))) _ = _
      rw [hb']
      exact leafCall_stored a s0.size (x, col) hy cfg s0 hcfg)
  rw [hO_eq_HO O _ _ _ _ _ (by decide)] at key
  unfold leafHash
  rw [t1, t2, t3]
  exact key

section File
variable (C : CK) (a : ℕ) (W : Three.Whole) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (embS : (p : OPos (chainsOf C (WholeD.of a W) tF tJ t3).sh) →
    OSym (chainsOf C (WholeD.of a W) tF tJ t3).sh p → Body L) (embE : SgX → Body L)

/-- **`CodeOwes` at `gJ P O` and the hash over O.** -/
theorem codeOwes_gJ (P : PageJ L (K + 1)) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool)
    (hP : P.leaf = leafOf bd) (sb : ℕ) (cfg : ByteArray) (hc : P.cfg = cfg) (hcfg : cfg.size = 32)
    (b₁ : BodyIs bd sb C (WholeD.of a W).ds₁ fun p => symb₁ embS (.inr p))
    (b₂ : BodyIs bd sb C (WholeD.of a W).ds₂ fun p => symb₂ embS (.inr p))
    (b₃ : BodyIs bd sb C (WholeD.of a W).ds₃ fun p => symb₃ embS (.inr p))
    (bE : ∀ y, bd (embE y) = embStored a sb y) (f₁ : TreesFit sb (WholeD.of a W).ds₁)
    (f₂ : TreesFit sb (WholeD.of a W).ds₂) (f₃ : TreesFit sb (WholeD.of a W).ds₃)
    (fE : StoredFitE a sb W) (hX₁ : ∀ q y, LeafXAgrees P (symb₁ embS (.inr q) y))
    (hX₂ : ∀ q y, LeafXAgrees P (symb₂ embS (.inr q) y))
    (hX₃ : ∀ q y, LeafXAgrees P (symb₃ embS (.inr q) y)) (hXE : ∀ y, LeafXAgrees P (embE y)) :
    CodeOwes C K a W tF tJ t3 (gJ P O) (Fmt.HO O) embS embE cfg sb where
  node := hc ▸ nodeIs_HO P O
  leaf₁ := leafIs_gJ P O bd hP sb C _ _ b₁ f₁ hX₁
  leaf₂ := leafIs_gJ P O bd hP sb C _ _ b₂ f₂ hX₂
  leaf₃ := leafIs_gJ P O bd hP sb C _ _ b₃ f₃ hX₃
  leafE := leafIsE_gJ P O bd hP a sb cfg hcfg embE bE W fE hXE

end File

end OnBytes.Maker.Page
