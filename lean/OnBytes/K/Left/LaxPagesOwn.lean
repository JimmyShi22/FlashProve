-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxPagesOwn.lean: the leaves of the chain's own trees at an entry's page: what
`assembleS_walks` and `ownOkE_of_read` (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean) ask of the bodies and of
the family.

`assembleS_walks` asks that the bodies of the chain's own symbols be one way `e1` for a tree's form,
a place and a column, lifted over the rounds' lists of trees (its `hemb`). `ownOkE_of_read` asks
that the family's answer at the typed leaf `⟨e1 sh x sym, leafSalt run salt⟩` be the format's own
leaf call (its `hleaf`). Here e1 is `ownEnc sB`: the bits of the label under 164 (the word with the
tree's number, the width and the salt's words; 2 ^ depth + place) and of the column with its fill.

Main names:
  `ownEnc sB`: the way.
  `spell_lift`: the format's spelling of a leaf in a list of rounds is `ownEnc sB`, lifted.
  `own_emb`: so the bodies of `ownES D hok` (OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean) are: `hemb`.
  `own_leaf`: `hleaf`, at the family that is read out of any one oracle g through the page
    `EntryFill.pageForE`, and the hash `hOfG g` made of the same oracle. By `RowsE3.ownE_law`
    (OnBytes/TypedOracleCompiler/Run/RowsE3.lean).
  `own_bounds`: at a description that passes the `ok` of OnBytes/TypedOracleCompiler, every tree of every round
    meets `own_leaf`'s two bounds.

The premises of `own_leaf`: the form is of no stored tree; its label's first word is below 2 ^ 48;
2 ^ depth + 2 ^ depth ≤ 2 ^ 64; the run value has 32 bytes; the page is made for a file's salt of sB
bytes.

Limits: values alone; nothing on soundness. That a round's trees are no stored trees, and that a
reader's run value has 32 bytes, is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.RowsE3
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Slice.PartChainStr

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Strings TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.RowsE TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig leafSalt)

/-- The body of a leaf of an own tree: the form, the place, the column. sB: the bytes of a file's
salt. -/
def ownEnc (sB : ℕ) : Enc1 (List Bool) := fun sh x sym =>
  spell2 164 (_root_.Fmt.leafPlace sh.tree sh.W (sB / 8), 2 ^ sh.a + x.val,
    _root_.Fmt.colBytes (List.ofFn sym) ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen sh.W sB))

/-- In a round's list of trees. -/
theorem spell_liftT (sB : ℕ) : ∀ (ts : List _root_.Fmt.Shape) (p : PQ.PosT ts) (a : PQ.SymT ts p),
    spell2 164 (PQ.leafT sB ts p a) = liftT (ownEnc sB) ts p a
  | _ :: _, .inl _, _ => rfl
  | _ :: ts, .inr p, a => spell_liftT sB ts p a

/-- The format's spelling of a leaf in a list of rounds is `ownEnc sB`, lifted. -/
theorem spell_lift (C : PQ.CK) (sB : ℕ) : ∀ (ds : List PQ.RD) (p : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) p),
    spell2 164 (PQ.leafSL C sB ds ⟨p, a⟩) = embLS C (liftT (ownEnc sB)) ds p a
  | [], p, _ => p.elim
  | d :: _, .inl p, a => spell_liftT sB d.trees p a
  | _ :: ds, .inr q, a => spell_lift C sB ds q a

/-- The bodies of the chain's own symbols are `ownEnc`, lifted. -/
theorem own_emb (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (q : OPos (PQ.uL D.C D.ds)) (a : OSym (PQ.uL D.C D.ds) q) :
    (ownES D hok).emb (.inr q) a = embLS D.C (liftT (ownEnc D.base.plan.salt)) D.ds q a := by
  have h := ok2_rd2_embTail D.base.plan.salt D.C (PQ.salt_of D.base hok) D.ds
    (smallL_of_ok D.base hok) q a
  have e := ((ok2_iff _).1 h.1).2.2
  rw [h.2] at e
  rw [← spell_lift]
  exact e

section
variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256)
  (rest : ByteArray) (sB : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (EntryFill.Ls D d₁))) (g : Fam (rom 256))

/-- The family's answer at a typed leaf of an own tree is the format's own leaf call. -/
theorem own_leaf (sh : _root_.Fmt.Shape) (h1 : sh.stored = false)
    (hp : _root_.Fmt.leafPlace sh.tree sh.W (sB / 8) < 2 ^ 48) (ha : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64)
    (run : ByteArray) (hrun : run.size = 32) (x : Fin (2 ^ sh.a)) (sym : Fin sh.W → UInt64)
    (salt : ByteArray) (hs : salt.size = sB) :
    (readBlocks (EntryFill.pageForE D d₁ cfg hcfg pd rest (8 * sB) back) g
        TypedOracleCompiler.Compile.Batch.OracleName.leaf ⟨ownEnc sB sh x sym, leafSalt run salt⟩ : Dig 256) =
      bytesToDig (leafAtH (hOfG g) sh run x.val (List.ofFn sym) salt) := by
  have hl : (List.ofFn sym).length = sh.W := List.length_ofFn
  have h := RowsE3.ownE_law (EntryFill.pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1) (8 * sB) back
    g sB rfl sh h1 x.val (List.ofFn sym) (ownEnc sB sh x sym) (by unfold ownEnc; rw [hl])
    (by rw [hl]; exact hp) (by have := x.isLt; omega) run salt hrun hs
  exact h

end

/-- At a description within the limits, every tree of every round meets `own_leaf`'s two bounds. -/
theorem own_bounds (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (d : PQ.RD) (hd : d ∈ D.ds)
    (sh : _root_.Fmt.Shape) (hs : sh ∈ d.trees) :
    _root_.Fmt.leafPlace sh.tree sh.W (D.base.plan.salt / 8) < 2 ^ 48 ∧
      2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64 := by
  obtain ⟨h1, h2, h3⟩ := smallL_of_ok D.base hok d hd sh hs
  have h8 := PQ.salt_of D.base hok
  refine ⟨?_, h3⟩
  unfold _root_.Fmt.leafPlace
  omega

end OnBytes.K.Left
