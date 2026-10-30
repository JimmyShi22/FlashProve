-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryPagePaid.lean: the two fields on the page of the entry's large tie are paid
at the entry's page: the law `SeedsPage` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean) holds of `pageForE`
(OnBytes/TypedOracleCompiler/Slice/EntryFill.lean) at both keys' names, each under its key's root as a digest.

Main theorems.
 `pageForE_seeds`       at one key's name, under that key's root. By `RowsE.seedsPageE_key`
                        (OnBytes/TypedOracleCompiler/Run/RowsE.lean).
 `pageForE_seeds_two`   BOTH FIELDS (`EntryTieLaws.page₀`, `page₁`,
                        a file of this project that is not in this library).

Asked: each key's root has 32 bytes; THE TWO KEYS HAVE ONE SHAPE AND ONE CONFIGURATION DIGEST; the
page's fixed bytes behind a root are those of that shape and digest, fewer than 2 ^ 32; the
description's number of blocks and one more are fewer than 2 ^ 48.

Not claimed. That any two keys have one shape and one digest; that the page's fixed bytes are these:
hypotheses. The page's other arguments (configuration digest, parameter digest, the bits of a file's
salt, the code for strings that spell nothing) are letters. No other field of the tie. NOTHING ON
SOUNDNESS IS SHOWN. What the heads of EntryFill.lean, RowsE.lean and SeedsBridge.lean do not claim.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Run.RowsE
import Run.ParserHashProofs

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open TypedOracleCompiler.Slice.EntryFill (Ls pageForE pinsE)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest : ByteArray) (n : ℕ) (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)))

/-- THE LAW ON A PAGE AT THE SEEDS' TAG HOLDS AT THE ENTRY'S PAGE, AT A KEY'S NAME AND UNDER THE
KEY'S ROOT AS A DIGEST. Asked: the key's root has 32 bytes; the page's fixed bytes behind a root
are those of the key's shape and configuration digest, fewer than 2 ^ 32; fewer than 2 ^ 48 blocks.
-/
theorem pageForE_seeds (hK : D.K + 1 < 2 ^ 48) (k : OnBytes.Tie.IdKey)
    (h32 : k.2.2.root.size = 32)
    (hrest : rest = FirstName.restOf k.2.1 k.1.code.logN k.1.code.ell k.1.code.r k.1.v
      k.1.answers k.1.saltBytes) (hr : rest.size < 2 ^ 32) :
    SeedsPage (pageForE D d₁ cfg hcfg pd rest n back) .test
      (OnBytes.Key.nameOf k.1 k.2.1 k.2.2)
      (q0S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id [_root_.Run.bytesToDig k.2.2.root])
      (q1S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id) :=
  RowsE.seedsPageE_key (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1) _ back hK
    (_root_.Run.bytesToDig k.2.2.root) k (_root_.Run.digToBytes_bytesToDig _ h32).symm hrest hr

/-- BOTH FIELDS ON THE PAGE OF THE ENTRY'S LARGE TIE (`EntryTieLaws.page₀`, `page₁`,
a file of this project that is not in this library), at the entry's page. ONE string of fixed bytes
serves both names:
the two keys have one shape and one configuration digest. -/
theorem pageForE_seeds_two (hK : D.K + 1 < 2 ^ 48) (k₀ k₁ : OnBytes.Tie.IdKey)
    (h₀ : k₀.2.2.root.size = 32) (h₁ : k₁.2.2.root.size = 32) (hsh : k₁.1 = k₀.1)
    (hcf : k₁.2.1 = k₀.2.1)
    (hrest : rest = FirstName.restOf k₀.2.1 k₀.1.code.logN k₀.1.code.ell k₀.1.code.r k₀.1.v
      k₀.1.answers k₀.1.saltBytes) (hr : rest.size < 2 ^ 32) :
    SeedsPage (pageForE D d₁ cfg hcfg pd rest n back) .test
        (OnBytes.Key.nameOf k₀.1 k₀.2.1 k₀.2.2)
        (q0S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id [_root_.Run.bytesToDig k₀.2.2.root])
        (q1S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id) ∧
      SeedsPage (pageForE D d₁ cfg hcfg pd rest n back) .test
        (OnBytes.Key.nameOf k₁.1 k₁.2.1 k₁.2.2)
        (q0S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id [_root_.Run.bytesToDig k₁.2.2.root])
        (q1S (L := Ls D d₁) .test D.C (seedEntry lg s) _ id) :=
  ⟨pageForE_seeds D d₁ cfg hcfg pd rest n back hK k₀ h₀ hrest hr,
    pageForE_seeds D d₁ cfg hcfg pd rest n back hK k₁ h₁ (by rw [hsh, hcf]; exact hrest) hr⟩

end TypedOracleCompiler.Slice
