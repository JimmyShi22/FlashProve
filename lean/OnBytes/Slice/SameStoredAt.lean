-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SameStoredAt.lean: the encodings of two descriptions spell stored leaves and vertices
alike, if the descriptions have one configuration digest, one salt length and one depth of stored
trees.

OnBytes/Slice/SameStored.lean shows that two implementations of typed oracles by one oracle on bit
strings read the same stored symbols off one log, if they meet `OneBlock` and `SameStored`. This
file shows both of the encoding `Tie.theImplX` (OnBytes/Tie/PageX.lean) at two sets of data that
agree in four things, and so of `Tie.theImplX (Tie.pageX ..)` (OnBytes/Tie/PageXFit.lean) at two
descriptions D₁ and D₂, with any two decisions (dec), numbers of blocks of a chain's answer (K) and
readers for the statement (V).

Why it holds. A leaf query on a stored table's symbol is written by the code of the format's call
number 174, which reads the configuration digest, the salt's length and the depth alone, or it
stands behind the byte 2 in the library's total code, whose string of such a query is made of fixed
marks, the symbol's serial form and the salt. A vertex query on two digests is written by the code
of the call number 166, which reads the configuration digest alone.

Main theorems.
 `oneBlock_implX`    in the encoding a leaf's and a vertex's answer is one block, taken as it is.
 `code_stored`       the string of a leaf query on a stored table's symbol, in both cases.
 `sameStored_implX`  `SameStored` for the encodings at two sets of data with one configuration
                     digest, one length of salt, codes of stored symbols that write alike, and total
                     codes that write stored leaves alike.
 `sameStored_pageX`  `SameStored` for the encodings of D₁ and D₂, the symbols matched as they are.
 `extLeaf_same_pageX`  so, off a log in which no two strings have one answer, both encodings read
                     one stored symbol at every leaf under every digest.

The depth is `D.a`: the depth of the description's first stored tree, 0 if it has none; within the
library's limits (`Run.PQ.XD.ok`) all stored trees of a description have it.

A description that opens no stored table has the depth 0: against one with a greater depth the
hypothesis fails. By a reading of the code's text (the position's word is 2^a + x), and by no
theorem here, the two encodings then write stored leaves differently.

What is not claimed. That two descriptions of two files have one configuration digest, salt length
and depth: these are hypotheses. Both encodings in `sameStored_pageX` are `Tie.pageX`'s, made for
the protocol under the tag `link`: of an encoding for a key's or a proof's interface nothing is
said. One that is built otherwise than `Tie.theImplX`, or with a further partial code that writes a
leaf query on a stored symbol, does not come under `sameStored_implX`. Nothing on any protocol,
language, checker or hash function; no probability.

-/
import OnBytes.Slice.SameStored
import OnBytes.Tie.PageXFit

set_option autoImplicit false

namespace OnBytes.Slice
open Rom Iop Compile Compile.Batch Run Run.PQ
open OnBytes.Tie (PageCX theImplX pageX pStoredLeaf pLeaf2 pAllX pAllX_no2 StmInv theImplX_stored
  theImplX_node)

section
variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageCX L K tg)

/-- In the encoding a leaf's and a vertex's answer is one block, taken as it is. -/
theorem oneBlock_implX : OneBlock (theImplX C) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- **The string of a leaf query on a stored table's symbol**: what the code of the call number 174
writes, where it writes; elsewhere the byte 2 and the total code's string. -/
theorem code_stored (x : L.Symbol) (salt : Bits) (j : Fin 1) :
    (theImplX C).code Batch.OracleName.leaf ⟨some (.inl x), salt⟩ j =
      ((pStoredLeaf C).put ⟨some (.inl x), salt⟩).getD
        (bitsOfByte 2 ++ C.back.put (.inl (.inl ⟨some (.inl x), salt⟩))) := by
  cases h : (pStoredLeaf C).put ⟨some (.inl x), salt⟩ with
  | some s => exact theImplX_stored C _ s h j
  | none =>
    have h2 : (pLeaf2 C).put ⟨some (.inl x), salt⟩ = none := h
    exact PCode.orElse_put_none (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C)
      (a := .inl (.inl ⟨some (.inl x), salt⟩)) h2

end

/-- The code of the call number 166 writes every pair of strings of 256 bits, from the start
alone. -/
theorem pNode_put (start : ByteArray) (x y : Bits) (h1 : x.length = 256) (h2 : y.length = 256) :
    (pNode start).put (x, y) = some (hdr 0 166 0 0 start ++ (x ++ y)) :=
  if_pos ⟨h1, h2⟩

/-- **The encodings at two sets of data spell stored leaves and vertices alike**, if the data have
one configuration digest and one length of salt, their codes of stored symbols write alike (through
u), and their total codes write leaf queries on stored symbols alike. Of vertices nothing more is
asked: the code of the call number 166 writes every pair of digests, from the configuration digest
alone. That any data other than `Tie.pageX`'s meet the hypotheses is not shown. -/
theorem sameStored_implX {I₁ X₁ I₂ X₂ : Type} {L₁ : BatchProtocol I₁ X₁} {L₂ : BatchProtocol I₂ X₂} {K₁ K₂ : ℕ}
    {t₁ t₂ : Tag} (C₁ : PageCX L₁ K₁ t₁) (C₂ : PageCX L₂ K₂ t₂) (u : L₁.Symbol ≃ L₂.Symbol)
    (hc : C₁.cfg = C₂.cfg) (hs : C₁.saltBits = C₂.saltBits)
    (hp : ∀ x, C₁.storedP.put x = C₂.storedP.put (u x))
    (hb : ∀ x salt, C₁.back.put (.inl (.inl ⟨some (.inl x), salt⟩)) =
      C₂.back.put (.inl (.inl ⟨some (.inl (u x)), salt⟩))) :
    SameStored (theImplX C₁) (theImplX C₂) u where
  node := fun a b j₁ j₂ => by
    have la : (List.ofFn a).length = 256 := List.length_ofFn
    have lb : (List.ofFn b).length = 256 := List.length_ofFn
    have hw := fun cfg : ByteArray => pNode_put cfg (List.ofFn a) (List.ofFn b) la lb
    rw [theImplX_node C₁ _ _ (hw _) j₁, theImplX_node C₂ _ _ (hw _) j₂, hc]
  stored := fun x salt j₁ j₂ => by
    rw [code_stored, code_stored, hb]
    congr 1
    show (if Tie.startIs (L := L₁) C₁.cfg ⟨some (.inl x), salt⟩ = true then
        (if salt.length = 256 + C₁.saltBits then (C₁.storedP.put x).map
          (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) else none) else none) =
      (if Tie.startIs (L := L₂) C₂.cfg ⟨some (.inl (u x)), salt⟩ = true then
        (if salt.length = 256 + C₂.saltBits then (C₂.storedP.put (u x)).map
          (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) else none) else none)
    rw [hc, hs, hp]
    rfl

variable (D₁ D₂ : XD) (dec₁ dec₂ : View → Bool) (K₁ K₂ : ℕ) (hcfg₁ : D₁.base.cfg.size = 32)
  (hcfg₂ : D₂.base.cfg.size = 32) (V₁ : StmInv D₁) (V₂ : StmInv D₂)

/-- **The encodings of two descriptions with one configuration digest, one salt length and one depth
of stored trees spell stored leaves and vertices alike.** Decisions, numbers of blocks, statements
and all else in the descriptions may differ. -/
theorem sameStored_pageX (hc : D₁.base.cfg = D₂.base.cfg)
    (hs : D₁.base.plan.salt = D₂.base.plan.salt) (ha : D₁.a = D₂.a) :
    SameStored (theImplX (pageX dec₁ K₁ hcfg₁ V₁)) (theImplX (pageX dec₂ K₂ hcfg₂ V₂))
      (Equiv.refl SgX) :=
  sameStored_implX (pageX dec₁ K₁ hcfg₁ V₁) (pageX dec₂ K₂ hcfg₂ V₂) (Equiv.refl SgX) hc
    (by show 8 * D₁.base.plan.salt = 8 * D₂.base.plan.salt; rw [hs])
    (fun x => by
      show (Tie.pStored D₁.a D₁.base.plan.salt).put x = (Tie.pStored D₂.a D₂.base.plan.salt).put x
      rw [ha, hs])
    (fun _ _ => rfl)

/-- **Both encodings read one stored symbol.** Off a log in which no two strings have one answer,
the stored table's symbol at leaf j of the tree of depth d under the digest cm is the same through
the encodings of D₁ and D₂; where the one finds none, so does the other. Asked of the descriptions:
one configuration digest, one salt length, one depth of stored trees. No probability. -/
theorem extLeaf_same_pageX (hc : D₁.base.cfg = D₂.base.cfg)
    (hs : D₁.base.plan.salt = D₂.base.plan.salt) (ha : D₁.a = D₂.a) (σ : Trace (rom 256))
    (hσ : NoClash σ) (d j : ℕ) (cm : Dig 256) :
    (Batch.extLeaf (singleTr (theImplX (pageX dec₁ K₁ hcfg₁ V₁)) σ) d cm j).bind storedSym =
      (Batch.extLeaf (singleTr (theImplX (pageX dec₂ K₂ hcfg₂ V₂)) σ) d cm j).bind storedSym := by
  have h := extLeaf_same (oneBlock_implX _) (oneBlock_implX _)
    (sameStored_pageX D₁ D₂ dec₁ dec₂ K₁ K₂ hcfg₁ hcfg₂ V₁ V₂ hc hs ha) σ hσ d j cm
  rw [← h]
  refine congrArg _ (funext fun q => ?_)
  exact Option.map_id'.symm

end OnBytes.Slice
