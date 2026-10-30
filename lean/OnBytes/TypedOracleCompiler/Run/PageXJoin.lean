-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageXJoin.lean: what a join of parts leans on in the encoding of typed queries, said
over the sibling's widened page (OnBytes/TypedOracleCompiler/Run/CodingPage.lean: one code of leaves' bodies, tags
164 or 174, a test on body and salt together).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/PageX.lean (the small laws, `theImplX_spare`, `theImplX_other`),
OnBytes/Slice/SameRead.lean (`OneBlock`), OnBytes/Slice/SameStored.lean (`SameStored`),
OnBytes/Slice/SameStoredAt.lean (`oneBlock_implX`, `code_stored`, `pNode_put`, `sameStored_implX`),
OnBytes/Tie/Page174.lean (`startIs`) and OnBytes/Slice/WalkOff.lean (`t169`, `IsCall169`, the core
of `look_call169`).

AS TEXT BUT FOR NAMES (theImplX to theImpl, totalX to total).
`theImpl_leaf1`, `theImpl_node1`, `theImpl_rngLeaf`, `theImpl_rngNode`, `theImpl_fbK`,
`theImpl_spare`, `OneBlock`, `oneBlock_impl`, `startIs`, `pNode_put256` (there `pNode_put`), `t169`,
`t169_differs`, `IsCall169`.
TURNED.
 `theImpl_other5`     `theImpl_other` with its five hypotheses on the tag as one, `¬ Tag5 s`.
 `theImpl_code_leaf`          `code_stored`, for EVERY leaf query: there is one code of leaves.
 `SameStored m₁ m₂ e₁ e₂`   with one type Sg of stored symbols and two embeddings into the two
                      interfaces' bodies, where the original has an equivalence of the two
                      interfaces' symbols.
 `sameStored_impl`    `sameStored_implX`; its hypothesis on the two codes of stored symbols is
                      `StoredIn` of both pages at ONE code p.
 `code_call169`, `inv_call169`   the core of `look_call169`, without the look: the string of a call
                      with the number 169 is a point of the spare oracle, written as itself.
NEW.
 `StoredIn C p e`     what a page with one code of bodies must give at the stored symbols: on a body
                      `e y` its code writes WHAT p WRITES, AND NOTHING WHERE p WRITES NOTHING (an
                      equation of options, not an implication); and its test on body and salt is
                      `startIs` at the page's own configuration digest, for every salt.
 `pLeafC_stored`      under `StoredIn`: what the page writes on a stored symbol, to the sign of
                      `Tie.pLeafS`.

WHAT IS NOT SAID. That any page meets `StoredIn`: not here (`storedIn_pageXPd`,
OnBytes/TypedOracleCompiler/Run/PageXFit.lean). The fourth hypothesis of `sameStored_impl` (`hb`: the two total
codes `back` write leaf queries on stored symbols alike) is a hypothesis here: where the format does
not write (a wrong start, a wrong length of salt, a symbol that p does not write) the string is the
byte 2 and `back`'s string, and the reading of a log keeps such strings; it is met by two pages
whose serialiser of bodies is `serTie` (`backP_stored_two`, OnBytes/TypedOracleCompiler/Run/SerTie.lean). Nothing
over a log here: the look, the walk and the raw string over the sibling are in OnBytes/TypedOracleCompiler/Slice/
(SameRead.lean, ByWalks.lean, LooksAgree.lean, which uses `StoredGet`). No comparison with
`Tie.theImplX` of OnBytes/ here: OnBytes/TypedOracleCompiler/Slice/TieEscape.lean. Nothing on soundness; no
probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXAgree

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-! ## The small laws of the encoding -/

section
variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : PageC L K tg)

/-- A leaf's answer is one block. -/
theorem theImpl_leaf1 : (theImpl C).blocks .leaf = 1 := rfl

/-- A vertex's answer is one block. -/
theorem theImpl_node1 : (theImpl C).blocks .node = 1 := rfl

/-- A leaf's answer is its one block, unchanged. -/
theorem theImpl_rngLeaf (f : Fin 1 → Fin 256 → Bool) : ((theImpl C).rng .leaf).symm f = f 0 := rfl

/-- A vertex's answer is its one block, unchanged. -/
theorem theImpl_rngNode (f : Fin 1 → Fin 256 → Bool) : ((theImpl C).rng .node).symm f = f 0 := rfl

/-- A chain query's answer has K + 1 blocks. -/
theorem theImpl_fbK (t : Tag) : (theImpl C).blocks (.fb t) = K + 1 := rfl

/-- A string that the total code does not write, and that does not begin with the byte 3, is a
point of the spare oracle, written as itself. Among them: a string with one of the five tags that
the partial codes do not write, if it does not begin with the byte 2. -/
theorem theImpl_spare (s : List Bool) (j : Fin 1) (hp : (total C).parse s = none)
    (h3 : ¬ bitsOfByte 3 <+: s) : (theImpl C).code .other s j = s := by
  refine codeA_other 256 K L (total C) (bitsOfByte 3) esc_ne (total_esc C) s j
    (freeE_of 256 K L (total C) (bitsOfByte 3) esc_ne s hp ?_)
  cases hs : StrCode.strip (bitsOfByte 3) s with
  | none => rfl
  | some t => exact absurd ⟨t, (StrCode.strip_some hs).symm⟩ h3

/-- A string with none of the five tags, and with neither escape in front, is a point of the spare
oracle, written as itself. `theImpl_other` with its five hypotheses on the tag as one. -/
theorem theImpl_other5 (s : List Bool) (j : Fin 1) (ht : ¬ Tag5 s)
    (h2 : ¬ bitsOfByte 2 <+: s) (h3 : ¬ bitsOfByte 3 <+: s) :
    (theImpl C).code .other s j = s :=
  theImpl_other C s j (fun h => ht (Or.inl h)) (fun h => ht (Or.inr (Or.inl h)))
    (fun h => ht (Or.inr (Or.inr (Or.inl h)))) (fun h => ht (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (fun h => ht (Or.inr (Or.inr (Or.inr (Or.inr h))))) h2 h3

end

/-! ## One block -/

section
variable {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- In m a leaf's and a vertex's answer is one block, and the typed answer is that block as it
is. -/
structure OneBlock (m : OracleCoding (typedOracleFamily lam K L) lam) : Prop where
  /-- a leaf's answer is one block -/
  leaf1 : m.blocks OracleName.leaf = 1
  /-- a vertex's answer is one block -/
  node1 : m.blocks OracleName.node = 1
  /-- a leaf's answer is the oracle's answer, as it is -/
  rngLeaf : ∀ r : Fin lam → Bool, ((m.rng OracleName.leaf).symm (fun _ => r) : Dig lam) = r
  /-- a vertex's answer is the oracle's answer, as it is -/
  rngNode : ∀ r : Fin lam → Bool, ((m.rng OracleName.node).symm (fun _ => r) : Dig lam) = r

end

/-- In the encoding a leaf's and a vertex's answer is one block, taken as it is. For all data. -/
theorem oneBlock_impl {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : PageC L K tg) :
    OneBlock (theImpl C) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## What a page with one code of bodies must give at the stored symbols -/

section
variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : PageC L K tg)

/-- The first 256 bits of the typed salt are the bytes `cfg`. -/
def startIs (cfg : ByteArray) (q : LeafIn L) : Bool := bitsToBytes (q.salt.take 256) == cfg

/-- The string of a leaf query: what the page's one code of leaves writes, where it writes;
elsewhere the byte 2 and the total code's string. -/
theorem theImpl_code_leaf (q : LeafIn L) (j : Fin 1) :
    (theImpl C).code .leaf q j =
      ((pLeafC C).put q).getD (bitsOfByte 2 ++ C.back.put (.inl (.inl q))) := by
  cases h : (pLeafC C).put q with
  | some s => exact theImpl_leaf C q s h j
  | none =>
    exact PCode.orElse_put_none (pAll C) C.back (bitsOfByte 2) (pAll_no2 C)
      (a := .inl (.inl q)) h

variable {Sg : Type}

/-- The page holds the stored symbols of the type Sg, spelled by the code p, as the bodies `e
y`. `put`: on such a body the page's code of bodies writes what p writes, and nothing where p
writes nothing. `ok`: on such a body the page's test on body and salt together is "the first 256
bits of the typed salt are the page's configuration digest", for every salt. At use p is `pStored a
salt` (OnBytes/TypedOracleCompiler/Run/Tag174.lean) and Sg its (position, column). -/
structure StoredIn (p : PCode Sg) (e : Sg → L.Bd) : Prop where
  /-- the page's code of bodies on a stored symbol is p -/
  put : ∀ y, C.leafP.put (e y) = p.put y
  /-- the page's test on a stored symbol is the test of the start -/
  ok : ∀ y salt, C.leafOK ⟨e y, salt⟩ = startIs C.cfg (⟨e y, salt⟩ : LeafIn L)

/-- What the page writes on a stored symbol: exactly if the first 256 bits of the typed salt are
the configuration digest, the salt has 256 + `saltBits` bits and p writes the symbol: the 33 bytes
with which a call with a digest of 32 bytes begins; the salt's first 256 bits (the call's start);
p's string; the salt's last bits. The spelling of `Tie.pLeafS`. -/
theorem pLeafC_stored {p : PCode Sg} {e : Sg → L.Bd} (h : StoredIn C p e) (y : Sg)
    (salt : List Bool) :
    (pLeafC C).put ⟨e y, salt⟩ =
      (if (bitsToBytes (salt.take 256) == C.cfg) = true then
        (if salt.length = 256 + C.saltBits then
          (p.put y).map (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)))
        else none)
      else none) := by
  show (if C.leafOK ⟨e y, salt⟩ = true then
      (if salt.length = 256 + C.saltBits then
        (C.leafP.put (e y)).map (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)))
      else none)
    else none) = _
  rw [h.ok, h.put]
  rfl

/-- A partial inverse of the embedding: which bodies are stored symbols. Wanted by a reading of logs
("the stored table's symbol in a leaf query, whatever the salt"): OnBytes/TypedOracleCompiler/Slice/LooksAgree.lean.
-/
structure StoredGet (e : Sg → L.Bd) (get : L.Bd → Option Sg) : Prop where
  /-- a stored symbol is read back -/
  get_e : ∀ y, get (e y) = some y
  /-- only stored symbols are read -/
  e_get : ∀ b y, get b = some y → b = e y

end

/-! ## Two pages spell stored leaves and vertices alike -/

/-- The code of the call number 166 writes every pair of strings of 256 bits, from the start
alone. -/
theorem pNode_put256 (start : ByteArray) (x y : Bits) (h1 : x.length = 256) (h2 : y.length = 256) :
    (pNode start).put (x, y) = some (hdr 0 166 0 0 start ++ (x ++ y)) :=
  if_pos ⟨h1, h2⟩

section
variable {I₁ X₁ I₂ X₂ Sg : Type} {lam K₁ K₂ : ℕ} {L₁ : BatchProtocolWithLeafBody I₁ X₁} {L₂ : BatchProtocolWithLeafBody I₂ X₂}

/-- The two implementations spell stored leaves and vertices alike. A vertex query on two
digests has one string in both. A leaf query on a stored symbol has one string in both, for every
symbol and EVERY salt. e₁ and e₂ embed the stored symbols into the two interfaces' bodies. Said for
all numbers of blocks j₁, j₂; under `OneBlock` there is one of each. -/
structure SameStored (m₁ : OracleCoding (typedOracleFamily lam K₁ L₁) lam) (m₂ : OracleCoding (typedOracleFamily lam K₂ L₂) lam)
    (e₁ : Sg → L₁.Bd) (e₂ : Sg → L₂.Bd) : Prop where
  /-- vertices -/
  node : ∀ (a b : Dig lam) j₁ j₂, m₁.code OracleName.node (List.ofFn a, List.ofFn b) j₁ =
    m₂.code OracleName.node (List.ofFn a, List.ofFn b) j₂
  /-- stored leaves -/
  stored : ∀ (x : Sg) (salt : Bits) j₁ j₂, m₁.code OracleName.leaf ⟨e₁ x, salt⟩ j₁ =
    m₂.code OracleName.leaf ⟨e₂ x, salt⟩ j₂

end

/-- The encodings at two pages spell stored leaves and vertices alike, if the pages have one
configuration digest and one length of salt, both hold the stored symbols spelled by ONE code p
(`StoredIn`), and their total codes write leaf queries on stored symbols alike. Of vertices nothing
more is asked: the code of the call number 166 writes every pair of digests, from the configuration
digest alone. That any page meets the hypotheses is not shown. -/
theorem sameStored_impl {I₁ X₁ I₂ X₂ Sg : Type} {L₁ : BatchProtocolWithLeafBody I₁ X₁} {L₂ : BatchProtocolWithLeafBody I₂ X₂} {K₁ K₂ : ℕ}
    {t₁ t₂ : Tag} (C₁ : PageC L₁ K₁ t₁) (C₂ : PageC L₂ K₂ t₂) (p : PCode Sg) (e₁ : Sg → L₁.Bd)
    (e₂ : Sg → L₂.Bd) (h₁ : StoredIn C₁ p e₁) (h₂ : StoredIn C₂ p e₂) (hc : C₁.cfg = C₂.cfg)
    (hs : C₁.saltBits = C₂.saltBits)
    (hb : ∀ x salt, C₁.back.put (.inl (.inl ⟨e₁ x, salt⟩)) =
      C₂.back.put (.inl (.inl ⟨e₂ x, salt⟩))) :
    SameStored (theImpl C₁) (theImpl C₂) e₁ e₂ where
  node := fun a b j₁ j₂ => by
    have la : (List.ofFn a).length = 256 := List.length_ofFn
    have lb : (List.ofFn b).length = 256 := List.length_ofFn
    have hw := fun cfg : ByteArray => pNode_put256 cfg (List.ofFn a) (List.ofFn b) la lb
    rw [theImpl_node C₁ _ _ (hw _) j₁, theImpl_node C₂ _ _ (hw _) j₂, hc]
  stored := fun x salt j₁ j₂ => by
    rw [theImpl_code_leaf, theImpl_code_leaf, hb, pLeafC_stored C₁ h₁, pLeafC_stored C₂ h₂, hc, hs]

/-! ## The string of a call with the number 169 is a point of the spare oracle -/

/-- The first 16 bits of the word with which the label of a call with the number 169 begins. -/
def t169 : List Bool := (bytesToBits (Fmt.u64n 169)).take 16

/-- They are none of the format's five tags. -/
theorem t169_differs : t169 ≠ t160 ∧ t169 ≠ t162 ∧ t169 ≠ t164 ∧ t169 ≠ t166 ∧ t169 ≠ t174 := by
  decide +kernel

/-- The bit string s is the string of a call with the number 169: either half, any tree number t,
any index i, any start of 32 bytes, any bytes. The 32 bytes are asked by the library's lemma on the
tag. -/
def IsCall169 (s : List Bool) : Prop :=
  ∃ (half : UInt8) (t i : ℕ) (st bs : ByteArray), (half = 0 ∨ half = 1) ∧ st.size = 32 ∧
    s = bytesToBits (Fmt.oStr half 169 t i st bs)

section
variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : PageC L K tg)

/-- The string of a call with the number 169 is a point of the spare oracle, written as itself,
through the encoding at any data. Its tag is none of the five (160, 162, 164, 166, 174), and its
first byte is 0 or 1. -/
theorem code_call169 (s : List Bool) (hs : IsCall169 s) (j : Fin 1) :
    (theImpl C).code .other s j = s := by
  obtain ⟨half, t, i, st, bs, hh, hst, rfl⟩ := hs
  rw [oStr_bits half 169 t i st bs]
  have n2 : (2 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  have n3 : (3 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  refine theImpl_other5 C _ j ?_ (hdr_not_prefix 2 half n2 _ _ _ _ _)
    (hdr_not_prefix 3 half n3 _ _ _ _ _)
  have ht : tag16 (hdr half 169 t i st ++ bytesToBits bs) = t169 :=
    (tag16_hdr half 169 t i st hst (bytesToBits bs)).trans (tag_low 169 t)
  unfold Tag5
  rw [ht]
  obtain ⟨d0, d2, d4, d6, d7⟩ := t169_differs
  rintro (h | h | h | h | h)
  · exact d0 h
  · exact d2 h
  · exact d4 h
  · exact d6 h
  · exact d7 h

/-- So it is read back as that point: neither as a vertex nor as a leaf. The form from which a look
at a log goes on. -/
theorem inv_call169 (s : List Bool) (hs : IsCall169 s) :
    (theImpl C).inv s = ⟨OracleName.other, (s, (0 : Fin 1))⟩ := by
  have h := (theImpl C).inv_code ⟨OracleName.other, (s, (0 : Fin 1))⟩
  rw [code_call169 C s hs 0] at h
  exact h

end

end TypedOracleCompiler.Run
