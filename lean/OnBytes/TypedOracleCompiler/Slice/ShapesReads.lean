-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesReads.lean: what an implementation owes so that its part reads the one
written reading; and that the parts of the library's compiler for chains with stored tables read it,
at every description.

`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) has the clause `reads`: off a log in which no
two strings have one answer the part reads the one written reading. That reading is `rawBy`
(OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean), said by two kinds of strings. So what is owed is said by strings
too: THE IMPLEMENTATION SPELLS a vertex query as `nodeStr` and a leaf query on a stored symbol as
`leafStr` (`Spells`).

Main definition: `Spells m e c a n`, for an implementation m over the compiler under OnBytes/TypedOracleCompiler/.
Main theorems.
 `Spells.looks`        then the look through m agrees with `lookZ c a n`.
 `Spells.reads`        a part whose reading is made of the walks of the look through m, in the
                       tree of depth a, with (0, no word) where nothing is found, reads
                       `rawBy c a n`.
 `look_page`, `partChain_raw_eq_rawBy`   A GUARD, GENERAL IN THE DESCRIPTION: the look through the
                       library's encoding of any description of a chain with stored tables agrees
                       with `lookZ` at the description's digest, depth and salt length; so the
                       library's part for such a chain reads `rawBy` there.

What is not claimed. That any implementation over the compiler under OnBytes/TypedOracleCompiler/ meets `Spells`, or
that any part's reading is so made of walks (`Spells` is shown of one implementation, that of an
entry's part with the page, in OnBytes/TypedOracleCompiler/Slice/EntryReadsAt.lean: `atRead_spells`;
`atRead_plain_wide` there shows `PlainRead` of that part, from which `PlainRead.byWalks`,
OnBytes/TypedOracleCompiler/Slice/ShapesReadsPart.lean, draws the walks where a leaf's and a vertex's answer is one
block). All is off logs in which no two strings have one
answer. No probability. Nothing on any hash function. The compiler under OnBytes/TypedOracleCompiler/ is the one
that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesRaw
import OnBytes.TypedOracleCompiler.Slice.LooksAgree
import OnBytes.Slice.RawWalks

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Rom _root_.Run _root_.Compile
open _root_.Iop (Dig)
open _root_.Run.PQ (SgX)

/-! ## Over the compiler under OnBytes/TypedOracleCompiler/ -/

section
open TypedOracleCompiler.Compile.Batch (typedOracleFamily LeafIn)
open TypedOracleCompiler.Run (StoredGet)
variable {I X : Type} {K : ℕ} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X}

/-- The implementation m spells vertices and stored leaves as the one written reading reads
them, at the digest c, the depth a and salts of n bytes. e embeds the stored symbols into the
interface's bodies. Said for all numbers of blocks j; under `OneBlock` there is one. Met by an
implementation whose code of leaves writes the query on e y with a salt exactly where `callStr`
does, and whose total code behind the byte 2 writes it as two marks, "some", "left" and the two
serial forms (OnBytes/TypedOracleCompiler/Run/SerTie.lean): SO THE TOTAL CODE BEHIND THE BYTE 2 IS NOT FREE. -/
structure Spells (m : OracleCoding (typedOracleFamily 256 K L) 256) (e : SgX → L.Bd) (c : ByteArray) (a n : ℕ) :
    Prop where
  /-- a vertex query on two digests is spelled as the vertex's string -/
  node : ∀ (x y : Dig 256) j,
    m.code TypedOracleCompiler.Compile.Batch.OracleName.node (List.ofFn x, List.ofFn y) j = nodeStr c (x, y)
  /-- a leaf query on a stored symbol, with any salt, is spelled as the stored leaf's string -/
  stored : ∀ (y : SgX) (salt : Bits) j,
    m.code TypedOracleCompiler.Compile.Batch.OracleName.leaf ⟨e y, salt⟩ j = leafStr c a n y salt

variable {m : OracleCoding (typedOracleFamily 256 K L) 256} {e : SgX → L.Bd} {get : L.Bd → Option SgX}
  {c : ByteArray} {a n : ℕ}

/-- Then the look through m agrees with the look by strings: both read the same strings as the
same vertices, and what `get` reads from the body of m's leaf is the stored symbol that `lookZ`
finds. Asked: one block for a leaf's and a vertex's answer; both laws of `StoredGet`. -/
theorem Spells.looks (h : Spells m e c a n) (h1 : TypedOracleCompiler.Run.OneBlock m)
    (g : StoredGet e get) :
    (∀ s, (TypedOracleCompiler.Slice.lookOf m).node s = (lookZ c a n).node s) ∧
      ∀ s, ((TypedOracleCompiler.Slice.lookOf m).leaf s).bind (fun q => get q.body) =
        (lookZ c a n).leaf s := by
  constructor
  · intro s
    refine Option.ext fun x => ?_
    rw [TypedOracleCompiler.Slice.lookOf_node, inv_iff_code, lookZ_node]
    constructor
    · rintro ⟨k, hk⟩
      exact hk.trans (h.node _ _ _)
    · intro hs
      exact ⟨⟨0, by rw [h1.node1]; omega⟩, hs.trans (h.node _ _ _).symm⟩
  · intro s
    refine Option.ext fun y => ?_
    rw [lookZ_leaf]
    constructor
    · intro hy
      obtain ⟨q, hq, hg⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨k, hk⟩ := (inv_iff_code m s TypedOracleCompiler.Compile.Batch.OracleName.leaf q).1
        ((TypedOracleCompiler.Slice.lookOf_leaf m s q).1 hq)
      have hb : q = ⟨e y, q.salt⟩ := by
        cases q with
        | mk body salt => exact congrArg (fun b => (⟨b, salt⟩ : LeafIn L)) (g.e_get body y hg)
      rw [hb] at hk
      exact ⟨q.salt, hk.trans (h.stored _ _ _)⟩
    · rintro ⟨salt, hs⟩
      have h2 : (TypedOracleCompiler.Slice.lookOf m).leaf s = some ⟨e y, salt⟩ :=
        (TypedOracleCompiler.Slice.lookOf_leaf m s _).2
          ((inv_iff_code m s TypedOracleCompiler.Compile.Batch.OracleName.leaf _).2
            ⟨⟨0, by rw [h1.leaf1]; omega⟩, hs.trans (h.stored _ _ _).symm⟩)
      rw [h2]
      exact g.get_e y

/-- WHAT IS OWED FOR THE CLAUSE `reads`. A part whose reading is made of the walks of the look
through m, in the perfect tree of depth a, with `get` of the leaf's body at every place and
(0, no word) where nothing is found, reads `rawBy c a n` off every log in which no two strings have
one answer. -/
theorem Spells.reads {γ : Type} {s : PartO 256 γ SgX} (h : Spells m e c a n)
    (h1 : TypedOracleCompiler.Run.OneBlock m) (g : StoredGet e get) (hc : c.size = 32)
    (hw : s.ByWalks (TypedOracleCompiler.Slice.lookOf m) (posOf a) (fun _ q => get q.body) (mkZ a))
    (σ : Trace (rom 256)) (hσ : NoClash σ) (cm : Dig 256) : s.raw σ cm = rawBy c a n σ cm :=
  hw.raw_eq_rawBy c hc n (h.looks h1 g).1 (h.looks h1 g).2 σ hσ cm

end

/-! ## A guard: the library's compiler, at every description -/

section
open _root_.Iop Prob Compile.Batch _root_.Run.PQ
open scoped ENNReal
open OnBytes.Tie (xdOf withinX)

/-- The look through the library's encoding of any description of a chain with stored tables
agrees with the look by strings, at the description's configuration digest, depth and salt
length. -/
theorem look_page (D : XD) (dec : View → Bool) (pd : Dig 256) (K : ℕ)
    (hcfg : D.base.cfg.size = 32) (V : Tie.StmInv D) :
    (∀ s, (lookOf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V))).node s =
        (lookZ D.base.cfg D.a D.base.plan.salt).node s) ∧
      ∀ s, ((lookOf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V))).leaf s).bind
        storedSym = (lookZ D.base.cfg D.a D.base.plan.salt).leaf s :=
  ⟨fun s => Option.ext fun x =>
      (look_node (Tie.pageXPd (D := D) dec pd K hcfg V) s x).trans (lookZ_node _ _ _ s x).symm,
    fun s => Option.ext fun y =>
      (look_stored_page D dec pd K hcfg V s y).trans (lookZ_leaf _ _ _ s y).symm⟩

/-- So the library's part for such a chain, at that encoding, reads `rawBy` at the description's
digest, depth and salt length, off every log in which no two strings have one answer. -/
theorem partChain_raw_eq_rawBy {γ : Type} (S0 : Fmt.SpecX)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (hw : withinX S0 = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (pd : Dig 256) (hcfg : (xdOf S0 stm).base.cfg.size = 32) (V : Tie.StmInv (xdOf S0 stm))
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (σ : Trace (rom 256)) (hσ : NoClash σ) (cm : Dig 256) :
    (partChain S0 stm dec hw Lg εs
      (Tie.theImplX (Tie.pageXPd (D := xdOf S0 stm) dec pd _ hcfg V)) pre).raw σ cm =
      rawBy (xdOf S0 stm).base.cfg (xdOf S0 stm).a (xdOf S0 stm).base.plan.salt σ cm := by
  rw [← rawBy_of_walks _ storedSym _ hcfg _ _ (look_page (xdOf S0 stm) dec pd _ hcfg V).1
    (look_page (xdOf S0 stm) dec pd _ hcfg V).2 σ hσ cm]
  funext j
  rw [partChain_raw_walks S0 stm dec hw Lg εs _ pre (oneBlock_implX _) σ cm j]
  rfl

end

end OnBytes.Slice.Shapes
