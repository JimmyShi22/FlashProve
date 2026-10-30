-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesReadsPart.lean: THE CLAUSE `reads` OF `FileSpec.Delivers`, FOR ANY PART OF
THE COMPILER UNDER OnBytes/TypedOracleCompiler/, from two equations of strings on its implementation; and the clause
`rawRd` of `Three.Beside`.

`FileSpec.Delivers.reads` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean): off a log in which no two strings have
one answer the part reads the one written reading. `Spells` (OnBytes/TypedOracleCompiler/Slice/ShapesReads.lean)
says of an implementation that it spells a vertex query and a leaf query on a stored symbol as the
one written reading reads them. Between the two stand facts on the part that name no string: how its
reading makes a raw string of the leaves. They are gathered in `PlainRead`. That they can be met,
and `Spells` with them: OnBytes/TypedOracleCompiler/Slice/EntryReadsAt.lean (`atRead_plain_wide`, `atRead_spells`),
at an entry's part with the page as its implementation.

Main definitions.
 `PlainRead p a`       the part p reads plainly, at the depth a: its tree has the depth a, its
                       string 2^a symbols; where nothing is found its wiring fills with what is
                       matched with (0, no word); its reading keeps, at every place, what the wire
                       reads from the leaf's body; the wire reads back what it writes, AND NOTHING
                       ELSE.
 `rdAt z dg`           the parts' one written reading at the sizes z: `rawBy` at the digest that dg
                       reads off the first table, z's depth and salt length.
Main theorems.
 `PlainRead.byWalks`   such a part's reading is made of the walks of the look through its
                       implementation, in the way of `rawBy`.
 `PlainRead.storedGet` the wire's reading of bodies has both laws of `StoredGet`.
 `Part.raw_eq_rawBy`   A PART THAT READS PLAINLY AND WHOSE IMPLEMENTATION SPELLS READS `rawBy`.
 `FileSpec.reads_of_spells`   the clause `reads`, at `rdAt z dg`, in the form in which `Delivers`
                       asks it.
 `rawRd_at`, `Three.At.beside_at`   the clause `rawRd`, for a key whose digest is dg of the
                       first table; `Beside` from the three languages and two facts on the files'
                       key.

What is not claimed. That any part reads plainly or any implementation spells. THE LAST CLAUSE OF
`PlainRead` IS NO LAW OF A WIRING: it is owed by whoever chooses the bodies. It cannot be left out:
a body that the wire read as a stored symbol without having written it would have a string of its
own, which the part would read and the written reading would not. All is off logs in which no two
strings have one answer. No probability. Nothing on any hash function. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesReads
import OnBytes.TypedOracleCompiler.Slice.ShapesAt

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Rom _root_.Run _root_.Compile
open _root_.Iop (Dig)
open _root_.Run.PQ (SgX)
open OnBytes.Tie (IdKey)
open TypedOracleCompiler.Run (StoredGet)

variable {γ : Type}

/-- The part p reads plainly, at the depth a. Six facts that name no string. -/
structure PlainRead (p : TypedOracleCompiler.Slice.Part 256 γ SgX) (a : ℕ) : Prop where
  /-- the tree over an external string has the depth a -/
  depth : p.W.depth = a
  /-- an external string has 2^a symbols -/
  len : p.L.wordLength = 2 ^ a
  /-- the wiring's way of building a string has, at each place, the symbol that is found there, and
  where none is found a symbol that is matched with (0, no word) -/
  fill : ∀ (φ : ℕ → Option p.L.Symbol) (q : Fin p.L.wordLength),
    p.u ((p.W.B.ext.build fun q => φ q.val : Fin p.L.wordLength → p.L.Symbol) q) =
      ((φ q.val).map p.u).getD (0, [])
  /-- the part's reading keeps, at every place and whatever the salt, what the wire reads from the
  leaf's body, and builds the string of these in the wiring's way -/
  byLeaves : p.J.R.ByLeaves (TypedOracleCompiler.Slice.keepAll p.W)
    fun φ => p.W.B.ext.build fun q => φ q.val
  /-- the wire reads back the stored symbol that it has written into a body -/
  back : ∀ s, p.W.prjE (p.W.embE s) = some s
  /-- and it reads a stored symbol from no other body -/
  only : ∀ b s, p.W.prjE b = some s → b = p.W.embE s

namespace PlainRead
variable {p : TypedOracleCompiler.Slice.Part 256 γ SgX} {a : ℕ}

/-- What the wiring builds of symbols carried back, as a raw string, is what `mkZ` makes. -/
theorem mk_eq (h : PlainRead p a) (ψ : ℕ → Option SgX) :
    rawOf p.u (p.W.B.ext.build fun q => (ψ q.val).map p.u.symm : Fin p.L.wordLength → p.L.Symbol) =
      mkZ a ψ := by
  funext j
  unfold rawOf mkZ
  by_cases hj : j < p.L.wordLength
  · rw [dif_pos hj, if_pos (h.len ▸ hj), h.fill (fun j => (ψ j).map p.u.symm) ⟨j, hj⟩]
    show some ((((ψ j).map p.u.symm).map p.u).getD (0, [])) = _
    rw [Option.map_map, Equiv.self_comp_symm, Option.map_id]
    rfl
  · rw [dif_neg hj, if_neg (h.len ▸ hj)]

/-- Such a part's reading is made of the walks of the look through its implementation, in the
perfect tree of depth a, with what the wire reads from the leaf's body at every place, and
(0, no word) where nothing is found. Asked: one block for a leaf's and a vertex's answer. -/
theorem byWalks (h : PlainRead p a) (one : TypedOracleCompiler.Run.OneBlock p.m) :
    p.toO.ByWalks (TypedOracleCompiler.Slice.lookOf p.m) (posOf a)
      (fun _ q => (p.W.prjE q.body).map p.u) (mkZ a) where
  raw_eq := fun σ cm => by
    have hd := h.depth
    subst hd
    rw [(TypedOracleCompiler.Slice.Part.toO_byWalks p one h.byLeaves).raw_eq σ cm]
    exact h.mk_eq fun j => ((TypedOracleCompiler.Slice.lookOf p.m).walk σ (posOf p.W.depth j) cm).bind
      fun q => (p.W.prjE q.body).map p.u

/-- The wire's reading of bodies, carried to the shared symbols, has both laws of `StoredGet`. -/
theorem storedGet (h : PlainRead p a) :
    StoredGet (L := p.L) (fun y => p.W.embE (p.u.symm y)) fun b => (p.W.prjE b).map p.u where
  get_e := fun y => by
    show (p.W.prjE (p.W.embE (p.u.symm y))).map p.u = some y
    rw [h.back]
    show some (p.u (p.u.symm y)) = some y
    rw [Equiv.apply_symm_apply]
  e_get := fun b y hy => by
    obtain ⟨s, hs, hu⟩ := Option.map_eq_some_iff.1 hy
    show b = p.W.embE (p.u.symm y)
    rw [← hu, Equiv.symm_apply_apply]
    exact h.only b s hs

end PlainRead

/-- A PART THAT READS PLAINLY AND WHOSE IMPLEMENTATION SPELLS READS THE ONE WRITTEN READING, off
every log in which no two strings have one answer. What is asked of the implementation: one block
for a leaf's and a vertex's answer, and the two equations of strings of `Spells`, at the wire's way
of writing a stored symbol into a body. -/
theorem Part.raw_eq_rawBy (p : TypedOracleCompiler.Slice.Part 256 γ SgX) {a : ℕ} (h : PlainRead p a)
    (one : TypedOracleCompiler.Run.OneBlock p.m) (c : ByteArray) (hc : c.size = 32) (n : ℕ)
    (hS : Spells p.m (fun y => p.W.embE (p.u.symm y)) c a n) (σ : Trace (rom 256))
    (hσ : NoClash σ) (cm : Dig 256) : p.raw σ cm = rawBy c a n σ cm :=
  hS.reads (s := p.toO) one h.storedGet hc (h.byWalks one) σ hσ cm

/-! ## At the sizes z -/

/-- The parts' one written reading at the sizes z: `rawBy` at the configuration digest that dg
reads off the first table, at the depth of z's shape and its salt's length. The second table is not
read. -/
noncomputable def rdAt (z : Size) (dg : Tab → ByteArray) (T₀ _T₁ : Tab) (σ : Trace (rom 256))
    (cm : Dig 256) : Raw SgX :=
  rawBy (dg T₀) z.T.a z.shape.saltBytes σ cm

/-- THE CLAUSE `reads`, in the form in which `FileSpec.Delivers` asks it, at `rdAt z dg`. Asked
at all tables: the part reads plainly at z's depth; one block (the clause `one`); the implementation
spells at the digest off the first table, z's depth and salt length. The digest has 32 bytes. -/
theorem FileSpec.reads_of_spells (φ : FileSpec) (z : Size) (dg : Tab → ByteArray)
    (hdg : ∀ T₀, (dg T₀).size = 32) (hP : ∀ T₀ T₁, PlainRead (φ.part T₀ T₁) z.T.a)
    (one : ∀ T₀ T₁, TypedOracleCompiler.Run.OneBlock (φ.part T₀ T₁).m)
    (hS : ∀ T₀ T₁, Spells (φ.part T₀ T₁).m
      (fun y => (φ.part T₀ T₁).W.embE ((φ.part T₀ T₁).u.symm y)) (dg T₀) z.T.a
      z.shape.saltBytes) :
    ∀ T₀ T₁ σ, NoClash σ → ∀ cm, (φ.part T₀ T₁).raw σ cm = rdAt z dg T₀ T₁ σ cm :=
  fun T₀ T₁ σ hσ cm =>
    Part.raw_eq_rawBy (φ.part T₀ T₁) (hP T₀ T₁) (one T₀ T₁) (dg T₀) (hdg T₀) _ (hS T₀ T₁) σ hσ cm

/-- THE CLAUSE `rawRd`: the parts' reading at the sizes z is `rawZ z` at every key whose
configuration digest is dg of the first table. -/
theorem rawRd_at (z : Size) (dg : Tab → ByteArray) (T₀ T₁ : Tab) (k : IdKey)
    (hk : k.2.1 = dg T₀) (σ : Trace (rom 256)) (cm : Dig 256) :
    rdAt z dg T₀ T₁ σ cm = rawZ z k σ cm := by
  unfold rdAt rawZ
  rw [hk]

/-- ALL OF `Beside` AT `rdAt z dg`: from the three languages and two facts on the files' key: it
holds z's shape, and its configuration digest is dg of the first table, whatever the files. -/
theorem Three.At.beside_at {z : Size} {Xi : Type} {Θ : Three z.D Xi} (h : Θ.At z)
    (dg : Tab → ByteArray)
    (langK : ∀ T₀ T₁ oK Y, (Θ.K T₀ T₁).Lang oK [Y] →
      DecR.LangK Θ.A (DecR.wayColl z.D) (Θ.recK T₀ T₁ oK) Y)
    (langE : ∀ T₀ T₁ oE Y₀ Y₁, (Θ.E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE (DecR.wayColl z.D) (Θ.recE₀ T₀ T₁ oE) (Θ.recE₁ T₀ T₁ oE) Y₀ Y₁)
    (langF : ∀ T₀ T₁ oF Y, (Θ.F T₀ T₁).Lang oF [Y] →
      DecR.LangP Θ.A (DecR.wayColl z.D) (Θ.xOf T₀ T₁ oF) (Θ.recF T₀ T₁ oF) Y)
    (keyShape : ∀ T₀ T₁ d, (Θ.key T₀ T₁ d).1 = z.shape)
    (keyDig : ∀ T₀ T₁ d, (Θ.key T₀ T₁ d).2.1 = dg T₀) : Θ.Beside (rdAt z dg) :=
  h.beside langK langE langF keyShape fun T₀ T₁ d σ cm =>
    rawRd_at z dg T₀ T₁ _ (keyDig T₀ T₁ d) σ cm

end OnBytes.Slice.Shapes
