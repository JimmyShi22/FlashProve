-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SerTie.lean: a serialiser of leaves' bodies that writes a stored symbol's body as
the library's serialiser of its tagged bodies writes the stored symbol; and what a page's total code
writes of a leaf query behind the escape.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Why. A page writes a leaf query that its partial codes do not write as the byte 2 and its total
code's string (`backP`, OnBytes/TypedOracleCompiler/Run/SerThin.lean). Two parts read one raw string off a log only
if their pages write a leaf query on a stored symbol as one string, at every salt, behind the escape
too (`sameStored_impl`, hypothesis `hb`: OnBytes/TypedOracleCompiler/Run/PageXJoin.lean). In `backP` the one datum
that enters a leaf query's string is the serialiser of bodies.

Main names (8).
 `tiePut`, `tiePut_some`, `tiePut_none`, `tieGet`, `serTie`   from the bodies' data B, a serialiser
                      sg of stored symbols and any serialiser sb of bodies: a stored symbol's body
                      is written as "some, left, sg's string", any other body as "some, right, sb's
                      string". Both laws of `Ser`, from `B.get_e` and `B.e_get`.
 `serTie_emb`         on `B.embE x` it writes what the library's `Ser.option (Ser.sum sg _)` writes
                      on `some (.inl x)`.
 `backP_leaf`         behind the escape a leaf query is two marks, the body's serial form, the
                      salt's: for every interface, all data, every K; by definition.
 `backP_stored_two`   two total codes with `serTie` at one sg write stored leaves alike: `hb`.

Over OnBytes/TypedOracleCompiler/Run/PlanQXRun.lean (`BodyD`), SerThin.lean and the library's Iop/Ser.lean alone.

What is not said. One slot "some, left": one family of stored symbols a page. That any page takes
this serialiser (at strings of bits: `leafT`, OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean). The comparison
with the library's page: OnBytes/TypedOracleCompiler/Slice/TieEscape.lean. Nothing on soundness; no probability;
nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PlanQXRun
import OnBytes.TypedOracleCompiler.Run.SerThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run

/-! ## A serialiser of bodies that writes stored symbols as the library's does -/

section
variable {Bd : Type} (B : BodyD Bd) (sg : Ser SgX) (sb : Ser Bd)

/-- What `serTie` writes: of a stored symbol's body the bits "some", "left" and sg's string of the
symbol; of any other body the bits "some", "right" and sb's string of the body. -/
def tiePut (b : Bd) : List Bool :=
  match B.getE b with
  | some x => true :: false :: sg.put x
  | none => true :: true :: sb.put b

/-- Of a stored symbol's body it writes "some", "left" and sg's string of the symbol. -/
theorem tiePut_some {b : Bd} {x : SgX} (h : B.getE b = some x) :
    tiePut B sg sb b = true :: false :: sg.put x := by
  unfold tiePut
  rw [h]

/-- Of any other body it writes "some", "right" and sb's string of the body. -/
theorem tiePut_none {b : Bd} (h : B.getE b = none) :
    tiePut B sg sb b = true :: true :: sb.put b := by
  unfold tiePut
  rw [h]

/-- What `serTie` reads. Behind "some", "right" a body that is a stored symbol's is refused: it is
not written so. -/
def tieGet : List Bool → Option (Bd × List Bool)
  | true :: false :: r => (sg.get r).map fun y => (B.embE y.1, y.2)
  | true :: true :: r => (sb.get r).bind fun y => if (B.getE y.1).isNone then some y else none
  | _ => none

/-- A serialiser of bodies that writes a stored symbol's body as the library's serialiser of its
tagged bodies writes the stored symbol. From the bodies' data, a serialiser sg of stored symbols
and any serialiser sb of bodies. -/
def serTie : Ser Bd where
  put := tiePut B sg sb
  get := tieGet B sg sb
  get_put := fun b rest => by
    cases h : B.getE b with
    | some x =>
      rw [tiePut_some B sg sb h]
      show (sg.get (sg.put x ++ rest)).map _ = _
      rw [sg.get_put, Option.map_some, B.e_get b x h]
    | none =>
      rw [tiePut_none B sg sb h]
      show (sb.get (sb.put b ++ rest)).bind _ = _
      rw [sb.get_put, Option.bind_some, h]
      rfl
  put_get := fun s b rest h => by
    match s, h with
    | true :: false :: r, h =>
      obtain ⟨⟨x, r'⟩, hx, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      rw [tiePut_some B sg sb (B.get_e x), sg.put_get r x r' hx]
      rfl
    | true :: true :: r, h =>
      obtain ⟨⟨c, r'⟩, hc, h⟩ := Option.bind_eq_some_iff.1 h
      by_cases hn : (B.getE c).isNone = true
      · rw [if_pos hn] at h
        cases h
        rw [tiePut_none B sg sb (Option.isNone_iff_eq_none.1 hn), sb.put_get r b rest hc]
        rfl
      · rw [if_neg hn] at h
        cases h

/-- On a stored symbol's body it writes what the library's serialiser of tagged bodies writes on the
stored symbol, whatever that has for the other bodies. -/
theorem serTie_emb {β : Type} (so : Ser β) (x : SgX) :
    (serTie B sg sb).put (B.embE x) = (Ser.option (Ser.sum sg so)).put (some (.inl x)) :=
  tiePut_some B sg sb (B.get_e x)

end

/-! ## Behind the escape -/

/-- Behind the escape a leaf query is written as two marks, the body's serial form and the
salt's: for every interface, all data, every K. -/
theorem backP_leaf {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (D : SerP Lf) (K : ℕ) (q : LeafIn (Lf ())) :
    (backP Lf D K).put (.inl (.inl q)) =
      false :: false :: (D.bd.put q.body ++ serBits.put q.salt) := rfl

/-- Two total codes whose serialisers of bodies are `serTie` at ONE serialiser sg of stored
symbols write leaf queries on stored symbols alike, at every symbol and every salt: the hypothesis
`hb` of `sameStored_impl` (OnBytes/TypedOracleCompiler/Run/PageXJoin.lean). The two interfaces, their types of
bodies, the bodies' data and the serialisers of other bodies are free. -/
theorem backP_stored_two {I₁ X₁ I₂ X₂ : Type} (Lf₁ : Unit → BatchProtocolWithLeafBody I₁ X₁) (Lf₂ : Unit → BatchProtocolWithLeafBody I₂ X₂)
    (D₁ : SerP Lf₁) (D₂ : SerP Lf₂) (K₁ K₂ : ℕ) (B₁ : BodyD (Lf₁ ()).Bd) (B₂ : BodyD (Lf₂ ()).Bd)
    (sg : Ser SgX) (sb₁ : Ser (Lf₁ ()).Bd) (sb₂ : Ser (Lf₂ ()).Bd)
    (h₁ : D₁.bd = serTie B₁ sg sb₁) (h₂ : D₂.bd = serTie B₂ sg sb₂) (x : SgX) (salt : Bits) :
    (backP Lf₁ D₁ K₁).put (.inl (.inl ⟨B₁.embE x, salt⟩)) =
      (backP Lf₂ D₂ K₂).put (.inl (.inl ⟨B₂.embE x, salt⟩)) := by
  rw [backP_leaf, backP_leaf, h₁, h₂]
  show false :: false :: (tiePut B₁ sg sb₁ (B₁.embE x) ++ _) =
    false :: false :: (tiePut B₂ sg sb₂ (B₂.embE x) ++ _)
  rw [tiePut_some B₁ sg sb₁ (B₁.get_e x), tiePut_some B₂ sg sb₂ (B₂.get_e x)]

end TypedOracleCompiler.Run.PQ
