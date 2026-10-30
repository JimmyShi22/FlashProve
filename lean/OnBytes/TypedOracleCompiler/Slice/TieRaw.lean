-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/TieRaw.lean: the entry's part over the sibling reads the raw string that the
line's entry parts read. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.



"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler. "The
sibling": the files of OnBytes/TypedOracleCompiler/: the library's compiler said again, with a list of roots in a
query and a leaf's body of a type that the interface chooses.

WHY. A part for a key file or a proof file over the sibling must read as the line's parts do
(`SameRaw`). No such part stands.











3 DECLARATIONS, ALL NEW.
 `sameRaw_str_line`, `sameRaw_str_implAt`   for every description: `partChainStr` against the line's
                      `partChain` at `Tie.implAtPd`, at `Tie.implAt`. By `sameRaw_of_walks`:
                      `Part.toO_byWalks` on both sides; one depth, one way of building a string from
                      symbols, by definition; `looks_cross` at `code_node_cross`,
                      `code_stored_cross`.











 `bind_map_refl`      a tool.

WHAT IS NOT SAID. THE CHECKERS ARE NOT TIED HERE. OnBytes/TypedOracleCompiler/Slice/TieYes.lean has one way: where
the line's returns something, the sibling's does, with the same two roots.
ONE PART OF THREE. `SameRaw` speaks of logs in which no two strings have one
answer. No probability. Nothing on any hash.


Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.PartEntryFull
import OnBytes.TypedOracleCompiler.Slice.TieLooks
import OnBytes.Slice.PartEntryTables

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (StmInv okX bodyS)
open OnBytes.Slice (SameRaw sameRaw_of_walks storedSym)
open scoped ENNReal

/-- Carrying symbols along the identity changes nothing. -/
theorem bind_map_refl {α β : Type} (o : Option α) (f : α → Option β) :
    (o.bind fun q => (f q).map (Equiv.refl β)) = o.bind f := by
  cases o with
  | none => rfl
  | some q =>
    show (f q).map (Equiv.refl β) = f q
    cases f q <;> rfl

section
variable {γ γ' : Type} (S0 : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
  (dec : View → Bool) (hcfg : S0.base.cfg.size = 32) (V : StmInv (PQ.xdOf S0 stm))
  (hok : TypedOracleCompiler.Run.PQ.ok (PQ.xdOf S0 stm).base = true)
  (hwork : ∀ d ∈ (PQ.xdOf S0 stm).ds, d.entry.work ≤ 64)
  (hokx : okX (PQ.xdOf S0 stm).ds (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).xs = true)
  (S : Finset (List Bool)) (T : List Bool → Dig 256)
  (Lg : LangT (List Bool) (PQ.xdOf S0 stm) dec) (εs : ℝ≥0∞) (pre : Pre γ)
  (hw : OnBytes.Tie.withinX S0 = true)
  (Lg' : Unit → (twoExternalStrings ((OnBytes.Tie.xdOf S0 stm).L dec).wordLength ((OnBytes.Tie.xdOf S0 stm).L dec).Symbol).Str
      →
    Prop) (εs' : ℝ≥0∞) (V' : OnBytes.Tie.StmInv (OnBytes.Tie.xdOf S0 stm)) (pd' : Dig 256)
  (pre' : Pre γ')

/-- THE PART OVER THE SIBLING READS THE RAW STRING THAT THE LINE'S PART READS, under every root,
off every log in which no two strings have one answer: for every description S0 with its statement
function and decision, `partChainStr` (the sibling's interface, wiring and encoding; strings of bits
as bodies) against the line's `partChain` at the library's encoding `Tie.implAtPd`, at every pd'.
Tables, languages, errors, readers of the statement and what stands before the chain are free on
both sides: a raw string depends on none of them. Both readings are made of the walks of a look
through the part's implementation, in the perfect tree of the stored tables' depth; the two looks
agree (`looks_cross`), because both encodings spell vertices and stored leaves alike, the strings
behind the escape among them (`code_node_cross`, `code_stored_cross`). No probability. -/
theorem sameRaw_str_line :
    SameRaw (partChainStr S0 stm dec hcfg V hok hwork hokx S T Lg εs pre).toO
      (OnBytes.Slice.partChain S0 stm dec hw Lg' εs'
        (OnBytes.Tie.implAtPd S0 stm dec hcfg V' pd') pre').toO := by
  have hL := looks_cross
    (m₁ := PQ.implAtPd (bodyS (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).base.plan.salt) S0 stm
      (leafT (PQ.xdOf S0 stm)) dec hcfg V (T (OnBytes.Slice.s0Of S0.base.params)))
    (m₂ := OnBytes.Tie.implAtPd S0 stm dec hcfg V' pd')
    (e₁ := (bodyS (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).base.plan.salt).embE)
    (get₁ := (bodyS (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).base.plan.salt).getE)
    (oneBlock_impl _) (OnBytes.Slice.oneBlock_implX _)
    (fun a b j₁ j₂ => code_node_cross _ (OnBytes.Tie.xdOf S0 stm) dec (leafT (PQ.xdOf S0 stm)) _ pd'
      _ _ hcfg V V' a b j₁ j₂)
    (fun x salt j₁ j₂ => code_stored_cross _ (OnBytes.Tie.xdOf S0 stm) dec (leafT (PQ.xdOf S0 stm))
      serBits rfl _ pd' _ _ hcfg V V' x salt j₁ j₂)
    ⟨(bodyS _ _).get_e, (bodyS _ _).e_get⟩
  refine sameRaw_of_walks
    (Part.toO_byWalks (partChainStr S0 stm dec hcfg V hok hwork hokx S T Lg εs pre)
      (oneBlock_impl _)
      (Reading.wide_byLeaves
        (PQ.okgAny (bodyS (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).base.plan.salt) (PQ.xdOf S0 stm) dec
          (ownES (PQ.xdOf S0 stm) hok) hwork hokx).B.ext
        (PQ.okgAny (bodyS (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).base.plan.salt) (PQ.xdOf S0 stm) dec
          (ownES (PQ.xdOf S0 stm) hok) hwork hokx).prjE_emb))
    (OnBytes.Slice.Part.toO_byWalks (OnBytes.Slice.partChain S0 stm dec hw Lg' εs'
      (OnBytes.Tie.implAtPd S0 stm dec hcfg V' pd') pre') (OnBytes.Slice.oneBlock_implX _)
      (OnBytes.Slice.Reading.wide_byLeaves
        (OnBytes.Slice.ext_ok_any (OnBytes.Tie.xdOf S0 stm) dec))) hL.1 fun j s => ?_
  exact (bind_map_refl _ _).trans ((hL.2 s).trans (bind_map_refl _ _).symm)

/-- The same at the line's encoding `Tie.implAt`, which holds the format's own digest of the
parameter bytes. Stated for every description, so that Lean need not compare closed terms. -/
theorem sameRaw_str_implAt :
    SameRaw (partChainStr S0 stm dec hcfg V hok hwork hokx S T Lg εs pre).toO
      (OnBytes.Slice.partChain S0 stm dec hw Lg' εs'
        (OnBytes.Tie.implAt S0 stm dec hcfg V') pre').toO :=
  sameRaw_str_line S0 stm dec hcfg V hok hwork hokx S T Lg εs pre hw Lg' εs' V'
    (OnBytes.Tie.pdX (OnBytes.Tie.xdOf S0 stm)) pre'

end

end TypedOracleCompiler.Slice
