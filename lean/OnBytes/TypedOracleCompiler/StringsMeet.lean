-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsMeet.lean: where the bodies that are strings meet the sibling's road from a
parsed file.

The sibling's statement on what follows the chain (`pi_after`, OnBytes/TypedOracleCompiler/Run/PageIsAfterTop.lean)
is for any type of bodies. Where the library has a `rfl`, it takes a hypothesis: the page's reader
of bodies spells every symbol's body as the format does. This file meets that hypothesis for bodies
that are strings, from the sibling's test `ok` on a description and nothing else:
 - `smallL_of_ok`: the trees of a description that passes `ok` meet the bounds of
   OnBytes/TypedOracleCompiler/StringsBounds.lean (by the sibling's `small_of`, OnBytes/TypedOracleCompiler/Run/SmallTrees.lean);
 - `leaf_of_ok`: the reader behind the test (`rdOk`) reads from the body of every symbol
   (`StringsList.embT`) the sibling's own spelling of its leaf;
 - `okRd_of_ok`: every such body passes the test `okRd`;
 - `pi_after_strings`: the sibling's `pi_after` at bodies that are strings, with no hypothesis on
   bodies left.

Main theorems: `smallL_of_ok`, `leaf_of_ok`, `okRd_of_ok`, `pi_after_strings`.

Not claimed. Nothing beyond the sibling's statement but that its hypothesis on bodies is met; what
its head says of it holds here: above all it is at ONE list of rounds, at an interface without an
external string, under the tag of Batch, and the sibling's lenient facts on a parsed file are
hypotheses. The sibling's `ok` shuts a key's shared and second chains out (no tree given from
outside; each own tree opened at most once). Nothing at the protocol in three stretches. The way of
writing external symbols is a parameter, of which nothing is asked: the interface has none. The
reader here is `rdOk`: 164 alone. What ties the family `famOf O (PDS … rdOk)` to the maps of
OnBytes/TypedOracleCompiler/StringsBoth.lean (`call2`, for the sibling's `famT`) is OnBytes/TypedOracleCompiler/StringsAt.lean's
`call2_of_okRd`, at bodies under 164; at a body under 174 the two differ. No page and no one oracle:
O is any function with values of 32 bytes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsBounds
import OnBytes.TypedOracleCompiler.Run.SmallTrees
import OnBytes.TypedOracleCompiler.Run.PageIsAfterTop

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop (OPos OSym Rho Plains Dig)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings

/-- The trees of a description that passes the sibling's `ok` meet the bounds on trees. -/
theorem smallL_of_ok (S : _root_.Fmt.Spec) (hok : PQ.ok S = true) : SmallL (PQ.rds S) :=
  fun d hd => SmallT.of_le fun s hs =>
    ⟨(PQ.small_of S hok d hd s hs).1.1, (PQ.small_of S hok d hd s hs).1.2,
      (PQ.small_of S hok d hd s hs).2⟩

variable (C : PQ.CK)

/-- The reader behind the test reads from every symbol's body the sibling's own spelling of its
leaf, at a description that passes the sibling's `ok`: the hypothesis on bodies of the sibling's
`pi_after`. -/
theorem leaf_of_ok (S : _root_.Fmt.Spec) (hok : PQ.ok S = true) (p : OPos (PQ.uL C (PQ.rds S)))
    (a : OSym (PQ.uL C (PQ.rds S)) p) :
    rdOk (StringsList.embT S.plan.salt C (PQ.rds S) (.inr p) a) =
      some (PQ.leafSL C S.plan.salt (PQ.rds S) ⟨p, a⟩) :=
  rdOk_embTail_of_small S.plan.salt C (PQ.salt_of S hok) (PQ.rds S) (smallL_of_ok S hok) p a

/-- And every such body passes `okRd`. -/
theorem okRd_of_ok (S : _root_.Fmt.Spec) (hok : PQ.ok S = true) (p : OPos (PQ.uL C (PQ.rds S)))
    (a : OSym (PQ.uL C (PQ.rds S)) p) :
    okRd (StringsList.embT S.plan.salt C (PQ.rds S) (.inr p) a) = true :=
  embTail_okRd_of_small S.plan.salt C (PQ.salt_of S hok) (PQ.rds S) (smallL_of_ok S hok) p a

end TypedOracleCompiler.Slice

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (ChainOut)
open TypedOracleCompiler.Strings (rdOk)

/-- The sibling's `pi_after` at bodies that are strings, with no hypothesis on bodies left: the
statement is the sibling's own, word for word, at Bd := strings of bits, leaf := `rdOk`, embS :=
`StringsList.embT`. -/
theorem pi_after_strings (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (hok : ok S = true) (embE : E0.Sym → List Bool)
    (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S))) (ρ : Rho (uL C (rds S)))
    (v : Bits) (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run)
    (hp : plainsSL C (rds S) o.rounds.toList = some pl)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) 0 ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) = true ∧
    afterP (fun _ => LbS (List Bool) C (rds S) dec)
        (famOf O (PDS (List Bool) S C dec rdOk) (K + 1)) (PSof C (rds S) dec)
        (wqS C K chal (rds S) dec) (StringsList.embT S.plan.salt C (rds S))
        embE 0 [bytesToDig o.pd] ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some []), rtSL C (rds S) o.rounds.toList) (.loc v) =
      (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList &&
        (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o))) :=
  pi_after (List Bool) rdOk O hO S C K chal dec hok
    (StringsList.embT S.plan.salt C (rds S)) embE (Slice.leaf_of_ok C S hok) o run pl ρ v hf hr hp
    hd

end TypedOracleCompiler.Run.PQ
