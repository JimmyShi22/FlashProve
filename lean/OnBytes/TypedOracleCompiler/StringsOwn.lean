-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsOwn.lean: what the sibling's general form asks of the bodies of a chain's own
symbols, met at strings of bits.

The sibling's statement that a run of its compiled verifier is the same at the typed oracle
functions of a description and at what the encoding reads out of one oracle (`verifyBS_readX`,
OnBytes/TypedOracleCompiler/Run/PageXAsked.lean) asks of the bodies of the chain's own symbols one structure,
`OwnFits`: the page's code of bodies writes the body of every own symbol, and no such body is a
stored symbol.
 - `prjX_none_of_164`: a body that begins with the 16 bits of 164 is read as no stored symbol;
 - `ownFitsS`: `OwnFits` at the instance of OnBytes/TypedOracleCompiler/StringsAt.lean (`bodyS`, `leafS`) and the
   embedding `StringsList.embT`, from the sibling's test `ok` on the description's chain and nothing
   else.

Main theorems: `prjX_none_of_164`, `ownFitsS`.

Not claimed. `verifyBS_readX` is not applied: what it takes besides (`FitsS D.base D.K`, of which
`ok` gives the clause on the salt; `TypedOK` of the argument string; a configuration digest of 32
bytes; a reader for the statement) is given by nobody here. The test is `PQ.ok D.base`: the first
clause of `XD.ok D`; its other clauses are not used. The prover's leaves and the stored table have
one length of salt here, the description's: the general form's choice; `okA_ownB_embTail` holds at
any two. That `StringsList.embT`, `prjT` and `embX`, `prjX` at `cX` are fields of a lawful wire at
the description's interface is shown by nobody. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsAt
import OnBytes.TypedOracleCompiler.StringsMeet
import OnBytes.TypedOracleCompiler.Run.PageXAsked

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open Rom
open _root_.Run (t164)

/-- A body that begins with the 16 bits of 164 is read as no stored symbol. -/
theorem prjX_none_of_164 (a salt : ℕ) (c : StrCode (ℕ × List UInt64)) {b : List Bool}
    (h : b.take 16 = t164) : prjX a salt c b = none := by
  cases hp : prjX a salt c b with
  | none => rfl
  | some y =>
      have e : b = embX a salt c y :=
        (((TypedOracleCompiler.Run.pStored a salt).orElse c esc16 (stored_no_esc a salt)).put_parse b y
          hp).symm
      have h1 := storedLike_embX a salt c y
      rw [← e, storedLike_own h] at h1
      cases h1

end TypedOracleCompiler.Strings

namespace TypedOracleCompiler.Run.PQ
open _root_.Iop (OPos OSym)
open TypedOracleCompiler.Strings TypedOracleCompiler.Slice

/-- The sibling's `OwnFits` at strings of bits, at a description whose chain passes the
sibling's `ok`: the page's code of bodies writes the body of every own symbol, and no such body is
read as a stored symbol. -/
theorem ownFitsS (D : XD) (hok : PQ.ok D.base = true) :
    OwnFits (bodyS D.a D.base.plan.salt) D (leafS D)
      (StringsList.embT D.base.plan.salt D.C D.ds) where
  writes
    | .inl p, _ => p.elim
    | .inr q, a => by
        have h := (okA_ownB_embTail D.base.plan.salt D.C D.a D.base.plan.salt (salt_of D.base hok)
          D.ds (smallL_of_ok D.base hok) q a).1
        show ((if okA D.a D.base.plan.salt (embTail D.base.plan.salt D.C D.ds q a) then
          some (embTail D.base.plan.salt D.C D.ds q a) else none :
            Option (List Bool))).isSome = true
        rw [if_pos h]
        rfl
  notStored
    | .inl p, _ => p.elim
    | .inr q, a =>
        prjX_none_of_164 D.a D.base.plan.salt cX
          (embTail_take164 D.base.plan.salt D.C (salt_of D.base hok) D.ds
            (smallL_of_ok D.base hok) q a)

end TypedOracleCompiler.Run.PQ
