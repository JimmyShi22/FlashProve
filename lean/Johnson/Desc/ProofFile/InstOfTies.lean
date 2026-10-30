-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/InstOfTies.lean: two ties of `ProofFile.instOf` (InstOf.lean) to texts that lie in
the library. Two theorems. No definition: no goal is stated.
  **`instOf_at_frame`**: `ProofFile.instOf` reads back what the verifier's own map from its instances to
    the description's lays: at every z : XF × RecFull, `instOf (LPFD.Full.instanceAsPlainRecord z) = some z.1.val`
    (`LPFD.Full.instanceAsPlainRecord`, Johnson/Desc/Laid/ProofFull.lean, with `instOf_request`, `instOf_reply`:
    ProofFullLaw.lean). So at every instance that `LPFD.Full.instanceAsPlainRecord` lays the reading returns, and
    returns the request z.1 that was laid. (ProofFull.lean's head calls that map the verifier's
    instance as the description's plain record; no theorem on the verifier is cited here.)
  **`sameRequest_of_instOf`**: the agreement of `instOf_agrees` in the output head's own form: with
    the head's public letters laid off Z and ξ (the sizes of `Z.p.X.hS`; the request that the seat
    reads off `startS Z ξ.pub`; the token of the reply that is asked about), and under the four
    numbers of `HeadScope ppref`, `SameRequest ppref x` holds
    (Johnson/Desc/Kinds/Law/ProgramBridge.lean, SameRequestOf.lean). By `sameRequest_unique` there x
    is the one typed request that these letters state.
Limits. Those of InstOf.lean: the reference sizes alone; hT, hV and `HeadScope ppref` are premises
here (who pays the last: Johnson/Desc/Kinds/Law/HeadScopeAt.lean). THE LETTERS OF
`sameRequest_of_instOf` ARE THOSE AT THE FIRST STATE AND AT THE TOKEN THAT IS ASKED ABOUT. Where the
output head's block runs, its seat reads the request off the state at the head's own rounds, and
lays the token of the reply that this state holds (`seatAt`, Johnson/Stored/HeadSeatAt.lean). That
the request stays from the first state up to these rounds, and that the reply held there is the one
asked about, is not shown here: so x is not yet shown to be the request of the head's laws. Nothing
on a trace, on an honest prover or on whether anything is accepted. Nothing on soundness, on a
binding of the commitment (the opening form, `BindsWith`), on correctness of extraction, on
completeness or on hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.InstOf
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Kinds.Law.SameRequestOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile
open OnBytes OnBytes.Flat OnBytes.Model
open _root_.Inst.Model (ppref Instance)
open VerifiableInference.Desc.Kinds.Head (Sizes Request Token sizesOf requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (HeadScope SameRequest)

/-- **What the verifier's own map lays is read back.** -/
theorem instOf_at_frame (z : LPFD.Full.XF × RecFull) :
    instOf (LPFD.Full.instanceAsPlainRecord z) = some z.1.val :=
  instOf_of_eq z.1 (LPFD.Full.instOf_request z) (LPFD.Full.instOf_reply z)

/-- **The agreement in the output head's own form**, at the first state's request and the asked
token. -/
theorem sameRequest_of_instOf {Z : Pub} (hT : Z.p.X.T = ppref.T) (hV : Z.p.X.P.h.V = ppref.V)
    {ξ : Inst} {x : Instance ppref} (h : instOf ξ = some x) :
    letI : Sizes := sizesOf Z.p.X.hS
    letI : Request := requestOf (startS Z ξ.pub)
    letI : Token := ⟨OnBytes.Desc.Reply.tokOf ξ.asked⟩
    HeadScope ppref → SameRequest ppref x := by
  intro Sc
  letI : Sizes := sizesOf Z.p.X.hS
  letI : Request := requestOf (startS Z ξ.pub)
  letI : Token := ⟨OnBytes.Desc.Reply.tokOf ξ.asked⟩
  obtain ⟨-, a1, a2, a3, -, a5, -, -⟩ := instOf_agrees hT hV h
  exact ⟨Sc.hT, Sc.hV, Sc.hd, Sc.hsh, fun i hi => a3 ⟨i, hi⟩, a1, a2, a5⟩

end ProofFile

#print axioms ProofFile.instOf_at_frame
#print axioms ProofFile.sameRequest_of_instOf
