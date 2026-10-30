-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/BigReqAt.lean: carries the facts of Johnson/Flat/BigIns.lean (stated for all
instances), through Johnson/Flat/BigThrough.lean, to the full-size data `bigReq p`
(Johnson/Flat/ThreeAtFiles.lean), whose requests have the type `Flat.Req`: the instances that the
program's reader accepts.

`bigReq p` is `bigIns p ppref _ recZeroFull recZeroFull` read through `Subtype.val`.
  `bigReq_block`, `bigReq_first`, `bigReq_early`, `bigReq_same`: field by field, by unfolding.
  `insReq_insOf`: what `Flat.insReq` returns is, as an instance, what `insOf ppref` returns.
  `spReq Z`: reads the request's item off a request, at Z's three public files.
  `hblk_bigReq`, `hitm_bigReq`: `hblk_bigIns` and `hitm_full` of BigIns.lean for `bigReq p`, with
    `Flat.insReq` reading the request and `spReq Z` reading the item: two sentences "at every served
    call that the program accepts (`K.PortYesAt`) and at which `Flat.insReq` returns a request": the
    block at the call's request is the program's block; `spReq Z` at its early part is the program's
    item. No
    statement of the library takes either as a premise in this form. Sv ("served") is any predicate
    which implies that the call's three public files are Z's (hSv). A, E, P in `hitm_bigReq` are
    data, read only to form the object whose early part is that of `bigReq p`. That their types
    have members is not shown here: where they have none `hitm_bigReq` says nothing.




Assumes: `sizesRefB Z.pol = true` (Johnson/Top/SizesRef.lean: the parameter file states the
reference sizes, under the acceptance policy "exact match"), and that the planner returns p at Z
(`planOf Z = .ok p`). At a call that the program accepts under another acceptance policy the first
fails, and the two laws say nothing.

Limits: those of Johnson/Flat/BigIns.lean's head. At a Sv that holds of no call `hblk_bigReq` and
`hitm_bigReq` say nothing. That the test, the planner's return and an accepted call at Z's files
hold together is shown at no Z. p is the program's own plan (`planOf Z`): nothing
at another plan, nothing
at another function for the hash.


The eight declarations here are used
by no other file. The full size alone. One direction only: from an accepted call to the equations.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.BigThrough
import Johnson.Flat.ThreeAtFiles
import Johnson.Top.InsReq
import Johnson.Top.SizesRef

set_option autoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Maker OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify
open Cb Cb.Ood OnBytes.Slice
open VerifiableInference.OnPublicFiles

/-- The block at a request is the flat description's at its instance. -/
theorem bigReq_block (p : Planned) (q : Flat.Req) :
    (bigReq p).block q = (pubOf p ppref ppref_V_pos).block q.val := rfl

/-- The fixed request is, as an instance, the flat description's fixed instance. -/
theorem bigReq_first (p : Planned) :
    (bigReq p).z₀.1.val = firstInstance ppref ppref_V_pos := rfl

/-- The early part of a request is, as an instance, the instance with the reply 0. -/
theorem bigReq_early (p : Planned) (q : Flat.Req) :
    ((bigReq p).early q).val = withoutReply ppref_V_pos q.val := rfl

/-- The four other fields, and the record beside the fixed request, are those of `bigIns` at the
reference sizes and the record of zeros. -/
theorem bigReq_same (p : Planned) :
    (bigReq p).k = (bigIns p ppref ppref_V_pos recZeroFull recZeroFull).k ∧
      (bigReq p).c = (bigIns p ppref ppref_V_pos recZeroFull recZeroFull).c ∧
      (bigReq p).depthReq = (bigIns p ppref ppref_V_pos recZeroFull recZeroFull).depthReq ∧
      (bigReq p).rec₀ = (bigIns p ppref ppref_V_pos recZeroFull recZeroFull).rec₀ ∧
      (bigReq p).z₀.2 = (bigIns p ppref ppref_V_pos recZeroFull recZeroFull).z₀.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- What `Flat.insReq` returns is, as an instance, what `insOf ppref` returns. -/
theorem insReq_insOf {x : K.UserStm} {q : Flat.Req} (h : Flat.insReq x = some q) :
    insOf ppref x = some q.val := Flat.buildReq_iff.1 h

/-- The function that reads the request's item off a request. -/
def spReq (Z : K.Pub) (q : Flat.Req) : ByteArray :=
  (holdsIns ppref_V_pos Z.pol Z.lay Z.KL).reqX q.val

section Served
variable {p : Planned} {Z : K.Pub} (t : Flat.sizesRefB Z.pol = true) (hpl : planOf Z = .ok p)
  (Sv : K.UserStm → Prop) (hSv : ∀ x, Sv x → x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL)

include t hpl hSv in
/-- **The block at the request of an accepted call whose statement meets Sv (its three public files
are Z's) is the program's block**, for `bigReq p`; under t and hpl. -/
theorem hblk_bigReq :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (q : Flat.Req) (pl' : Planned) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → Flat.insReq (K.stmOf F o) = some q →
      planned F.pol F.KL (some F.lay) = .ok pl' →
      Head.stFromCall (words32 F.request) (words32 F.y) pl'.X.T = .ok so →
      Head.coveredOf so pl'.X.T pl'.X.P.h.V = .ok cov → linksOf pl'.X cov = .ok links →
      (bigReq p).block q = blockAt pl' links so.y :=
  hblk_through ppref_V_pos (Flat.sizesAt_of_test t) hpl Subtype.val Flat.insReq
    (fun _ _ => insReq_insOf) Sv hSv _ (bigReq_block p)

include t hpl hSv in
/-- **The item read off the early part of the request of such a call is the program's item**, for
`bigReq p`; under t and hpl. -/
theorem hitm_bigReq (A : (frS.toDecR frZ 402653181).Claims Flat.Req) (E : Coding A)
    (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigReq p)).Provers) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (q : Flat.Req) (item : ByteArray),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → Flat.insReq (K.stmOf F o) = some q →
      Proof.requestItem F.pol F.KL F.request = some item →
      spReq Z (((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigReq p)).withProvers P).early q) = item :=
  hitm_through ppref_V_pos (Flat.sizesAt_of_test t) hpl Subtype.val Flat.insReq
    (fun _ _ => insReq_insOf) Sv hSv (spReq Z) (fun _ => rfl) _ (bigReq_early p)

end Served

end Johnson.Session
