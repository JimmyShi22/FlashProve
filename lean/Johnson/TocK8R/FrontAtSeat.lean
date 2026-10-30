-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
FrontAtSeat.lean: FROM THE BATCHING's YES ALONE, AT THE SEAT: at each of the 25 links of
onlineDescription's first chain, in scope: where the link's batching's block says yes from the verifier's
state s, the run that the link states under "K8.equations" was called, and said yes, at a state
whose smallness test's structure and list of tables are those of s; equations said yes at these; and
the list of tables is that structure's own closed list.

Statements and proofs: by calls (AtSeat.lean's K8At and k08_scope; K8SitsFront.lean's
k08_front_batch; K8Sits.lean's sits_equations; EquationsOut.lean's eq_funs; the integer-model
thread's yes_alone and k9_of).
Main names:
  FrontSays Lk i pre post s sB: some a, b, z with the gathering's yes from atS.set s a and sB =
    atS.set z.2 b; and, at them: x, what the gathering over pre returns; q, the parts of x's state;
    s.tl? = some q.tl; s.funs? = some q.funs; q.funs = q.tl.funs; equations' yes at q, at the
    ledger's count + the number of x's claims.
  **k08_front_at_seat**: at a link with K8At whose batching is K9.batch atS w under the seat's
    dress: the yes of the link's batching's block from s to sB gives FrontSays.
  **k08_front_scope**: all 25 links in one sentence.
Limits. Those of AtSeat.lean. THE YES OF THE FRAME's STEP BEHIND THE BATCHING IS NOT ASKED HERE. IN
FrontSays a, b AND z ARE SOME: of a nothing is said but that it is there. Nothing on the ledger.
From a yes alone.

-/
import Johnson.TocK8R.AtSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace TocK8

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching orderOf orderAfterOf)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open ProofFile (Cl)
open IM

/-- **What the batching's yes says at a link.** -/
def FrontSays (Lk : Link S Cl) (i : ℕ) (pre post : List (ℕ × String)) (s sB : S) : Prop :=
  ∃ (a b : VerifiableInference.Desc.K9.Part) (z : List Claim × S),
    claimsInBy Lk.each Lk.hear (pre ++ (i, "K8.equations") :: post)
      (VerifiableInference.Desc.K9.atS.set s a) = .ok z ∧
    sB = VerifiableInference.Desc.K9.atS.set z.2 b ∧
    ∃ (x : List Claim × S) (q : K8Part) (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      claimsInBy Lk.each Lk.hear pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      partOf x.2 = some q ∧ s.tl? = some q.tl ∧ s.funs? = some q.funs ∧ q.funs = q.tl.funs ∧
      equations (q.F.nClaim + x.1.length) q.tl q.funs q.F = .ok (tl', F1, cls)

/-- **AT A LINK WITH K8At WHOSE BATCHING IS K9's UNDER THE SEAT's DRESS: FROM THE ONE YES.** -/
theorem k08_front_at_seat {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    {w : VerifiableInference.Desc.K9.Where} {a9 : Place} (hk : a9.kind ≠ KindName.K7)
    (hb : ∀ g, LaidAlone ProofFile.sameReply (Lk.batch g)
      (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w g) (Lk.batch g).name a9)
    (s sB : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h1 : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok sB) :
    FrontSays Lk i pre post s sB := by
  have y := ((yes_alone (hb _) hk s sB rs gs).1 h1).1
  rw [K.order] at y
  obtain ⟨a, b, z, x, run, v, hz, e, hx, hl, hr, ht, hf⟩ :=
    k08_front_batch Lk.each Lk.hear i pre post w K.hpre s sB rs gs y
  obtain ⟨r, hm, hu⟩ := K.hE run hl
  obtain ⟨q, tl', F1, hq, he, -⟩ :=
    (sits_equations p r hm x.1.length x.2 v.2 v.1).1 (hu _ _ _ hr)
  obtain ⟨q1, -, q3⟩ := partOf_some.1 hq
  exact ⟨a, b, z, hz, e, x, q, tl', F1, v.1, hx, hq, ht.symm.trans q1, hf.symm.trans q3,
    eq_funs he, he⟩

/-- **AT EACH OF THE 25 LINKS OF onlineDescription's FIRST CHAIN, IN SCOPE.** -/
theorem k08_front_scope {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ Lk : Link S Cl, c.links[l]? = some Lk ∧
      ∀ (s sB : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
        (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok sB →
        FrontSays Lk (ixOf (subAt l)) (preOf (subAt l)) (postOf (subAt l)) s sB := by
  intro l hl
  obtain ⟨L9, w, -, -, e9, -, -, -, -, -, hb, -⟩ := (k9_of hS hR O).2 l hl
  obtain ⟨Lk, Xl, e, -, K, -⟩ := k08_scope hS hR O l hl
  obtain rfl : Lk = L9 := Option.some.inj (e.symm.trans e9)
  exact ⟨Lk, e, fun s sB rs gs h1 =>
    k08_front_at_seat K (a9 := a9Of l (subAt l)) (fun h => nomatch h) hb s sB rs gs h1⟩

end TocK8

#print axioms TocK8.k08_front_at_seat
#print axioms TocK8.k08_front_scope
