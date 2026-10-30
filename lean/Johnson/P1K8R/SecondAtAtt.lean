-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondAtAtt.lean: THE SMALLNESS TEST: AT AN ATTENTION SEGMENT: `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES OF THE BATCHING BLOCK, FROM THE
ASSEMBLY's TIES AND PREMISES ON THE STATE IN FRONT OF THE BATCHING ALONE. Lemmas; none of the
library's goals. No prover stands in them; nothing on completeness, soundness or hiding. An
assembly.

  `apartOne_of_apartAt`   a claim that names array n3 alone names neither the digits' array nor a
      matrix's array of symbols, where n3 is apart from these at the data (LinkJoin.ApartAt,
      Johnson/Desc/First/Link/Law/OkJoin.lean)
  **`secondEqs_at_att`**   `secondEqs_at_plain` (Johnson/Desc/K8/Honest/SecondAtPlain.lean) at the
      attention's order (`attPre`, `att_pre`, `post_nil`: Johnson/Desc/K8/Honest/FallAtt.lean), its
      premises on the other runs built from `att_pre_apart`, `attKeep_drawn`, `attLedger_drawn`
      (AttApart.lean), under what these ask of the state in front: moved there, not shown. Nothing
      stands behind "K8.equations" in this order, so the second invariant is "true". Its end is the
      premise of `second_at_link` (SecondFew.lean) that speaks of `SecondEqs`. The letters F and a.F
      name one ledger: at a state in an attention segment the open ledger is that segment's own
Limits. EVERY PREMISE ON THE STATE IS SHOWN OF NO STATE HERE. The ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AttApart
import Johnson.Desc.K8.Honest.SecondAtPlain
import Johnson.Desc.First.Link.Law.OkJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- A claim that names array n3 alone names neither the digits' array nor a matrix's array of
symbols: where n3 is apart from these at the data (LinkJoin.ApartAt,
Johnson/Desc/First/Link/Law/OkJoin.lean). -/
theorem apartOne_of_apartAt {tl : HTailF2} {n3 : Nat} {cl : Claim} (hA : LinkJoin.ApartAt tl n3)
    (h : OnlyArray n3 cl) : ApartOne tl cl := by
  obtain ⟨_, _, _, hZ, _, hG, _⟩ := hA
  exact ⟨h _ hZ, fun mu hmu => h _ (hG mu hmu)⟩

/-- **AT AN ATTENTION SEGMENT: `SecondEqs` BEHIND EVERY YES OF THE BATCHING BLOCK, FROM PREMISES ON
THE STATE IN FRONT ALONE.** The invariants of `secondEqs_at_plain` are no letters any more. -/
theorem secondEqs_at_att (L : Link S Claim) (A : Attention.Plan) (nU : Array Nat)
    (ties : LinkJoin.AttTies L (Att.P.parCOf A) nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run → LinkJoin.Under run
      (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (hord : L.order = First.orderOf .attention) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (hS : SecondFront tl F) (T : Fo.CoefOK tl F)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R)
    (hs : AttAsks s) (a : AttOwn) (ha : s.here = .att a)
    (hU : Att.P.U3At A (Att.P.plannedK A) a.F) (hAp : LinkJoin.ApartAt tl A.iU3) :
    ∀ (x : Cb.Gl.E) (t' : S) (tl' : HTailF2) (G : Fork), batch s [⟨[], chiAt x⟩] = .ok t' →
      tlForkP.get? t' = some (tl', G) → SecondEqs tl' G := by
  refine secondEqs_at_plain L 4 attPre [] (by rw [hord]; rfl)
    (att_pre L (Att.P.parCOf A) nU ties tC tD tJ tP) (post_nil L) ties.tEq p batch s tl F funs hb
    ht hF hf hS T hR (AttInv A s) (fun _ => True)
    (fun o ho run hat m u u' c hu hr => ?_)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ ho => nomatch ho)
    fun x t h => ⟨attKeep_drawn p s t _ h, attLedger_drawn p s t _ h a ha hU⟩
  obtain ⟨q, k⟩ := att_pre_apart L A nU ties tC tD tJ tP s hs o ho run hat m u u' c hu hr
  exact ⟨fun cl hcl => apartOne_of_apartAt hAp (q cl hcl), k⟩

end P1K8

#print axioms P1K8.apartOne_of_apartAt
#print axioms P1K8.secondEqs_at_att
