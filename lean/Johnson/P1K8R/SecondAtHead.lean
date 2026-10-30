-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondAtHead.lean: THE SMALLNESS TEST: AT THE HEAD's SEGMENT: `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES OF THE BATCHING BLOCK, FROM THE
ASSEMBLY's TIES AND PREMISES ON THE STATE IN FRONT OF THE BATCHING ALONE. A lemma; none of the
library's goals. No prover stands in it; nothing on completeness, soundness or hiding. An assembly.

  **`secondEqs_at_head`**   `secondEqs_at_plain` (Johnson/Desc/K8/Honest/SecondAtPlain.lean) at the
      head's order (`headPre`, `headPost`, `head_pre`, `head_post`:
      Johnson/Desc/K8/Honest/FallHead.lean), its four premises on the other runs built from
      `head_pre_apart`, `head_k8_keeps`, `head_post_apart`, `headKeep_drawn`, `laterS_drawn`
      (HeadApart.lean), under what these ask of the state in front: moved there, not shown; from
      "names array iU3 alone" to "names neither the digits' array nor a matrix's array of symbols"
      by `apartOne_of_apartAt` (SecondAtAtt.lean). Its end is the premise of `second_at_link`
      (SecondFew.lean) that speaks of `SecondEqs`
The letter F and the ledger o.F of `HeadWants`'s field head name one ledger: at a state in the
head's opened segment the open ledger is that segment's own.
Limits. EVERY PREMISE ON THE STATE IS SHOWN OF NO STATE HERE. The ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.HeadApart
import Johnson.P1K8R.SecondAtAtt
import Johnson.Desc.K8.Honest.SecondAtPlain
import Johnson.Desc.K8.Honest.FallHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- **AT THE HEAD's SEGMENT: `SecondEqs` BEHIND EVERY YES OF THE BATCHING BLOCK, FROM PREMISES ON
THE STATE IN FRONT ALONE.** The invariants of `secondEqs_at_plain` are no letters any more. -/
theorem secondEqs_at_head (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L h iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Kinds.Head.callerReaders (Kinds.Head.planesAt iU3))))
    (hord : L.order = First.orderOf .head) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (hS : SecondFront tl F) (T : Fo.CoefOK tl F)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R)
    (hs : HeadWants h iU3 p6 s) (hAp : LinkJoin.ApartAt tl iU3) :
    ∀ (x : Cb.Gl.E) (t' : S) (tl' : HTailF2) (G : Fork), batch s [⟨[], chiAt x⟩] = .ok t' →
      tlForkP.get? t' = some (tl', G) → SecondEqs tl' G := by
  refine secondEqs_at_plain L 5 headPre headPost (by rw [hord]; rfl)
    (head_pre L h iU3 l piece p6 nU ties tC tD tP) (head_post L h iU3 l piece p6 nU ties)
    ties.tEq p batch s tl F funs hb ht hF hf hS T hR (HeadInv s) (HeadInv s)
    (fun o ho run hat m u u' c hu hr => ?_)
    (fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 _ h3 =>
      head_k8_keeps s u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 h3)
    (fun o ho run hat m u u' c hu hr => ?_)
    fun x t hd => ⟨headKeep_drawn p s t _ hd, laterS_drawn p s t _ hd⟩
  · obtain ⟨q, k⟩ := head_pre_apart L h iU3 l piece p6 nU ties tC tD tP s hs o ho run hat m u u'
      c hu hr
    exact ⟨fun cl hcl => apartOne_of_apartAt hAp (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := head_post_apart L h iU3 l piece p6 nU ties s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => apartOne_of_apartAt hAp (q cl hcl), k⟩

end P1K8

#print axioms P1K8.secondEqs_at_head
