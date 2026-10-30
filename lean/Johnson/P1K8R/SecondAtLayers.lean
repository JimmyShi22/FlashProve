-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondAtLayers.lean: THE SMALLNESS TEST: AT A LAYERS' SEGMENT: `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES OF THE BATCHING BLOCK, FROM THE
ASSEMBLY's TIES AND PREMISES ON THE STATE IN FRONT OF THE BATCHING ALONE. Lemmas; none of the
library's goals. No prover stands in them; nothing on completeness, soundness or hiding. An
assembly.

  `apartOne_of_only`   a claim that names the third array of reads alone names neither the digits'
      array nor a matrix's array of symbols, where the arrays' numbers are apart (`apartB`,
      Johnson/Desc/K8/Honest/ApartOf.lean)
  **`secondEqs_at_layers`**   `secondEqs_at_plain` (Johnson/Desc/K8/Honest/SecondAtPlain.lean) at
      the layers' order, its four premises on the other runs built from `lay_pre`, `layKeep_k8`,
      `lay_post`, `layKeep_drawn` (LayersApart.lean), under what these ask of the state in front:
      moved there, not shown. The invariants are "the state has the three fields of the state in
      front". Its end is the premise of `second_at_link` (SecondFew.lean) that speaks of `SecondEqs`
The cut of the order and the two conditions on its stretches are called: `layPre`, `layPost`,
`lay_order`, `lay_preOk`, `lay_postOk` (Johnson/Desc/K8/Honest/LayersCut.lean).
Limits. EVERY PREMISE ON THE STATE IS SHOWN OF NO STATE HERE. The ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LayersApart
import Johnson.Desc.K8.Honest.SecondAtPlain
import Johnson.Desc.K8.Honest.LayersCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- A claim that names the third array of reads alone names neither the digits' array nor a matrix's
array of symbols: where the arrays' numbers are apart. -/
theorem apartOne_of_only {tl : HTailF2} {cl : Claim} (hA : apartB tl = true)
    (h : OnlyArray ((tl.ix.U.getD 2 none).getD 0) cl) : ApartOne tl cl := by
  obtain ⟨-, -, ⟨u2, -⟩, hm⟩ := (apartB_iff tl).1 hA
  exact ⟨h _ fun e => u2 e.symm, fun mu hmu => h _ fun e => (hm mu hmu).2.2.2 e.symm⟩

/-- **AT A LAYERS' SEGMENT: `SecondEqs` BEHIND EVERY YES OF THE BATCHING BLOCK, FROM PREMISES ON THE
STATE IN FRONT ALONE.** The invariants of `secondEqs_at_plain` are no letters any more. -/
theorem secondEqs_at_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = First.orderOf .layers) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (hS : SecondFront tl F) (T : Fo.CoefOK tl F)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R)
    (hs : LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s) :
    ∀ (x : Cb.Gl.E) (t' : S) (tl' : HTailF2) (G : Fork), batch s [⟨[], chiAt x⟩] = .ok t' →
      tlForkP.get? t' = some (tl', G) → SecondEqs tl' G := by
  refine secondEqs_at_plain L 4 layPre layPost (hord.trans lay_order)
    (lay_preOk L p4 nU ties tC tD) (lay_postOk L p4 nU ties) ties.tEq p batch s tl F funs hb
    ht hF hf hS T hR (fun u => layKeep u = layKeep s) (fun u => layKeep u = layKeep s)
    (fun o ho run hat m u u' c hu hr => ?_)
    (fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu _ h0 _ h =>
      (layKeep_k8 u tl₀ tl₁ F₀ F₂ funs₀ k8 n h0 h).trans hu)
    (fun o ho run hat m u u' c hu hr => ?_) fun x t h => layKeep_drawn p s t _ h
  · obtain ⟨q, k⟩ := lay_pre L p4 nU ties tC tD _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => apartOne_of_only hS.apart (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := lay_post L p4 nU ties _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => apartOne_of_only hS.apart (q cl hcl), k⟩

end P1K8

#print axioms P1K8.apartOne_of_only
#print axioms P1K8.secondEqs_at_layers
