-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/AllAtSorts.lean: THE SMALLNESS TEST: `allHeld_at_drawn`
(Johnson/Desc/K8/Honest/LeftAtDrawn.lean: behind a yes of the batching block, at whatever the round
has drawn, three readings and seven tests of the verifier's test on what the adding has left) AT A
SEGMENT OF EACH OF THE THREE SORTS, WITH NO INVARIANT LEFT AS A LETTER. As in
Johnson/Desc/ProofFile/Honest/K8/FiveAtSorts.lean, THE PREMISE ON THE SEGMENT's OTHER RUNS
(`RunsKeep`) IS MOVED TO THE ONE STATE IN FRONT, NOT PAID: it is built from the same twelve lemmas
of Johnson/P1K8R/LayersApart.lean (four), AttApart.lean (three) and HeadApart.lean (five), under
what these ask of the state in front. None of the library's goals.

  **`allHeld_at_layers`**, **`allHeld_at_att`**, **`allHeld_at_head`**   the sort's ties · the
                   lookups' runs' ties · the sort's order · the state in front shows tl, F, funs ·
                   tl.heard = some g · AllFront tl F g nbW Wn · the link's list has a member for
                   each array · what the sort's lemmas ask of the state in front (LayAsks | AttAsks,
                   the attention's own state and its third vector | HeadWants) · at attention and
                   the head: the third vector's array is the array that the sort's runs name · a yes
                   of the batching block at d ⊢ the state behind shows data tl' and a ledger G with
                   AllHeld tl' G
WRITTEN A FURTHER TIME: the three proofs are those of `fiveHeld_at_layers`, `fiveHeld_at_att` and
`fiveHeld_at_head` (FiveAtSorts.lean) with the one call exchanged. These three ask more than those
and end in more; those stand at a field element in reduced words, these at every drawn value.
Limits. IMPLICATIONS. NO MEMBER. PAID BY NOBODY HERE: AllFront's seventeen · the sentence on the
link's list · the ties · LayAsks, AttAsks, HeadWants and the two premises beside · the equation on
the third vector's array. PAYERS, NOT CALLED HERE, EACH AT EVERY STATE REACHED IN FRONT OF A
BATCHING: AllFront whole: `allFront_at_all` (Johnson/Desc/K8/Honest/AllFrontAtAll.lean) · LayAsks,
AttAsks, HeadWants: `layAsks_at_wrap`, `attAsks_at_wrap`, `headWants_at_wrap` (AsksAtWrap.lean
beside this file); the last two say besides which number the third vector's array has; the first
takes that number as it stands in the state's data. That any such state is reached is said outright
by none of them. THE LEMMAS ON THE OTHER RUNS STAND OVER FURTHER FILES, some of them other kinds'
own: this file is no better than they; which of them are rows of the library is for the library's
own list to say. NOT THE WHOLE OF THE VERIFIER's TEST: see the Limits of
Johnson/Desc/K8/Honest/LeftAtLink.lean. At one drawn value d. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.LeftAtDrawn
import Johnson.Desc.ProofFile.Honest.K8.FiveAtSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest
open _root_.P1K8

/-- **AT A LAYERS' SEGMENT.** -/
theorem allHeld_at_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = First.orderOf .layers) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (hs : LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s)
    (d : Fmt.Drawn) (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G := by
  refine allHeld_at_drawn L 4 layPre layPost (hord.trans lay_order)
    (lay_preOk L p4 nU ties tC tD) (lay_postOk L p4 nU ties) ties.tEq p batch s t' tl F funs hb
    ht hF hf g hg nbW Wn D hT
    (fun u => layKeep u = layKeep s) (fun u => layKeep u = layKeep s)
    ⟨fun o ho run hat m u u' c hu hr => ?_,
      fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu _ h0 _ h =>
        (layKeep_k8 u tl₀ tl₁ F₀ F₂ funs₀ k8 n h0 h).trans hu,
      fun o ho run hat m u u' c hu hr => ?_⟩ d (fun t h => layKeep_drawn p s t _ h) hbt
  · obtain ⟨q, k⟩ := lay_pre L p4 nU ties tC tD _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_only D.pub.apart (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := lay_post L p4 nU ties _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_only D.pub.apart (q cl hcl), k⟩

/-- **AT AN ATTENTION SEGMENT.** -/
theorem allHeld_at_att (L : Link S Claim) (A : Attention.Plan) (nU : Array Nat)
    (ties : LinkJoin.AttTies L (Att.P.parCOf A) nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run → LinkJoin.Under run
      (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (hord : L.order = First.orderOf .attention) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (hs : AttAsks s) (a : AttOwn) (ha : s.here = .att a)
    (hU : Att.P.U3At A (Att.P.plannedK A) a.F) (hU2 : tl.ix.U.getD 2 none = some A.iU3)
    (d : Fmt.Drawn) (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G := by
  refine allHeld_at_drawn L 4 attPre [] (by rw [hord]; rfl)
    (att_pre L (Att.P.parCOf A) nU ties tC tD tJ tP) (post_nil L) ties.tEq p batch s t' tl F funs
    hb ht hF hf g hg nbW Wn D hT
    (AttInv A s) (fun _ => True)
    ⟨fun o ho run hat m u u' c hu hr => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ ho => nomatch ho⟩ d
    (fun t h => ⟨attKeep_drawn p s t _ h, attLedger_drawn p s t _ h a ha hU⟩) hbt
  obtain ⟨q, k⟩ := att_pre_apart L A nU ties tC tD tJ tP s hs o ho run hat m u u' c hu hr
  exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩

/-- **AT THE HEAD's SEGMENT.** -/
theorem allHeld_at_head (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L h iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Kinds.Head.callerReaders (Kinds.Head.planesAt iU3))))
    (hord : L.order = First.orderOf .head) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (nbW : Nat) (Wn : List Want)
    (D : AllFront tl F g nbW Wn)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (hs : HeadWants h iU3 p6 s) (hU2 : tl.ix.U.getD 2 none = some iU3)
    (d : Fmt.Drawn) (hbt : batch s [⟨[], d⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ AllHeld tl' G := by
  refine allHeld_at_drawn L 5 headPre headPost (by rw [hord]; rfl)
    (head_pre L h iU3 l piece p6 nU ties tC tD tP) (head_post L h iU3 l piece p6 nU ties)
    ties.tEq p batch s t' tl F funs hb ht hF hf g hg nbW Wn D hT (HeadInv s) (HeadInv s)
    ⟨fun o ho run hat m u u' c hu hr => ?_,
      fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 _ h3 =>
        head_k8_keeps s u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 h3,
      fun o ho run hat m u u' c hu hr => ?_⟩ d
    (fun t hd => ⟨headKeep_drawn p s t _ hd, laterS_drawn p s t _ hd⟩) hbt
  · obtain ⟨q, k⟩ := head_pre_apart L h iU3 l piece p6 nU ties tC tD tP s hs o ho run hat m u u'
      c hu hr
    exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := head_post_apart L h iU3 l piece p6 nU ties s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.allHeld_at_layers
#print axioms ProofFile.Honest.K8.allHeld_at_att
#print axioms ProofFile.Honest.K8.allHeld_at_head
