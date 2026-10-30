-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FiveAtSorts.lean: THE SMALLNESS TEST: `fiveHeld_at_link`
(Johnson/Desc/K8/Honest/TiesAtLink.lean: behind a yes of the batching block at a challenge x, six of
the eight conjuncts of the verifier's clause on the ties' and the planes' shapes and its tests on
the planes' weights, the reads' shapes and the reads' weights say yes) AT A SEGMENT OF EACH OF THE
THREE SORTS, WITH NO INVARIANT LEFT AS A LETTER. As in
Johnson/Desc/ProofFile/Honest/K8/FourAtSorts.lean, THE PREMISE ON THE SEGMENT's OTHER RUNS
(`RunsKeep`) IS MOVED TO THE ONE STATE IN FRONT, NOT PAID: it is built from the same twelve lemmas
of Johnson/P1K8R/LayersApart.lean (four), AttApart.lean (three) and HeadApart.lean (five), UNDER
WHAT THESE ASK OF THE STATE IN FRONT. OTHER THAN THERE: at attention and the head the premise
`LinkJoin.ApartAt` IS EXCHANGED FOR ONE EQUATION: the third vector's array is the array that the
sort's runs name; that it is another than the digits' and the bits' is a clause of the public test
`apartB`, which stands among the premises already. None of the library's goals.

  `FiveFront s tl F g`   `fiveHeld_at_link`'s ten premises on the data and the ledger in front, as
                   one structure: PubAt · the reads' row and the bits' three rows begin at column 0
                   · BitsFront · BitsPub · the link's list has a member for each array · the digits'
                   array has 2 mz columns · SymbolsFront · symbolsLaid · TiesRest. A DRESS, NO
                   PAYMENT
  `fourRows_of_third`   the third vector's array is n3 · apartB tl = true · a claim that names array
                   n3 alone ⊢ FourRows tl
  **`fiveHeld_at_layers`**, **`fiveHeld_at_att`**, **`fiveHeld_at_head`**   the sort's ties · the
                   lookups' runs' ties · the sort's order · the state in front shows tl, F, funs ·
                   tl.heard = some g · FiveFront · what the sort's lemmas ask of the state in front
                   (LayAsks | AttAsks, the attention's own state and its third vector | HeadWants) ·
                   at attention and the head: that one equation · a yes of the batching block at x ⊢
                   FiveHeld tl g t'
Limits. IMPLICATIONS. PAID BY NOBODY HERE: FiveFront · the ties · LayAsks, AttAsks, HeadWants and
the two premises beside · the equation on the third vector's array. THE LEMMAS ON THE OTHER RUNS
STAND OVER FURTHER FILES, some of them other kinds' own: this file is no better than they; which of
them are rows of the library is for the library's own list to say. THE EQUATION IS NO WEAKER A
PREMISE THAN `LinkJoin.ApartAt`: with `apartB` and `piecesLaid`, which stand in PubAt, it yields it
(`apartAt_of_tests`, Johnson/P1K8R/ThirdTie.lean; not imported and not called here); it is a plainer
one: one equation on a public number. PAYERS, NOT CALLED HERE: which number the third vector's array
has, at every state that the chain's own blocks reach in front of a batching: `u2_at_batch`
(ThirdTie.lean) · LayAsks, AttAsks, HeadWants there: AsksAtWrap.lean beside this file. At one
challenge x. The rows are named by the plan's number of blocks. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.TiesAtLink
import Johnson.Desc.ProofFile.Honest.K8.FourAtSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest
open _root_.P1K8

/-- `fiveHeld_at_link`'s premises on the data and the ledger in front. -/
structure FiveFront (s : S) (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Prop where
  pub : PubAt tl g
  zR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0
  zB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0
  bits : BitsFront tl F
  bitsPub : BitsPub tl g
  list : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size
  colsZ : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz
  syms : SymbolsFront tl F
  laid : symbolsLaid tl = true
  rest : TiesRest tl

/-- A claim that names the third vector's array alone, where the arrays' numbers are apart. -/
theorem fourRows_of_third {tl : HTailF2} {n3 : Nat} {cl : Claim}
    (hU : tl.ix.U.getD 2 none = some n3) (hA : apartB tl = true) (h : OnlyArray n3 cl) :
    FourRows tl cl := by
  have e : (tl.ix.U.getD 2 none).getD 0 = n3 := by
    rw [hU]
    rfl
  exact fourRows_of_only hA (by rw [e]; exact h)

/-- **AT A LAYERS' SEGMENT.** -/
theorem fiveHeld_at_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = First.orderOf .layers) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FiveFront s tl F g)
    (hs : LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FiveHeld tl g t' := by
  refine fiveHeld_at_link L 4 layPre layPost (hord.trans lay_order)
    (lay_preOk L p4 nU ties tC tD) (lay_postOk L p4 nU ties) ties.tEq p batch s t' tl F funs hb
    ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.colsZ D.syms D.laid D.rest D.list
    (fun u => layKeep u = layKeep s) (fun u => layKeep u = layKeep s)
    ⟨fun o ho run hat m u u' c hu hr => ?_,
      fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu _ h0 _ h =>
        (layKeep_k8 u tl₀ tl₁ F₀ F₂ funs₀ k8 n h0 h).trans hu,
      fun o ho run hat m u u' c hu hr => ?_⟩ x (fun t h => layKeep_drawn p s t _ h) hbt
  · obtain ⟨q, k⟩ := lay_pre L p4 nU ties tC tD _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_only D.pub.apart (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := lay_post L p4 nU ties _ s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_only D.pub.apart (q cl hcl), k⟩

/-- **AT AN ATTENTION SEGMENT.** -/
theorem fiveHeld_at_att (L : Link S Claim) (A : Attention.Plan) (nU : Array Nat)
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
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FiveFront s tl F g)
    (hs : AttAsks s) (a : AttOwn) (ha : s.here = .att a)
    (hU : Att.P.U3At A (Att.P.plannedK A) a.F) (hU2 : tl.ix.U.getD 2 none = some A.iU3)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FiveHeld tl g t' := by
  refine fiveHeld_at_link L 4 attPre [] (by rw [hord]; rfl)
    (att_pre L (Att.P.parCOf A) nU ties tC tD tJ tP) (post_nil L) ties.tEq p batch s t' tl F funs
    hb ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.colsZ D.syms D.laid D.rest D.list
    (AttInv A s) (fun _ => True)
    ⟨fun o ho run hat m u u' c hu hr => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ ho => nomatch ho⟩ x
    (fun t h => ⟨attKeep_drawn p s t _ h, attLedger_drawn p s t _ h a ha hU⟩) hbt
  obtain ⟨q, k⟩ := att_pre_apart L A nU ties tC tD tJ tP s hs o ho run hat m u u' c hu hr
  exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩

/-- **AT THE HEAD's SEGMENT.** -/
theorem fiveHeld_at_head (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
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
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FiveFront s tl F g)
    (hs : HeadWants h iU3 p6 s) (hU2 : tl.ix.U.getD 2 none = some iU3)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FiveHeld tl g t' := by
  refine fiveHeld_at_link L 5 headPre headPost (by rw [hord]; rfl)
    (head_pre L h iU3 l piece p6 nU ties tC tD tP) (head_post L h iU3 l piece p6 nU ties)
    ties.tEq p batch s t' tl F funs hb ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.colsZ
    D.syms D.laid D.rest D.list (HeadInv s) (HeadInv s)
    ⟨fun o ho run hat m u u' c hu hr => ?_,
      fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 _ h3 =>
        head_k8_keeps s u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 h3,
      fun o ho run hat m u u' c hu hr => ?_⟩ x
    (fun t hd => ⟨headKeep_drawn p s t _ hd, laterS_drawn p s t _ hd⟩) hbt
  · obtain ⟨q, k⟩ := head_pre_apart L h iU3 l piece p6 nU ties tC tD tP s hs o ho run hat m u u'
      c hu hr
    exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := head_post_apart L h iU3 l piece p6 nU ties s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_third hU2 D.pub.apart (q cl hcl), k⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.fourRows_of_third
#print axioms ProofFile.Honest.K8.fiveHeld_at_layers
#print axioms ProofFile.Honest.K8.fiveHeld_at_att
#print axioms ProofFile.Honest.K8.fiveHeld_at_head
#print axioms ProofFile.Honest.K8.FiveFront
