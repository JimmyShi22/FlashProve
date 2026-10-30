-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FourAtSorts.lean: THE SMALLNESS TEST: `fourHeld_at_link`
(Johnson/Desc/K8/Honest/FourAtLink.lean: behind a yes of the batching block at a challenge x, four
of the verifier's tests on what the adding has left say yes) AT A SEGMENT OF EACH OF THE THREE
SORTS, WITH NO INVARIANT LEFT AS A LETTER. ITS PREMISE ON THE SEGMENT's OTHER RUNS (`RunsKeep`,
Johnson/Desc/K8/Honest/BothAtLink.lean) IS MOVED TO THE ONE STATE IN FRONT, NOT PAID: it is built
here from twelve lemmas of Johnson/P1K8R/LayersApart.lean (four), AttApart.lean (three) and
HeadApart.lean (five), UNDER WHAT THESE ASK OF THE STATE IN FRONT: each run keeps a named invariant
and makes claims that name one array alone, the third vector's; that array is another than the
digits' and the bits'. None of the library's goals.

  `FourFront s tl F g`   `fourHeld_at_link`'s eight premises on the data and the ledger in front, as
                   one structure: PubAt · the reads' row and the bits' three rows begin at column 0
                   · BitsFront · BitsPub · the link's list has a member for each array · the digits'
                   array has 2 mz columns and has the reads' row. A DRESS, NO PAYMENT
  `fourRows_of_names`   a claim that names nothing of the digits' array and nothing of the bits'
                   array ⊢ FourRows tl
  `fourRows_of_only`, `fourRows_of_apartAt`   a claim that names one array alone, which is apart
                   from these two (by the test `apartB`, at the third vector's array; by the
                   library's `LinkJoin.ApartAt`) ⊢ FourRows tl
  **`fourHeld_at_layers`**, **`fourHeld_at_att`**, **`fourHeld_at_head`**   the sort's ties · the
                   lookups' runs' ties · the sort's order · the state in front shows tl, F, funs ·
                   tl.heard = some g · FourFront · what the sort's lemmas ask of the state in front
                   (LayAsks | AttAsks, the attention's own state and its third vector | HeadWants) ·
                   at attention and the head: LinkJoin.ApartAt · a yes of the batching block at x ⊢
                   FourHeld tl g t'
Each follows the like theorem on the ties' second halves (`secondEqs_at_layers`, `secondEqs_at_att`,
`secondEqs_at_head`, Johnson/P1K8R/SecondAtLayers.lean, SecondAtAtt.lean, SecondAtHead.lean) in how
the premises are handed. The cut of a layers' segment's order is called (`layPre`, `layPost`,
`lay_order`, `lay_preOk`, `lay_postOk`, Johnson/Desc/K8/Honest/LayersCut.lean).
Limits. IMPLICATIONS. PAID BY NOBODY HERE: FourFront · the ties · LayAsks, AttAsks, HeadWants and
the two premises beside · ApartAt. PAYERS, NOT CALLED HERE: LayAsks, AttAsks, HeadWants at every
state reached in front of a batching: AsksAtWrap.lean beside this file. THE LEMMAS ON THE OTHER RUNS
STAND OVER FURTHER FILES, some of them other kinds' own: this file is no better than they; which of
them are rows of the library is for the library's own list to say. At one challenge x. The reads'
row is named by the plan's number of blocks. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.FourAtLink
import Johnson.P1K8R.SecondAtLayers
import Johnson.P1K8R.SecondAtAtt
import Johnson.P1K8R.SecondAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest
open _root_.P1K8

/-- `fourHeld_at_link`'s premises on the data and the ledger in front. -/
structure FourFront (s : S) (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Prop where
  pub : PubAt tl g
  zR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0
  zB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0
  bits : BitsFront tl F
  bitsPub : BitsPub tl g
  list : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size
  colsZ : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz
  rowZ : tl.zzRowReads < (F.trees.getD tl.ix.ZZ {}).rows.size

/-- A claim that names nothing of the digits' array and nothing of the bits' array. -/
theorem fourRows_of_names {tl : HTailF2} {cl : Claim} (hZ : NamesNot tl.ix.ZZ cl)
    (hB : NamesNot tl.ix.BZ cl) : FourRows tl cl :=
  ⟨namesNot_at hZ _, fun e _ => namesNot_at hB e⟩

/-- A claim that names the third vector's array alone, where the arrays' numbers are apart. -/
theorem fourRows_of_only {tl : HTailF2} {cl : Claim} (hA : apartB tl = true)
    (h : OnlyArray ((tl.ix.U.getD 2 none).getD 0) cl) : FourRows tl cl := by
  obtain ⟨-, -, ⟨uZ, uB⟩, -⟩ := (apartB_iff tl).1 hA
  exact fourRows_of_names (h _ fun e => uZ e.symm) (h _ fun e => uB e.symm)

/-- A claim that names array n3 alone, where n3 is apart at the data. -/
theorem fourRows_of_apartAt {tl : HTailF2} {n3 : Nat} {cl : Claim}
    (hA : LinkJoin.ApartAt tl n3) (h : OnlyArray n3 cl) : FourRows tl cl := by
  obtain ⟨_, _, _, hZ, hB, _, _⟩ := hA
  exact fourRows_of_names (h _ hZ) (h _ hB)

/-- **AT A LAYERS' SEGMENT.** -/
theorem fourHeld_at_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = First.orderOf .layers) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FourFront s tl F g)
    (hs : LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FourHeld tl g t' := by
  refine fourHeld_at_link L 4 layPre layPost (hord.trans lay_order)
    (lay_preOk L p4 nU ties tC tD) (lay_postOk L p4 nU ties) ties.tEq p batch s t' tl F funs hb
    ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.list D.colsZ D.rowZ
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
theorem fourHeld_at_att (L : Link S Claim) (A : Attention.Plan) (nU : Array Nat)
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
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FourFront s tl F g)
    (hs : AttAsks s) (a : AttOwn) (ha : s.here = .att a)
    (hU : Att.P.U3At A (Att.P.plannedK A) a.F) (hAp : LinkJoin.ApartAt tl A.iU3)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FourHeld tl g t' := by
  refine fourHeld_at_link L 4 attPre [] (by rw [hord]; rfl)
    (att_pre L (Att.P.parCOf A) nU ties tC tD tJ tP) (post_nil L) ties.tEq p batch s t' tl F funs
    hb ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.list D.colsZ D.rowZ
    (AttInv A s) (fun _ => True)
    ⟨fun o ho run hat m u u' c hu hr => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ ho => nomatch ho⟩ x
    (fun t h => ⟨attKeep_drawn p s t _ h, attLedger_drawn p s t _ h a ha hU⟩) hbt
  obtain ⟨q, k⟩ := att_pre_apart L A nU ties tC tD tJ tP s hs o ho run hat m u u' c hu hr
  exact ⟨fun cl hcl => fourRows_of_apartAt hAp (q cl hcl), k⟩

/-- **AT THE HEAD's SEGMENT.** -/
theorem fourHeld_at_head (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
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
    (g : Forest.Heard) (hg : tl.heard = some g) (D : FourFront s tl F g)
    (hs : HeadWants h iU3 p6 s) (hAp : LinkJoin.ApartAt tl iU3)
    (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') : FourHeld tl g t' := by
  refine fourHeld_at_link L 5 headPre headPost (by rw [hord]; rfl)
    (head_pre L h iU3 l piece p6 nU ties tC tD tP) (head_post L h iU3 l piece p6 nU ties)
    ties.tEq p batch s t' tl F funs hb ht hF hf g hg D.pub D.zR D.zB D.bits D.bitsPub D.list
    D.colsZ D.rowZ (HeadInv s) (HeadInv s)
    ⟨fun o ho run hat m u u' c hu hr => ?_,
      fun u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 _ h3 =>
        head_k8_keeps s u tl₀ tl₁ F₀ F₂ funs₀ k8 n hu h1 h2 h3,
      fun o ho run hat m u u' c hu hr => ?_⟩ x
    (fun t hd => ⟨headKeep_drawn p s t _ hd, laterS_drawn p s t _ hd⟩) hbt
  · obtain ⟨q, k⟩ := head_pre_apart L h iU3 l piece p6 nU ties tC tD tP s hs o ho run hat m u u'
      c hu hr
    exact ⟨fun cl hcl => fourRows_of_apartAt hAp (q cl hcl), k⟩
  · obtain ⟨q, k⟩ := head_post_apart L h iU3 l piece p6 nU ties s hs o ho run hat m u u' c hu hr
    exact ⟨fun cl hcl => fourRows_of_apartAt hAp (q cl hcl), k⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.fourRows_of_names
#print axioms ProofFile.Honest.K8.fourRows_of_only
#print axioms ProofFile.Honest.K8.fourRows_of_apartAt
#print axioms ProofFile.Honest.K8.fourHeld_at_layers
#print axioms ProofFile.Honest.K8.fourHeld_at_att
#print axioms ProofFile.Honest.K8.fourHeld_at_head
#print axioms ProofFile.Honest.K8.FourFront
