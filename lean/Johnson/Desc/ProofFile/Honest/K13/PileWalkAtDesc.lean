-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileWalkAtDesc.lean: THE MEMBER OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN, AT THE IOP's OWN START: NINE OF THE TWELVE PREMISES ARE SHOWN, THREE ARE PREMISES.
Statements with their proofs.

PileWalkAtFlat.lean of this folder shows six of the twelve, at any start. Here three more, at start
:= `ProofFile.startS Z` at the public part of the instance: `reply`, `empty`, `atEnd`.
Under: In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the proof
file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the first
chain); and hp: every sub-protocol of the chain's list passes its own test on the plan.
Main names:
  `atEnd`: by `fold_notAtEnd` (ClearedBySort.lean of this folder: at every border up to 355 the
    fold's state does not stand at the chain's end) and the library's `rows_of_not_mem`
    (Johnson/Desc/First/Pile/PileMakers.lean: there `S.rows` is the field `out.pending`).
  `no_K7_behind`: by the kernel, at the library's written list of places: none of the places number
    347 to 354 is of the kind that hears the reply. `reply_at_flat`: **every decision of these
    numbers leaves the reply**: by the library's `ProofFile.chainBy_leaves`, `ProofFile.sameReply_eq`
    (Johnson/Desc/Plain/Leaves/PureHears.lean) at the opening's own chain (`IM.Open.chain`), and
    `IM.place_at` (Johnson/IMR/PlacesScope.lean).
  `empty`, and that the start does not stand at the chain's end: the library's `startS_facts`
    (Johnson/Desc/AtSeats/StatementSeat.lean).
  `pileWalk_at_desc`: **`PileWalk` at c.blocksInOrder, the IOP's own start, b := 355, `sitesAt c Z`, rd :=
    `S.rows`**, from three premises, each as `PileWalk` asks it: `sites` · `reach` · `stays`.
    `pileIs_at_desc`: **so `PileIs` there.**

What is not claimed. Any of the three premises; that they can be met together. pubOf: a free
parameter. That hp holds. Nothing at another border. It is none of the library's goals. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.PileWalkAtFlat
import Johnson.Desc.Plain.Leaves.PureHears
import Johnson.Desc.AtSeats.StatementSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs ClaimsIs SiteClaims MergeSite
  FoldReaches pileBySites pileIs_of_claimsIs)
open ProofFile (Cl Lot Ground)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open Meaning.K2
open LPFK9 (fold_ix)

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- None of the places number 347 to 354 is of the kind that hears the reply. -/
theorem no_K7_behind (k : Nat) (h1 : 346 < k) (h2 : k < 355) (a : Place)
    (ha : IM.placesW[k]? = some a) : a.kind ≠ KindName.K7 := by
  have hh : ((IM.placesW.drop 347).take 8).all (fun a => a.kind != KindName.K7) = true := by
    decide +kernel
  have hm : a ∈ (IM.placesW.drop 347).take 8 := by
    apply List.mem_of_getElem? (i := k - 347)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      show 347 + (k - 347) = k by omega]
    exact ha
  simpa using List.all_eq_true.1 hh a hm

/-- **Behind the head's merge, in front of K13's batching, every decision leaves the reply.** -/
theorem reply_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : Nat) (blk : Block S Cl)
    (h1 : 346 < k) (h2 : k < 355) (hb : c.blocksInOrder[k]? = some blk) (s t : S) (R : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s R gs = .ok t) :
    t.out.reply = s.out.reply := by
  have hpl : IM.placesW[k]? = some blk.place := IM.place_at hS hR O hb
  rcases ProofFile.chainBy_leaves (fun s : S => s.out.reply) Z base _ _ c O.chain
      (fun t s e => ProofFile.sameReply_eq t s e) blk (List.mem_of_getElem? hb) with h7 | hL
  · exact absurd h7 (no_K7_behind k h1 h2 _ hpl)
  · exact hL s R gs t hd

/-- **THE MEMBER OF `PileWalk`, AT THE IOP's OWN START**, where every sub-protocol of the chain
passes its test on the plan. pubOf: the public part of an instance: a free parameter. NINE OF THE
TWELVE ARE SHOWN; THREE ARE PREMISES. -/
theorem pileWalk_at_desc (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z, ClaimsIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) σ.j σ.m
      Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hstays : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.j < k → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileWalk c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n Z.p.X.layers.wsLay Z.first.lin
      (sitesAt c Z) claims asked S.rows := by
  have hst : ∀ x, NotAtEnd (ProofFile.startS Z (pubOf x)) := fun x a e => by
    rw [(startS_facts O.pub (pubOf x)).2.2] at e
    cases e
  refine pileWalk_at_flat hS hR O hp _ n claims asked hsites hreach hstays
    (fun k blk h1 h2 hb _ _ _ s _ _ R gs t hd => reply_at_flat hS hR O k blk h1 h2 hb s t R gs hd)
    (fun x => ?_) (fun x rs cols s r cl hf _ => ?_)
  · rw [rows_of_not_mem (hst x)]
    exact (startS_facts O.pub (pubOf x)).1
  · exact rows_of_not_mem
      (fold_notAtEnd hS hR O 355 (Nat.le_refl _) _ (hst x) rs cols (s, r, cl) hf)

/-- **So `PileIs` there.** -/
theorem pileIs_at_desc (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z, ClaimsIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) σ.j σ.m
      Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hstays : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.j < k → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n
      (pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims) asked :=
  pileIs_of_claimsIs (pileWalk_at_desc hS hR O hp pubOf n claims asked hsites hreach hstays)

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.no_K7_behind
#print axioms ProofFile.Honest.K13.reply_at_flat
#print axioms ProofFile.Honest.K13.pileWalk_at_desc
#print axioms ProofFile.Honest.K13.pileIs_at_desc
