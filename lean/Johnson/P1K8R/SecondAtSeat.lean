-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondAtSeat.lean: THE SMALLNESS TEST: AT THE SEATED BATCHING BLOCK OF EACH OF THE
THREE SORTS OF SEGMENT: `SecondEqs` (Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES OF
THE BLOCK's DECISION, FROM PREMISES ON THE STATE IN FRONT ALONE: UNDER THE SCOPE, THE FILES READ AND
IM.Open. Definitions and lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding. An assembly.

  `BehindEqs b s`, `FrontOwed s tl F funs`   `SecondEqs` behind the block's decision, at every field
      element at which it says yes; what the three sorts ask alike of the state in front: it holds
      data, a ledger and tables; `SecondFront` (Johnson/Desc/K8/Honest/SecondOpen.lean); Fo.CoefOK;
      the expected pieces' rows lie in the digits' array
  **`behind_seat_layers`**, **`behind_seat_att`**, **`behind_seat_head`**   `secondEqs_at_layers`,
      `secondEqs_at_att`, `secondEqs_at_head` (Johnson/P1K8R/SecondAtLayers.lean, SecondAtAtt.lean,
      SecondAtHead.lean) at the block that is seated at 14 l + 9, and at 14 * 24 + 11 for the head.
      The assembly's ties, the order and the batching's tie are premises no more; the letters of the
      sorts' own premises are tied to the built description
THE OPENINGS OF THE THREE PROOFS ARE THOSE OF `plain_seat_layers`, `plain_seat_att`,
`plain_seat_head` (Johnson/P1K8R/PlainAtSeat.lean), LETTER FOR LETTER BUT FOR ONE SIGN: that file's
`PlainSeat` keeps the ties behind an "exists".
TWO SEAMS FOR WHOEVER PAYS THE HEAD's PREMISES AT A REACHED STATE: `HeadWants` stands here at the
array 0 and at Kinds.Head.Law.workAtW; LinkJoin.k6HeardAt_347
(Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean) ends at Kinds.Head.Law.readsOf and at workOf. That
readsOf is 0 is `head_u3` (Johnson/P1K8R/FallAtSeatHead.lean); of workAtW and workOf
Johnson/LPFK9R/OwesAtLetters.lean says "one text under two names". Neither is joined here.
Limits. EVERY PREMISE ON THE STATE IS SHOWN OF NO STATE HERE. That the state is reached at that
border is not spoken of.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.SecondAtLayers
import Johnson.P1K8R.SecondAtAtt
import Johnson.P1K8R.SecondAtHead
import Johnson.P1K8R.PlainAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)

/-- `SecondEqs` behind the block's decision, at every field element at which it says yes. -/
def BehindEqs (b : Block S Claim) (s : S) : Prop :=
  ∀ x t, b.decide s [⟨[], chiAt x⟩] [] = .ok t →
    ∀ tl' G, tlForkP.get? t = some (tl', G) → SecondEqs tl' G

/-- What the three sorts ask alike of the state in front of a segment's batching. -/
structure FrontOwed (s : S) (tl : HTailF2) (F : Fork) (funs : Array HFun) : Prop where
  data : s.tl? = some tl
  ledger : s.fork? = some F
  tables : s.funs? = some funs
  second : SecondFront tl F
  coef : Fo.CoefOK tl F
  rows : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
    w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE SEATED BATCHING BLOCK OF A LAYERS' SEGMENT.** -/
theorem behind_seat_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par), c.blocksInOrder[14 * l + 9]? = some b ∧
      LPFK9.k4ParAt Z Bs.G₀ l = some p4 ∧
      ∀ (s : S) (tl : HTailF2) (F' : Fork) (funs : Array HFun), FrontOwed s tl F' funs →
        LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s → BehindEqs b s := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hordA hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', p4, X, e1', hp4, hX, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  rw [h7] at hflat
  refine ⟨_, p4, hflat, hp4, fun s tl F' funs hf hs x t hdec tl' G hq => ?_⟩
  exact secondEqs_at_layers Lk p4 _ ties tC tD hord p
    (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs []) s tl F' funs
    (fun rs t h0 => ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order))
      (by decide : KindName.K9 ≠ KindName.K7) s t rs []).1 h0).1)
    hf.data hf.ledger hf.tables hf.second hf.coef hf.rows hs x t tl' G hdec hq

/-- **AT THE SEATED BATCHING BLOCK OF AN ATTENTION SEGMENT.** -/
theorem behind_seat_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) :
    ∃ (b : Block S Claim) (Ap : Attention.Plan) (g : ℕ), c.blocksInOrder[14 * l + 9]? = some b ∧
      l = 2 * g + 1 ∧ Bs.G₀.W.A[g]? = some Ap ∧
      ∀ (s : S) (tl : HTailF2) (F' : Fork) (funs : Array HFun) (a : AttOwn),
        FrontOwed s tl F' funs → AttAsks s → s.here = .att a →
        Att.P.U3At Ap (Att.P.plannedK Ap) a.F → LinkJoin.ApartAt tl Ap.iU3 → BehindEqs b s := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hordA hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  rw [h7] at hflat
  refine ⟨_, Ap, g, hflat, rfl, hA, fun s tl F' funs a hf hs ha hU hAp x t hdec tl' G hq => ?_⟩
  exact secondEqs_at_att Lk Ap _ ties tC tD tJ tP hord p
    (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs []) s tl F' funs
    (fun rs t h0 => ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order))
      (by decide : KindName.K9 ≠ KindName.K7) s t rs []).1 h0).1)
    hf.data hf.ledger hf.tables hf.second hf.coef hf.rows hs a ha hU hAp x t tl' G hdec hq

/-- **AT THE SEATED BATCHING BLOCK OF THE HEAD's SEGMENT.** -/
theorem behind_seat_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b : Block S Claim, c.blocksInOrder[14 * 24 + 11]? = some b ∧
      ∀ (s : S) (tl : HTailF2) (F' : Fork) (funs : Array HFun), FrontOwed s tl F' funs →
        HeadWants Bs.G₀.W.hS 0
          (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s →
        LinkJoin.ApartAt tl 0 → BehindEqs b s := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord hordA hlen
  have h9 : Lk.hear.length = 9 := by
    rw [hlen]
    rfl
  have hU3 := head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  rw [h9] at hflat
  refine ⟨_, hflat, fun s tl F' funs hf hs hAp x t hdec tl' G hq => ?_⟩
  exact secondEqs_at_head Lk _ 0 _ 4 _ _ ties tC tD tP hord p
    (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs []) s tl F' funs
    (fun rs t h0 => ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order))
      (by decide : KindName.K9 ≠ KindName.K7) s t rs []).1 h0).1)
    hf.data hf.ledger hf.tables hf.second hf.coef hf.rows hs hAp x t tl' G hdec hq

end

end P1K8

#print axioms P1K8.behind_seat_layers
#print axioms P1K8.behind_seat_att
#print axioms P1K8.behind_seat_head
#print axioms P1K8.BehindEqs
#print axioms P1K8.FrontOwed
