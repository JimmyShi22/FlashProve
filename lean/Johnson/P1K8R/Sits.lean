-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/Sits.lean: THE HARD ROW K08_sits, AT THE PROOF FILE: A JOINING.

THE ROW: in the written description of the proof file the entry of the description's list of blocks
at each place of the kind K8 is the constant of which the kind's law speaks, at the plan's numbers,
under the seat's wrappers alone, or its yes gives that law's premise.
WHERE IS WHAT. That the block at the place is `seatedAs sameReply (K8.whole (k8ParW Z G₀ Xl l)) …`
(`LaidAlone`), at all 25 links of the value of `onlineDescription` in the goals' scope: THE INTEGER-MODEL
FILES' seats (Johnson/IMR: `k8_of_layers`, `k8_of_attention`, `k8_of_head`; `seat_open`;
`step_alone` and the fields; FlatIx.lean, FlatScope.lean: the
number in the flat list): CALLED. HERE: that this term is the term of K8's first half's laws:
  `whole_like`: `K8.whole p` has the rounds, decision, field `before` and test on the plan of
    `approximateRangeProofDrawKind atS p.toPar`.
  `means_out`: the draw leaves what was put out.
  `alone_step`: **THE HEAD LAW AT THE SEATED BLOCK**: its step says yes just where there is one
    round that passes the frame's test, `MeansAtS p.toPar` holds, no column is taken, and the record
    in front bears no mark. THE REPLY'S GUARD NEVER BITES AT THIS KIND: the draw leaves the reply.
  `alone_seats`: a yes of the seated block is a yes of the draw's block with the same record and no
    mark behind it, both ways (`Seats`, Johnson/Desc/First/K8/LawSeated.lean): so every law of
    ours under `Seats`, and along `Block.Under`, holds of it.
    NO WORD OF A REFUSAL IS SPELLED.
  `alone_likeP`: it has `LikeP` (Johnson/Desc/First/K8/LawSeatedPlan.lean): so the laws at the plan.
  `SitsAt Z G₀ c l i`: all of this of the block at link l, number i among the link's blocks in front
    of the batching, WHICH IS THE ENTRY NUMBER 14 l + i + 2 OF THE CHAIN'S FLAT LIST.
  `k08_sits`: **THE ROW**: in scope, from the value of `onlineDescription`: `SitsAt` at every layers' link
    and attention link (i = 4) and at the head's (i = 5). That the numbers ks and tau of `k8Par` are
    the public part's own plans' is said by Johnson/IMR/K8Seat.lean's three: not said again here.
Limits. THAT `onlineDescription` RETURNS IN SCOPE IS A PREMISE. The full size's 25 links. ms, asks, matsIn,
readsIn and nU are `k8ParW`'s own terms: not tied to the plans here. Nothing on the second half's
runs (`claims`, `after`), which the seat guards too. THE PIECE of the table of joints is not in it.
The laws' own premises stay. Nothing on soundness.

-/
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.First.K8.LawSeatedPlan
import Johnson.Desc.First.K8.LawLeaves

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn roundsFit seatSame)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

/-- The kind, whole, has the first half's rounds, decision, field `before` and test on the plan. -/
theorem whole_like (p : ParW) : Like atS p.toPar (whole p) := ⟨rfl, rfl, rfl, rfl⟩

/-- The draw leaves what was put out. -/
theorem means_out (p : Par) (st st' : S) (r : Fmt.RoundView) (h : MeansAtS p st r st') :
    st'.out = st.out := by
  obtain ⟨tl, _, _, _, _, _, _, _, _, _, e⟩ := h
  rw [e]
  exact (putTl_rest st _).2.2.2.2.2.2.1

section
variable {b : Block S Cl} {p : ParW} {name : String} {l i : ℕ}
  (h : IM.LaidAlone ProofFile.sameReply b (whole p) name
    { chain := 1, link := some l, piece := i, kind := .K8 })

include h in
/-- **The head law at the seated block.** -/
theorem alone_step (ft : Nat) (st st' : S) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    b.step ft st rs cols = .ok (st', k) ↔
      ∃ r, rs = [r] ∧ roundsFit [round p.toPar] [r] = true ∧ MeansAtS p.toPar st r st' ∧ k = 0 ∧
        st.failed = none := by
  rw [IM.step_alone h (fun e => nomatch e), step_like (whole_like p), step_atS_iff]
  constructor
  · rintro ⟨⟨r, e, hf, hm, hn⟩, hk, _⟩
    exact ⟨r, e, hf, hm, hn, (hear_mark p.toPar st st' r hm) ▸ hk⟩
  · rintro ⟨r, e, hf, hm, hn, hk⟩
    refine ⟨⟨r, e, hf, hm, hn⟩, (hear_mark p.toPar st st' r hm).trans hk, ?_⟩
    unfold ProofFile.sameReply
    rw [means_out p.toPar st st' r hm]
    exact beq_self_eq_true _

include h in
/-- **A yes of the seated block is a yes of the draw's block, with the same record and no mark
behind it: both ways.** No word of a refusal is spelled. -/
theorem alone_seats : Seats b (approximateRangeProofDrawKind atS p.toPar) := by
  have er : b.rounds = (whole p).rounds := IM.alone_rounds h
  refine ⟨er, fun s rs gs t => ?_⟩
  rw [IM.yes_alone h (fun e => nomatch e)]
  constructor
  · rintro ⟨a, c, _⟩
    exact ⟨a, c⟩
  · rintro ⟨a, c⟩
    refine ⟨a, c, ?_⟩
    have hr : t.out.reply = s.out.reply := hear_leaves_reply p.toPar s rs gs t a
    unfold ProofFile.sameReply
    rw [hr]
    exact beq_self_eq_true _

include h in
theorem alone_likeP : LikeP atS p.toPar b := by
  have e1 : b.rounds = (whole p).rounds := IM.alone_rounds h
  have e2 : b.before = (whole p).before := IM.alone_before h
  have e3 : b.planOk = (whole p).planOk := IM.alone_planOk h
  exact ⟨e1, e2, e3⟩

end

/-- The law's numbers are the lot's. -/
theorem toPar_eq (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : ℕ) :
    (ProofFile.k8ParW Z G X l).toPar = ProofFile.k8Par Z G X l := rfl

/-- All of it, of the block at link l, number i among the link's blocks in front of the batching. -/
def SitsAt (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (l i : ℕ) : Prop :=
  ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH),
    c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧ c.blocksInOrder[14 * l + i + 2]? = some b ∧
    G₀.built[l]? = some Xl ∧
    IM.LaidAlone ProofFile.sameReply b (whole (ProofFile.k8ParW Z G₀ Xl l)) b.name
      { chain := 1, link := some l, piece := i + 1, kind := .K8 } ∧
    Seats b (approximateRangeProofDrawKind atS (ProofFile.k8ParW Z G₀ Xl l).toPar) ∧ LikeP atS (ProofFile.k8ParW Z G₀ Xl l).toPar b ∧
    ∀ (ft : Nat) (st st' : S) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      b.step ft st rs cols = .ok (st', k) ↔
        ∃ r, rs = [r] ∧ roundsFit [round (ProofFile.k8ParW Z G₀ Xl l).toPar] [r] = true ∧
          MeansAtS (ProofFile.k8ParW Z G₀ Xl l).toPar st r st' ∧ k = 0 ∧ st.failed = none

theorem sitsAt_of_alone {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl} {l i : ℕ}
    {Lk : Link S Cl} {b : Block S Cl} {Xl : LinkH} (e1 : c.links[l]? = some Lk)
    (e2 : Lk.hear[i]? = some b) (ef : IM.flatIx c l i = 14 * l + i + 2)
    (e3 : G₀.built[l]? = some Xl)
    (h : IM.LaidAlone ProofFile.sameReply b (whole (ProofFile.k8ParW Z G₀ Xl l)) b.name
      { chain := 1, link := some l, piece := i + 1, kind := .K8 }) : SitsAt Z G₀ c l i :=
  ⟨Lk, b, Xl, e1, e2, ef ▸ IM.hear_at_flat e1 e2, e3, h, alone_seats h, alone_likeP h,
    alone_step h⟩

/-- **THE ROW K08_sits, at the proof file.** -/
theorem k08_sits {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      (∀ g < 12, SitsAt Z G₀ c (2 * g) 4) ∧ (∀ g < 12, SitsAt Z G₀ c (2 * g + 1) 4) ∧
      SitsAt Z G₀ c 24 5 := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.desc, fun g hg => ?_,
    fun g hg => ?_, ?_⟩
  · obtain ⟨Lk, b, Xl, _, e1, e2, e3, h, _⟩ := IM.k8_of_layers hS hR O g hg
    exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 4) e3 h
  · obtain ⟨Lk, b, Xl, _, e1, e2, e3, h, _⟩ := IM.k8_of_attention hS hR O g hg
    exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 4) e3 h
  · obtain ⟨Lk, b, Xl, e1, e2, e3, h, _⟩ := IM.k8_of_head hS hR O
    exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 5) e3 h

end P1K8S

#print axioms P1K8S.alone_step
#print axioms P1K8S.alone_seats
#print axioms P1K8S.alone_likeP
#print axioms P1K8S.k08_sits
