-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFill.lean: CONDITIONAL: WHICH PROVER's SIDE STANDS AT
WHICH PLACE OF THE FIRST CHAIN IN THE PROVER THAT onlineProverFromPublicFiles (Honest/AtPure.lean) RETURNS AT THE FILLING
OF RECORD widerFillAt (Honest/AtPureWiderAt.lean): THE GENERAL PART. That filling has ten lists of
sides; that each list's sides stand at places of one kind, ten kinds in all, is the premise
WiderKinds. Two definitions, eight statements with their proofs. It is
atPure_first_find_pairs (Honest/FirstFindPairs.lean) at these ten lists, as now_first_find
(Honest/FirstFindSixKinds.lean) is at another filling's six.

  widerPairs        A DEFINITION: the filling's ten lists, in its order, each with its kind
  widerFillAt_lots  the filling's field lots is that list's first column: by unfolding
  WiderKinds        A DEFINITION: A PREMISE's FORM: nine fields, one a list: every side of the list
                    is at a place of the list's kind; each at the one reader of the index that the
                    filling lays at the public part. (The tenth list's, the next token's, is
                    replyLot_kind, Honest/FirstFindKind.lean.)
  WiderKinds.all    the nine fields and replyLot_kind, as one sentence over widerPairs
  widerPairs_nodup  no kind is listed twice
  wider_first_find  CONDITIONAL: **at a place of a list's kind, what is found among the first
                    chain's sides of the prover is what is found in that list**
  wider_kind_of     CONDITIONAL: every side of the first chain is at a place of one of the ten kinds
  wider_first_none  CONDITIONAL: **at a place of none of the ten kinds nothing is found**: so at
                    every place of the kinds "frame", K9, K10 and K12
  wider_first_none_in   CONDITIONAL: at a place of a list's kind at which that list holds nothing,
                    nothing is found
  wider_no_frame    CONDITIONAL: **no side of the first chain is at a place of the kind "frame"**

The premises. h: onlineProverFromPublicFiles returns A at the filling · K: WiderKinds at A's public part and ground · in
wider_first_find: q is one of the ten pairs; the place is of its kind; hg: what that list's own
sides hold at the place.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. THAT onlineProverFromPublicFiles RETURNS AT ANY FILES IS A HYPOTHESIS. WiderKinds IS SHOWN OF
NOTHING HERE: each field is a lemma on one kind's list, for that list's authors or whoever reads its
text: this file imports the filling and the general lemma alone; what of the nine is shown stands in
Honest/Thread/FirstFillKinds.lean. The kind that widerPairs writes beside a list is a label: only
the next token's is held by a lemma here; a wrong label would make its field false and the
statements idle.
hg IS FOR THE CALLER: which side a list holds at a place is not said here. The statements are about
lists and places. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.FirstFindPairs
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)

variable {W₀ : Type}

/-- **The filling's ten lists, in its order, each with its kind.** It is a definition: nothing is
claimed of it. -/
def widerPairs (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName) :=
  [(HLot.byPub I.weights (LongLots.plain o S O).k1, .K1),
    (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩, .K2),
    (replyLot, .K7),
    (HLot.byPub I.weights (LongLots.plain o S O).k11, .K11),
    (HLot.byPub I.weights (LongLots.plain o S O).k13, .K13),
    (HLot.byPub I.weights (LongLots.plain o S O).k3, .K3),
    (HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt, .K4),
    (K5.k5LotK id O.keyOf, .K5),
    (HLot.byPub I.weights (LongLots.plain o S O).k6, .K6),
    (K8.smallLot id fun _ G _ l => K3.matsOwn G.W l, .K8)]

/-- The filling's lists are the pairs' first column. -/
theorem widerFillAt_lots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : (widerFillAt I o S O).lots = (widerPairs I o S O).map (·.1) := rfl

/-- **EVERY SIDE OF EACH LIST IS AT A PLACE OF THE LIST's KIND**: nine fields, each at the reader of
the index that the filling lays at the public part Z. It is a definition: a premise's form. Nothing
is claimed of it. -/
structure WiderKinds (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) : Prop where
  k1 : ∀ x ∈ (K1.dataSideNo S (fun w : Local W₀ IndexCommitterCoins Inst Cells =>
      ⟨w.x, ⟨w.trace, I.weights Z w.w₀, w.rc⟩⟩) o :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K1
  k2 : ∀ x ∈ (K2.switchLot (widerRows S Z G) (fun w : Local W₀ IndexCommitterCoins Inst Cells =>
      ⟨w.trace, I.weights Z w.w₀, w.rc⟩) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K2
  k11 : ∀ x ∈ (K11.headMergeLot O.claims (I.weights Z) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K11
  k13 : ∀ x ∈ (K13.k13Lot (I.weights Z) O.pile :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K13
  k3 : ∀ x ∈ (K3.theLotInst id (I.weights Z) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K3
  k4 : ∀ x ∈ (K4.k4HLot id (I.weights Z) (fun _ _ => K4.k4LookAt) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K4
  k5 : ∀ x ∈ (K5.k5LotK id O.keyOf :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K5
  k6 : ∀ x ∈ (K6.headLot K6.headFitsB (K6.headWit' id (I.weights Z)) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K6
  k8 : ∀ x ∈ (K8.smallLot id (fun _ G _ l => K3.matsOwn G.W l) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G,
    x.place.kind = .K8

variable {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

/-- The nine fields and the next token's lemma, as one sentence over the ten pairs. -/
theorem WiderKinds.all {Z : Pub} {G : Ground} (K : WiderKinds I o S O Z G) :
    ∀ r ∈ widerPairs I o S O, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := by
  intro r hr
  simp only [widerPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.k1
  · exact K.k2
  · exact replyLot_kind Z G
  · exact K.k11
  · exact K.k13
  · exact K.k3
  · exact K.k4
  · exact K.k5
  · exact K.k6
  · exact K.k8

/-- No kind is listed twice. -/
theorem widerPairs_nodup : ((widerPairs I o S O).map (·.2)).Nodup := by
  have hn :
      ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName).Nodup := by
    decide
  exact hn

variable {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **AT A PLACE OF A LIST's KIND, WHAT IS FOUND AMONG THE FIRST CHAIN's SIDES IS WHAT IS FOUND IN
THAT LIST.** CONDITIONAL: onlineProverFromPublicFiles returns A at the filling; WiderKinds at A's public part and ground;
q is one of the ten pairs; the place is of its kind; hg: what the list's own sides hold there. -/
theorem wider_first_find (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName}
    (hq : q ∈ widerPairs I o S O) {p : Place} (hp : p.kind = q.2)
    {g : Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g :=
  atPure_first_find_pairs h (widerFillAt_lots I o S O) K.all widerPairs_nodup hq hp hg

/-- **Every side of the first chain is at a place of one of the ten kinds.** CONDITIONAL: onlineProverFromPublicFiles
returns A at the filling; WiderKinds at A's public part and ground. -/
theorem wider_kind_of (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) :
    ∀ g ∈ A.H.first, g.place.kind ∈
      ([.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) := by
  intro g hg
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, widerFillAt_lots] at hg
  obtain ⟨L, hL, hx⟩ := List.mem_flatMap.1 hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  rw [K.all r hr g hx]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

/-- **AT A PLACE OF NONE OF THE TEN KINDS NOTHING IS FOUND.** CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling; WiderKinds at A's public part and ground; the place's kind is none of the ten. -/
theorem wider_first_none (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) {p : Place}
    (hp : p.kind ∉ ([.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName)) :
    A.H.first.find? (fun x => x.place == p) = none :=
  find_none_of_places fun x hx e => hp (e ▸ wider_kind_of h K x hx)

/-- **At a place of a list's kind at which that list holds nothing, nothing is found.** CONDITIONAL:
onlineProverFromPublicFiles returns A at the filling; WiderKinds at A's public part and ground; q is one of the ten
pairs; the place is of its kind; hg: the list's own sides hold nothing there. -/
theorem wider_first_none_in (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName}
    (hq : q ∈ widerPairs I o S O) {p : Place} (hp : p.kind = q.2)
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = none) :
    A.H.first.find? (fun x => x.place == p) = none := by
  refine find_none_of_places fun x hx e => ?_
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, widerFillAt_lots] at hx
  obtain ⟨L, hL, hxL⟩ := List.mem_flatMap.1 hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  have hk : r.2 = q.2 := by rw [← K.all r hr x hxL, e, hp]
  obtain rfl : r = q := List.inj_on_of_nodup_map widerPairs_nodup hr hq hk
  exact List.find?_eq_none.1 hg x hxL (beq_iff_eq.2 e)

/-- **NO SIDE OF THE FIRST CHAIN IS AT A PLACE OF THE KIND "frame".** CONDITIONAL: onlineProverFromPublicFiles returns A
at the filling; WiderKinds at A's public part and ground. -/
theorem wider_no_frame (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) : ∀ g ∈ A.H.first, g.place.kind ≠ .frame := by
  intro g hg e
  have hm := wider_kind_of h K g hg
  rw [e] at hm
  exact absurd hm (by decide)

end ProofFile.Honest

#print axioms ProofFile.Honest.widerFillAt_lots
#print axioms ProofFile.Honest.WiderKinds.all
#print axioms ProofFile.Honest.widerPairs_nodup
#print axioms ProofFile.Honest.wider_first_find
#print axioms ProofFile.Honest.wider_kind_of
#print axioms ProofFile.Honest.wider_first_none
#print axioms ProofFile.Honest.wider_first_none_in
#print axioms ProofFile.Honest.wider_no_frame
