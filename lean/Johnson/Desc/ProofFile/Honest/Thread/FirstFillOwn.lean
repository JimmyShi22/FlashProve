-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillOwn.lean: CONDITIONAL: WHICH SIDE STANDS AT A PLACE IN
THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING widerFillOwn own₀ L … (Honest/AtPureWiderAt.lean):
GENERAL IN THE SIDES' OWN STATE X, IN ITS START own₀ AND IN THE FIVE LISTS L THAT THE FILLING TAKES
AS A LETTER. Of a side the statements read its place alone. Two definitions; eleven statements with
their proofs.

  ownPairs            the filling's ten lists, in its order, each with its kind: five through L,
                      five written out. A SECOND TEXT of widerPairs (Honest/Thread/FirstFill.lean),
                      at a letter where that has LongLots.plain: HELD TO IT BY widerPairs_is, by rfl
  widerFillOwn_lots   the filling's lists are the pairs' first halves: by rfl
  LongKinds           a premise's form: every side of each of L's five lists stands at a place of
                      the list's kind: five clauses
  LongKinds.all       CONDITIONAL: so does every side of each of the ten
  ownPairs_nodup      no kind comes twice among the ten
  longKinds_plain     LongKinds at LongLots.plain, at every X: no premise
  own_others_apart    CONDITIONAL: no side of another of the ten lists stands at a place of this
                      list's kind
  own_first_find · own_first_none_in   CONDITIONAL: at a place of a list's kind the prover's first
                      chain has what that list has there: a side; none
  own_kind_of · own_first_none · own_no_frame   CONDITIONAL: every side of the first chain stands at
                      a place of one of the ten kinds; at a place of another kind there is none;
                      none stands at a place of the kind "frame"

The premises. h: onlineProverFromPublicFiles returns A at the filling · K: LongKinds at A's public part and ground. K IS
PROVED HERE AT LongLots.plain ALONE. At another L it asks one lemma of each of five lists' authors.

Called, of other authors: atPure_first_find_pairs (Honest/FirstFindPairs.lean), atPure_ok
(Honest/AtPureLaw.lean), find_none_of_places (Honest/FirstFind.lean), replyLot_kind
(Honest/FirstFindKind.lean), K3.Law.rowLotAt_kind (Honest/K3/Law/LotKind.lean), K4.k4HLot_kind
(Honest/K4/Law/LotKind.lean), K6.headLot_kind (Honest/K6/LotKind.lean), K13.k13Lot_kind
(Honest/K13/LotKind.lean). Of this file's authors: k1_kind, k2_kind, k8_kind, k11_kind
(Honest/Thread/FirstFillKinds.lean), K5.k5LotK_kind (Honest/K5/Law/LotKind.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That onlineProverFromPublicFiles returns at any filling is not proved here. What a side does is not
said. That a sub-protocol stands at a place is not said. The first chain alone. No property of a
prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillKinds
import Johnson.Desc.ProofFile.Honest.K6.LotKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ X : Type}

/-! ## 1 The ten lists, at a letter for five of them -/

/-- **The filling's ten lists, in its order, each with its kind.** It is a definition: nothing is
claimed of it. -/
def ownPairs (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName) :=
  [(HLot.byPub I.weights L.k1, .K1),
    (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩, .K2),
    (replyLot, .K7),
    (HLot.byPub I.weights L.k11, .K11),
    (HLot.byPub I.weights L.k13, .K13),
    (HLot.byPub I.weights L.k3, .K3),
    (HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt, .K4),
    (K5.k5LotK id O.keyOf, .K5),
    (HLot.byPub I.weights L.k6, .K6),
    (K8.smallLot id fun _ G _ l => K3.matsOwn G.W l, .K8)]

/-- The filling's lists are the pairs' first halves. -/
theorem widerFillOwn_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwn own₀ L I o S O).lots = (ownPairs L I S O).map (·.1) := rfl

/-- The elder text is this one at the plain lists. -/
theorem widerPairs_is (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    widerPairs I o S O = ownPairs (LongLots.plain o S O) I S O := rfl

/-- **Every side of each of L's five lists stands at a place of the list's kind.** It is a
definition: a premise's form. -/
structure LongKinds (L : LongLots W₀ X) (I : WiderIn W₀) (Z : Pub) (G : Ground) : Prop where
  k1 : ∀ x ∈ (L.k1 (I.weights Z)).halves Z G, x.place.kind = .K1
  k3 : ∀ x ∈ (L.k3 (I.weights Z)).halves Z G, x.place.kind = .K3
  k6 : ∀ x ∈ (L.k6 (I.weights Z)).halves Z G, x.place.kind = .K6
  k11 : ∀ x ∈ (L.k11 (I.weights Z)).halves Z G, x.place.kind = .K11
  k13 : ∀ x ∈ (L.k13 (I.weights Z)).halves Z G, x.place.kind = .K13

variable {L : LongLots W₀ X} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

/-- **So does every side of each of the ten.** CONDITIONAL: K. -/
theorem LongKinds.all {Z : Pub} {G : Ground} (K : LongKinds L I Z G) :
    ∀ r ∈ ownPairs L I S O, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := by
  intro r hr
  simp only [ownPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.k1
  · exact k2_kind (widerRows S Z G)
      (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) Z G
  · exact replyLot_kind Z G
  · exact K.k11
  · exact K.k13
  · exact K.k3
  · exact K4.k4HLot_kind id (I.weights Z) (fun _ _ => K4.k4LookAt) Z G
  · exact K5.k5LotK_kind id O.keyOf Z G
  · exact K.k6
  · exact k8_kind id (fun _ G _ l => K3.matsOwn G.W l) Z G

/-- No kind comes twice among the ten. -/
theorem ownPairs_nodup : ((ownPairs L I S O).map (·.2)).Nodup := by
  have hn :
      ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName).Nodup := by
    decide
  exact hn

/-- **At the plain lists the form holds, at every own state.** No premise. -/
theorem longKinds_plain (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) : LongKinds (X := X) (LongLots.plain o S O) I Z G :=
  { k1 := k1_kind _ _ _ Z G
    k3 := K3.Law.rowLotAt_kind _ Z G
    k6 := K6.headLot_kind _ _ Z G
    k11 := k11_kind _ _ Z G
    k13 := K13.k13Lot_kind _ _ Z G }

/-- **No side of another of the ten lists stands at a place of this list's kind.** CONDITIONAL: K;
r is one of the ten pairs; its kind is not k. -/
theorem own_others_apart {Z : Pub} {G : Ground} (K : LongKinds L I Z G)
    {r : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName}
    (hr : r ∈ ownPairs L I S O) {k : KindName} (hne : r.2 ≠ k) :
    ∀ x ∈ r.1.halves Z G, x.place.kind ≠ k :=
  fun x hx e => hne ((K.all r hr x hx).symm.trans e)

/-! ## 2 At the prover that onlineProverFromPublicFiles returns -/

variable {own₀ : X} {o o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}

/-- **At a place of a list's kind the first chain has the side that the list has there.**
CONDITIONAL: h; K; q is one of the ten pairs; p is of its kind; the list has g at p. -/
theorem own_first_find (h : onlineProverFromPublicFiles o' pol lay KL (widerFillOwn own₀ L I o S O) = .ok A)
    (K : LongKinds L I A.Z A.G)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName}
    (hq : q ∈ ownPairs L I S O) {p : Place} (hp : p.kind = q.2)
    {g : Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X}
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g :=
  atPure_first_find_pairs h (widerFillOwn_lots own₀ L I o S O) K.all ownPairs_nodup hq hp hg

/-- **Every side of the first chain stands at a place of one of the ten kinds.** CONDITIONAL: h; K.
-/
theorem own_kind_of (h : onlineProverFromPublicFiles o' pol lay KL (widerFillOwn own₀ L I o S O) = .ok A)
    (K : LongKinds L I A.Z A.G) :
    ∀ g ∈ A.H.first, g.place.kind ∈
      ([.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) := by
  intro g hg
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, widerFillOwn_lots] at hg
  obtain ⟨M, hM, hx⟩ := List.mem_flatMap.1 hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [K.all r hr g hx]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

/-- At a place of another kind the first chain has no side. CONDITIONAL: h; K; hp. -/
theorem own_first_none (h : onlineProverFromPublicFiles o' pol lay KL (widerFillOwn own₀ L I o S O) = .ok A)
    (K : LongKinds L I A.Z A.G) {p : Place}
    (hp : p.kind ∉ ([.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName)) :
    A.H.first.find? (fun x => x.place == p) = none :=
  find_none_of_places fun x hx e => hp (e ▸ own_kind_of h K x hx)

/-- **Where the list of a place's kind has no side there, the first chain has none.** CONDITIONAL:
h; K; q is one of the ten pairs; p is of its kind; the list has nothing at p. -/
theorem own_first_none_in (h : onlineProverFromPublicFiles o' pol lay KL (widerFillOwn own₀ L I o S O) = .ok A)
    (K : LongKinds L I A.Z A.G)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName}
    (hq : q ∈ ownPairs L I S O) {p : Place} (hp : p.kind = q.2)
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = none) :
    A.H.first.find? (fun x => x.place == p) = none := by
  refine find_none_of_places fun x hx e => ?_
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, widerFillOwn_lots] at hx
  obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  have hk : r.2 = q.2 := by rw [← K.all r hr x hxM, e, hp]
  obtain rfl : r = q := List.inj_on_of_nodup_map ownPairs_nodup hr hq hk
  exact List.find?_eq_none.1 hg x hxM (beq_iff_eq.2 e)

/-- No side of the first chain stands at a place of the kind "frame". CONDITIONAL: h; K. -/
theorem own_no_frame (h : onlineProverFromPublicFiles o' pol lay KL (widerFillOwn own₀ L I o S O) = .ok A)
    (K : LongKinds L I A.Z A.G) : ∀ g ∈ A.H.first, g.place.kind ≠ .frame := by
  intro g hg e
  have hm := own_kind_of h K g hg
  rw [e] at hm
  exact absurd hm (by decide)

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.widerFillOwn_lots
#print axioms ProofFile.Honest.FirstFill.widerPairs_is
#print axioms ProofFile.Honest.FirstFill.LongKinds.all
#print axioms ProofFile.Honest.FirstFill.ownPairs_nodup
#print axioms ProofFile.Honest.FirstFill.longKinds_plain
#print axioms ProofFile.Honest.FirstFill.own_others_apart
#print axioms ProofFile.Honest.FirstFill.own_first_find
#print axioms ProofFile.Honest.FirstFill.own_kind_of
#print axioms ProofFile.Honest.FirstFill.own_first_none
#print axioms ProofFile.Honest.FirstFill.own_first_none_in
#print axioms ProofFile.Honest.FirstFill.own_no_frame
