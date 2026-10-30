-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/SentAtPlace.lean: **WHAT THE SUB-PROTOCOL AT A PLACE OF THE PROOF FILE's FIRST CHAIN SENDS, AS A TERM WITH CODE, BY EACH KIND's OWN MAKER OF ITS PARAMETER; AND THE LIST OF ROUNDS' SIDE OF THE FACTS "seatsCarried" AND "msgShapes" UNDER ONE TEST WITH CODE.** Definitions, statements and proofs.
As reported, not shown here, the join that takes these terms is general in the letter sn; its one sentence on sn is: sn k = [] wherever the place is of none of the kinds K1, K2, K12.
  sentAtPlace Z G a   by the place's kind: K1, in a link, at piece 1: the first segment's opening's messages (K1.firstPar) · K1, in a link, later: the link's messages of moment 1 (piece at most 5: the reads') | 2 (the digits') (K1.parLater) · K1, behind the links: W's sending (K1.parW at the program's linMessageW)
                      · K2: what the code switch into the place's group announces (P1K2.numsAt's sent) · K12: the last proximity test's switches' sendings (K12.Coin.sendsFrom at H2U.p12OfMade Z.made, from its second stage on) · every other kind: nothing.
  snAt Z G ps j       the same at place number j of a list of places ps (meant: the written list of the 358 places).
  snAt_calm | snAt_none   the join's one sentence on sn.
  snAt_k1_first | _k1_later | _w | _k2 | _k12   what it is at each sender's place: for the senders' files: each by rfl behind the place.
  shapes_of_lists     SendsAre c n sn → msgsOfChain c = the shapes of sn's sendings' notices, flattened: the like side of "msgShapes".
  **seats_side | shapes_side**   under sendsAreB Z.made.proof.1 n (snAt Z G ps) = true: seats_at_cut's premise at the tables' own L · the tables' own M.
WHICH PIECE BEARS WHICH MOMENT (at most 5: moment 1) IS READ OFF THE DRIVER's kindsBeforeBatching (the reads' place is piece 4, in the head's link 5; the digits' 6 | 7): no theorem here says it.
Limits. The test is evaluated nowhere here. That a sub-protocol sends what sentAtPlace says is each sender's files' debt. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Door.LaidOfLists
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.K12.Coin.BookAppends
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K1.First
import Johnson.Desc.K1.Places
import Johnson.Desc.ProofFile.Lot.K1
import Johnson.Desc.ProofFile.Lot.K2OfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params

/-- What the sub-protocol at a place sends. -/
def sentAtPlace (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) : List (Array OracleNotice) :=
  match a.kind, a.link with
  | .K1, some l =>
    if a.piece = 1 then [(K1.firstPar G.first (K1.gpOf Z)).sent]
    else [(K1.parLater G.first (K1.gpOf Z) l a.piece (if a.piece ≤ 5 then 1 else 2)).sent]
  | .K1, none =>
    ((linMessageW G.first.lin).map fun msg => (K1.parW G.first (K1.gpOf Z) a.piece msg).sent).toList
  | .K2, link => (((P1K2.prepOf Z G).bind fun P => P1K2.numsAt P link).map (·.sent)).toList
  | .K12, _ => Coin.sendsFrom (H2U.p12OfMade Z.made) 0 (H2U.p12OfMade Z.made).nums.stages.tail
  | _, _ => []

/-- The same at place number j of a list. -/
def snAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j : Nat) : List (Array OracleNotice) :=
  match ps[j]? with
  | some a => sentAtPlace Z G a
  | none => []

theorem snAt_some (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j : Nat) (a : Place)
    (h : ps[j]? = some a) : snAt Z G ps j = sentAtPlace Z G a := by
  unfold snAt
  rw [h]

theorem snAt_none (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j : Nat) (h : ps[j]? = none) :
    snAt Z G ps j = [] := by
  unfold snAt
  rw [h]

/-- **Whoever is of none of the three kinds sends nothing.** -/
theorem snAt_calm (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j : Nat) (a : Place)
    (h : ps[j]? = some a) (h1 : a.kind ≠ .K1) (h2 : a.kind ≠ .K2) (h12 : a.kind ≠ .K12) :
    snAt Z G ps j = [] := by
  rw [snAt_some Z G ps j a h]
  unfold sentAtPlace
  split
  · exact absurd (by assumption) h1
  · exact absurd (by assumption) h1
  · exact absurd (by assumption) h2
  · exact absurd (by assumption) h12
  · rfl

theorem snAt_k1_first (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j l : Nat)
    (h : ps[j]? = some ⟨1, some l, 1, .K1⟩) :
    snAt Z G ps j = [(K1.firstPar G.first (K1.gpOf Z)).sent] := by
  rw [snAt_some Z G ps j _ h]
  rfl

theorem snAt_k1_later (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j l piece : Nat)
    (h : ps[j]? = some ⟨1, some l, piece, .K1⟩) (hp : piece ≠ 1) :
    snAt Z G ps j =
      [(K1.parLater G.first (K1.gpOf Z) l piece (if piece ≤ 5 then 1 else 2)).sent] := by
  rw [snAt_some Z G ps j _ h]
  show (if piece = 1 then _ else _) = _
  rw [if_neg hp]

theorem snAt_w (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j piece : Nat)
    (h : ps[j]? = some ⟨1, none, piece, .K1⟩) :
    snAt Z G ps j = ((linMessageW G.first.lin).map fun msg =>
      (K1.parW G.first (K1.gpOf Z) piece msg).sent).toList := by
  rw [snAt_some Z G ps j _ h]
  rfl

theorem snAt_k2 (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j piece : Nat)
    (link : Option Nat) (h : ps[j]? = some ⟨1, link, piece, .K2⟩) :
    snAt Z G ps j =
      (((P1K2.prepOf Z G).bind fun P => P1K2.numsAt P link).map (·.sent)).toList := by
  rw [snAt_some Z G ps j _ h]
  rfl

theorem snAt_k12 (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (j piece : Nat)
    (link : Option Nat) (h : ps[j]? = some ⟨1, link, piece, .K12⟩) :
    snAt Z G ps j =
      Coin.sendsFrom (H2U.p12OfMade Z.made) 0 (H2U.p12OfMade Z.made).nums.stages.tail := by
  rw [snAt_some Z G ps j _ h]
  rfl

/-- **The like side of "msgShapes".** -/
theorem shapes_of_lists (c : Johnson.G.ChainSends) (n : Nat) (sn : Nat → List (Array OracleNotice))
    (hE : SendsAre c n sn) :
    msgsOfChain c = (((List.range n).flatMap sn).flatMap (·.toList)).map (·.shape) := by
  unfold SendsAre at hE
  rw [← hE]
  unfold msgsOfChain msgsOf
  rw [List.flatMap_map]
  simp only [List.flatMap_def, List.map_map, Function.comp_def, List.toList_toArray, List.map_id']

/-- **The list of rounds' side of "seatsCarried", under one test with code.** -/
theorem seats_side (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (n : Nat) (codes : Codes)
    (Ld : Laid) (hB : sendsAreB Z.made.proof.1 n (snAt Z G ps) = true)
    (hLd : laidAtCodes codes Z.made.proof.1 = some Ld) :
    Coin.laidOf codes ((List.range n).flatMap (snAt Z G ps)) = some (toTree Ld) :=
  laid_of_lists codes Z.made.proof.1 n (snAt Z G ps) Ld (sendsAre_of_B hB) hLd

/-- **And of "msgShapes".** -/
theorem shapes_side (Z : ProofFile.Pub) (G : ProofFile.Ground) (ps : List Place) (n : Nat)
    (hB : sendsAreB Z.made.proof.1 n (snAt Z G ps) = true) :
    msgsOfChain Z.made.proof.1 =
      (((List.range n).flatMap (snAt Z G ps)).flatMap (·.toList)).map (·.shape) :=
  shapes_of_lists Z.made.proof.1 n (snAt Z G ps) (sendsAre_of_B hB)

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.snAt_calm
#print axioms VerifiableInference.Desc.K12.Door.snAt_none
#print axioms VerifiableInference.Desc.K12.Door.snAt_k1_first
#print axioms VerifiableInference.Desc.K12.Door.snAt_k1_later
#print axioms VerifiableInference.Desc.K12.Door.snAt_w
#print axioms VerifiableInference.Desc.K12.Door.snAt_k2
#print axioms VerifiableInference.Desc.K12.Door.snAt_k12
#print axioms VerifiableInference.Desc.K12.Door.shapes_of_lists
#print axioms VerifiableInference.Desc.K12.Door.seats_side
#print axioms VerifiableInference.Desc.K12.Door.shapes_side
