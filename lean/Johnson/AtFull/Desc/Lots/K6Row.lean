-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Desc/Lots/K6Row.lean: THE ROW OF THE LOT OF THE OUTPUT HEAD'S OWN ROUNDS
(P4.k6Lot, Johnson/Desc/ProofFile/Lot/K6K7.lean: the first of the two lots of ProofFile.p4Pure) FOR "the
proof file's description is put together at written skeletons": UNDER HYPOTHESES BY FIELD ON WHAT
THE LOT READS OF THE PUBLIC PART Z AND THE SEGMENTS' RECORDS G, THE LOT'S SKELETON (ProofFile.Sk.lotSk,
Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean) IS A WRITTEN ONE. Definitions, statements and
proofs; nothing is evaluated.

WHAT IT DOES NOT SAY, FIRST. THAT ANY Z AND G MEET THE HYPOTHESES. It pays none of them. NO EXAMPLE
OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose
own Limits say what they are worth. The written skeleton bears the KIND's name, not the place's
("H:4"): the name column comes of the spots. Nothing on soundness.

Main names (namespace Johnson.AtFull.Lots).
  k6SkW, k6LotW: the written skeletons of the block and of the lot.
  toldFrom_empties: a block none of whose rounds sends an oracle message tells nothing.
  lPdAt h: the logarithm of the padded number of features, at the sizes that the kind reads off the
      shape h.
  skel_seated: GENERAL: the skeleton of the block as a lot seats it, at every public record, link
      and list "before".
  headBefore_at: the list "before" BY FIELD.
  K6Reads Z G: what the lot reads, field by field.
  k6_row_at: THE ROW. k6_steady: the lot supplies no batching.
  k6_row_fails: THE ROW CAN FAIL: where the list "before" is refused, or the plan names no array of
      reads, the lot has no block.

By seatedClaims_some (Law/SeatedBridge.lean), Prices.rounds_length and prices_length
(Law/HeadPrices.lean), and steady_none (Law/Skel/SkelEnd.lean).
WHAT PROVES THE FIELDS, NONE CALLED HERE: ok, laid: by numbers: planOk_of_numbers, laid_of_numbers;
in the goals' scope: ok_in_scope, laidOk_in_scope (Johnson/Goal/Meaning/HeadCondScope.lean) ·
third: ReadsNamed.public_third, wherever publicOf returns · the two lists in "before": k6Msgs_at
(K6RowAt.lean), where the table of steps and the entries are the written ones.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.ProofFile.Lot.K6K7
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.Kinds.Law.HeadPrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots

open OnBytes
open ProofFile.Sk (Skel LotSk skel lotSk toldFrom Steady steady_none)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Kinds (Norm.lPd Norm.d)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (seatedClaims_some)

/-- The skeleton of K6's block at a link, a number of rounds, a list "before" and a test. -/
def k6SkAt (l n : Nat) (ms : List (Nat × Nat)) (ok : Bool) : Skel :=
  { name := "the output head's own rounds", place := ⟨1, some l, 4, .K6⟩, nRounds := n
    nOracles := n, told := [], before := ms, planOk := ok
    claims := ["norm", "join", "policy", "logits"], after := [] }

/-- **The written skeleton of K6's block.** -/
def k6SkW : Skel := k6SkAt 24 82 [(1, 73), (1, 67)] true

/-- **The written skeleton of K6's lot.** -/
def k6LotW : LotSk :=
  { name := "the output head's own rounds (K6)", letters := false, still := [], blocks := [k6SkW]
    batch := fun _ => none, each := fun _ => false, tests := fun _ => false }

/-- A block none of whose rounds sends an oracle message tells nothing. -/
theorem toldFrom_empties {α : Type} (l : List α) :
    ∀ k, toldFrom k (l.map fun _ => ([] : List VerifiableInference.Desc.Oracle)) = [] := by
  induction l with
  | nil => intro k; rfl
  | cons a l ih =>
    intro k
    have e : toldFrom k (([] : List VerifiableInference.Desc.Oracle) :: l.map fun _ => []) =
        toldFrom (k + 1) (l.map fun _ => []) := rfl
    exact e.trans (ih (k + 1))

/-- The logarithm of the padded number of features, at the sizes that the kind reads off a shape. -/
def lPdAt (h : Model.Head.Shape) : Nat :=
  letI := sizesOf h
  Norm.lPd

/-- **GENERAL: the skeleton of the block as a lot seats it.** -/
theorem skel_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    skel b = k6SkAt l (16 + 2 * lPdAt W.hS + 4 * W.hS.lt) ms
      ((parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request)).ok && laidOk W) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.mp h0
  have hn : (@rounds (sizesOf W.hS)).length =
      16 + 2 * lPdAt W.hS + 4 * W.hS.lt :=
    (@Law.Prices.rounds_length (sizesOf W.hS)).trans (Law.Prices.prices_length _ _)
  unfold skel k6SkAt
  simp only [Skel.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · show (List.map _ (@rounds (sizesOf W.hS))).length = _
    rw [List.length_map]
    exact hn
  · show (List.map _ (List.map _ (@rounds (sizesOf W.hS)))).length = _
    rw [List.length_map, List.length_map]
    exact hn
  · exact toldFrom_empties _ 0

/-- **The list "before", by field.** X: the last built segment; t: its one foreign array; l₀: the
link that bore it; Y: that link's record. -/
theorem headBefore_at {Z : ProofFile.Pub} {G : ProofFile.Ground} {X Y : Model.Stages.LinkH} {t l₀ : Nat}
    {nm : String} {a b : List Nat} (hX : G.built.back? = some X)
    (hFT : X.tl.ix.FT.toList = [t]) (hborn : X.arrayOf[t]? = some (l₀, nm))
    (hY : G.built[l₀]? = some Y) (ha : ProofFile.k8Msgs Z (X.name ++ ".1.call") = a)
    (hb : ProofFile.k8Msgs Z (Y.name ++ ".0.call") = b) (ha0 : a ≠ []) (hb0 : b ≠ []) :
    P4.headBefore Z G = some ((a ++ b).map fun n => (1, n)) := by
  have hd : [l₀].eraseDups = [l₀] := by simp [List.eraseDups_cons]
  unfold P4.headBefore
  simp [hX, hFT, hborn, hd, hY, ha, hb, ha0, hb0]

/-- **What the lot reads of Z and G, field by field.** -/
structure K6Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) : Prop where
  size : G.built.size = 25
  third : ∃ iU3, G.W.H.tl.ix.U.getD 2 none = some iU3
  lt : G.W.hS.lt = 10
  d : G.W.hS.d = 5120
  ok : (parOf G.W.hS ((Params.settingOf G.W.P.frame).workOf .field .request)).ok = true
  laid : laidOk G.W = true
  before : ∃ (X Y : Model.Stages.LinkH) (t l₀ : Nat) (nm : String), G.built.back? = some X ∧
    X.tl.ix.FT.toList = [t] ∧ X.arrayOf[t]? = some (l₀, nm) ∧ G.built[l₀]? = some Y ∧
    X.name = "H" ∧ Y.name = "G11" ∧
    ProofFile.k8Msgs Z "H.1.call" = [73] ∧ ProofFile.k8Msgs Z "G11.0.call" = [67]

/-- The lot's blocks are the one table. -/
theorem k6_blocks (Z : ProofFile.Pub) (G : ProofFile.Ground) : (P4.k6Lot Z).blocks G = P4.k6Hear Z G := rfl

/-- Where the list "before" is given and the plan names the array of reads, the lot has just one
block. -/
theorem k6Hear_some {Z : ProofFile.Pub} {G : ProofFile.Ground} {ms : List (Nat × Nat)} {iU3 : Nat}
    (hB : P4.headBefore Z G = some ms) (hU : G.W.H.tl.ix.U.getD 2 none = some iU3) :
    ∃ b, seatedClaims G.W (G.built.size - 1) ms = some b ∧ P4.k6Hear Z G = [b] := by
  obtain ⟨b, hs⟩ : ∃ b, seatedClaims G.W (G.built.size - 1) ms = some b := by
    unfold seatedClaims blockClaims
    rw [hU]
    exact ⟨_, rfl⟩
  refine ⟨b, hs, ?_⟩
  unfold P4.k6Hear
  rw [hB]
  show (seatedClaims G.W (G.built.size - 1) ms).toList = [b]
  rw [hs]
  rfl

/-- Where it is refused, or the plan names none, the lot has no block. -/
theorem k6Hear_none {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : P4.headBefore Z G = none ∨ G.W.H.tl.ix.U.getD 2 none = none) : P4.k6Hear Z G = [] := by
  unfold P4.k6Hear
  rcases h with h | h
  · rw [h]
    rfl
  · cases P4.headBefore Z G with
    | none => rfl
    | some ms =>
      show (seatedClaims G.W (G.built.size - 1) ms).toList = []
      unfold seatedClaims blockClaims
      rw [h]
      rfl

/-- **JUST WHAT THE ROW ASKS.** -/
theorem k6_row_iff {Z : ProofFile.Pub} {G : ProofFile.Ground} :
    lotSk G (P4.k6Lot Z) = k6LotW ↔
      P4.headBefore Z G = some [(1, 73), (1, 67)] ∧
        (∃ iU3, G.W.H.tl.ix.U.getD 2 none = some iU3) ∧ G.built.size - 1 = 24 ∧
        16 + 2 * lPdAt G.W.hS + 4 * G.W.hS.lt = 82 ∧
        ((parOf G.W.hS ((Params.settingOf G.W.P.frame).workOf .field .request)).ok &&
          laidOk G.W) = true := by
  constructor
  · intro e
    have e1 : (P4.k6Hear Z G).map skel = [k6SkW] := congrArg LotSk.blocks e
    cases hB : P4.headBefore Z G with
    | none =>
      rw [k6Hear_none (Or.inl hB)] at e1
      cases e1
    | some ms =>
      cases hU : G.W.H.tl.ix.U.getD 2 none with
      | none =>
        rw [k6Hear_none (Or.inr hU)] at e1
        cases e1
      | some iU3 =>
        obtain ⟨b, hs, hH⟩ := k6Hear_some hB hU
        rw [hH, List.map_cons, List.map_nil, skel_seated hs] at e1
        have e2 := List.head_eq_of_cons_eq e1
        unfold k6SkW k6SkAt at e2
        simp only [Skel.mk.injEq, VerifiableInference.Desc.Place.mk.injEq, Option.some.injEq,
          true_and, and_true] at e2
        obtain ⟨hl, hn, -, hm, hk⟩ := e2
        exact ⟨by rw [hm], ⟨iU3, rfl⟩, hl, hn, hk⟩
  · rintro ⟨hB, ⟨iU3, hU⟩, hl, hn, hk⟩
    obtain ⟨b, hs, hH⟩ := k6Hear_some hB hU
    have hb : skel b = k6SkW := by
      rw [skel_seated hs, hl, hn, hk]
      rfl
    unfold lotSk k6LotW
    rw [k6_blocks, hH, List.map_cons, List.map_nil, hb]
    rfl

/-- **The storey between**: the row from K6Reads. -/
theorem k6_row_at {Z : ProofFile.Pub} {G : ProofFile.Ground} (R : K6Reads Z G) :
    lotSk G (P4.k6Lot Z) = k6LotW := by
  obtain ⟨X, Y, t, l₀, nm, hX, hFT, hborn, hY, nX, nY, ha, hb⟩ := R.before
  have hB : P4.headBefore Z G = some [(1, 73), (1, 67)] :=
    headBefore_at (a := [73]) (b := [67]) hX hFT hborn hY
      (by rw [nX, show "H" ++ ".1.call" = "H.1.call" from by decide]; exact ha)
      (by rw [nY, show "G11" ++ ".0.call" = "G11.0.call" from by decide]; exact hb) (by simp)
      (by simp)
  have hl : lPdAt G.W.hS = 13 := by
    unfold lPdAt Norm.lPd
    rw [show (letI := sizesOf G.W.hS; Norm.d) = 5120 from R.d]
    decide
  exact k6_row_iff.2 ⟨hB, R.third, by rw [R.size], by rw [hl, R.lt], by rw [R.ok, R.laid]; rfl⟩

/-- The lot supplies no batching. -/
theorem k6_steady (Z : ProofFile.Pub) (G : ProofFile.Ground) : Steady G (P4.k6Lot Z) :=
  steady_none G (P4.k6Lot Z) fun _ => rfl

/-- Where the list "before" is refused, or the plan names no array of reads, the row is false. -/
theorem k6_row_fails {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : P4.headBefore Z G = none ∨ G.W.H.tl.ix.U.getD 2 none = none) :
    lotSk G (P4.k6Lot Z) ≠ k6LotW := by
  intro e
  have e1 : (P4.k6Hear Z G).map skel = [k6SkW] := congrArg LotSk.blocks e
  rw [k6Hear_none h] at e1
  cases e1

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.toldFrom_empties
#print axioms Johnson.AtFull.Lots.skel_seated
#print axioms Johnson.AtFull.Lots.headBefore_at
#print axioms Johnson.AtFull.Lots.k6_blocks
#print axioms Johnson.AtFull.Lots.k6Hear_some
#print axioms Johnson.AtFull.Lots.k6Hear_none
#print axioms Johnson.AtFull.Lots.k6_row_iff
#print axioms Johnson.AtFull.Lots.k6_row_at
#print axioms Johnson.AtFull.Lots.k6_steady
#print axioms Johnson.AtFull.Lots.k6_row_fails
