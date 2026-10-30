-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3Skel.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot,
Johnson/Desc/ProofFile/Lot/K3.lean): THE SKELETON (ProofFile.Sk.Skel,
Johnson/Desc/ProofFile/Law/Skel/Skel.lean) OF THE SUB-PROTOCOL THAT THE KIND's OWN TEXT
`K3.theStated` MAKES AT A LOOKUP's ADDRESS, AS A TERM OF WHAT THAT TEXT READS. Definitions with
code; theorems. GENERAL: at every public data, codes and shape: no scope, no head, no opening.
  `skOwn`: the skeleton of the kind's own sub-protocol, of the lookup's parameters, the piece, the
    list "before" and the plan's test.
  `dress`: what the step without a round behind it and the caller's run "planes" do to a skeleton.
  `skAt`: `theStated`'s text on skeletons.
  `skel_blockVia`, `own_at`, `skel_theStated`: **(theStated … ⟨1, some i, pieceAt X i d, .K3⟩).map
    skel = skAt …**.
  `hear_skel`, `lot_skel`: the lot's sub-protocols' skeletons are the values of skAt over the
    addresses; the lot reads nothing of the ground.
Limits. Nothing is evaluated here. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.ProofFile.Law.Skel.Skel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (theStated theWhole theOwn pieceAt isHead quietAt withCaller
  seatCalls seatDigits)
open VerifiableInference.Desc.First.Look (P placeAt beforeAt laidAt padKeyAt)
open ProofFile.Sk (Skel skel toldFrom skel_andThen skel_quiet)

/-- The skeleton of the kind's own sub-protocol. -/
def skOwn (p : P) (piece : Nat) (sent : List (Nat × Nat)) (ok : Bool) : Skel :=
  { name := p.name, place := ⟨1, some p.link, piece, .K3⟩, nRounds := p.rounds.length
    nOracles := p.rounds.length, told := [], before := sent, planOk := ok
    claims := ["objects", "guests"], after := [] }

/-- The step without a round behind it; the caller's run. -/
def dress (quiet caller : Bool) (i piece : Nat) (k : Skel) : Skel :=
  let k1 := if quiet then k.andThen k.name (Skel.quiet (k.name ++ ": behind it") 1 (some i) piece)
    else k
  if caller then { k1 with claims := k1.claims ++ ["planes"] } else k1

/-- **`theStated`'s text on skeletons.** rd: whether the calling kind's readers are there. -/
def skAt (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (rd : Bool) (i : Nat)
    (d : Bool) : Option Skel :=
  (placeAt X i d).bind fun p => (beforeAt codes shape i d).bind fun sent =>
    (laidAt X i d).bind fun laid => (padKeyAt X i d).map fun key =>
      dress (quietAt X i d).isSome (!d && rd) i (pieceAt X i d)
        (skOwn p (pieceAt X i d) sent
          (K3.planOk (S := First.S) (Cl := Claim) p laid [] && K3.Law.fitsVia p && key))

theorem toldFrom_replicate (n : Nat) :
    ∀ k, toldFrom k (List.replicate n ([] : List VerifiableInference.Desc.Oracle)) = [] := by
  induction n with
  | zero => intro k; rfl
  | succ n ih => intro k; simp [List.replicate_succ, toldFrom, ih]

theorem skel_blockVia {Cl : Type} (seat : K3.Seat First.S Cl) (piece : Nat) (laid : Array Nat)
    (sent : List (Nat × Nat)) (p : P) :
    skel (K3.Law.blockVia seat piece laid sent p []) =
      skOwn p piece sent (K3.planOk (S := First.S) (Cl := Cl) p laid [] && K3.Law.fitsVia p) := by
  simp [skel, K3.Law.blockVia, skOwn, toldFrom_replicate]

/-- The plan's test does not read the type of claims where there is no guest. -/
theorem planOk_cl {Cl Cl' : Type} (p : P) (laid : Array Nat) :
    K3.planOk (S := First.S) (Cl := Cl) p laid [] =
      K3.planOk (S := First.S) (Cl := Cl') p laid [] := by
  unfold K3.planOk First.Look.P.planOk
  rfl

theorem skel_plan {Cl : Type} (b : Block First.S Cl) (ok : Bool) :
    skel { b with planOk := ok } = { skel b with planOk := ok } := rfl

theorem skel_caller {Cl : Type} (seat : K3.Seat First.S Cl) (p : P) (r : K3.Readers First.S)
    (b : Block First.S Cl) :
    skel (withCaller seat p r b) = { skel b with claims := (skel b).claims ++ ["planes"] } := by
  simp [skel, withCaller]

theorem piece_ne (X : Verify.Public) (i : Nat) : pieceAt X i false ≠ pieceAt X i true := by
  unfold pieceAt
  split <;> decide

theorem piece_beq (X : Verify.Public) (i : Nat) (d : Bool) :
    (pieceAt X i d == pieceAt X i true) = d := by
  cases d
  · exact beq_eq_false_iff_ne.2 (piece_ne X i)
  · exact beq_self_eq_true _

theorem piece_bne (X : Verify.Public) (i : Nat) (d : Bool) :
    (pieceAt X i d != pieceAt X i false) = d := by
  cases d
  · exact bne_self_eq_false _
  · exact bne_iff_ne.2 (piece_ne X i).symm

theorem findSome_two {β : Type} (f : Bool → Option β) :
    [false, true].findSome? f = (f false).or (f true) := by
  cases h : f false <;> cases h' : f true <;> simp [List.findSome?, h, h']

/-- The kind's own sub-protocol at the lookup's address, of what the four readings give. -/
def ownOf {Cl : Type} (claim : Aff → Cl) (piece : Nat) (d : Bool) (p : P)
    (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) : Block First.S Cl :=
  let b₀ := K3.Law.blockVia (if d then seatDigits claim else seatCalls claim) piece laid sent p []
  { b₀ with planOk := b₀.planOk && key }

/-- **`theOwn` at a lookup's own address.** -/
theorem own_at {Cl : Type} (claim : Aff → Cl) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (i : Nat) (d : Bool) :
    theOwn claim true X codes shape ⟨1, some i, pieceAt X i d, .K3⟩ =
      (placeAt X i d).bind fun p => (beforeAt codes shape i d).bind fun sent =>
        (laidAt X i d).bind fun laid => (padKeyAt X i d).map fun key =>
          ownOf claim (pieceAt X i d) d p sent laid key := by
  unfold theOwn
  dsimp only
  rw [if_neg (by decide)]
  rw [Option.bind_some, findSome_two]
  cases d
  · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      bne_iff_ne.2 (piece_ne X i), Option.or_none]
    rfl
  · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      bne_iff_ne.2 (piece_ne X i).symm, Option.none_or]
    rfl

theorem ownOf_name {Cl : Type} (claim : Aff → Cl) (piece : Nat) (d : Bool) (p : P)
    (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) :
    (ownOf claim piece d p sent laid key).name = p.name := rfl

theorem skel_ownOf {Cl : Type} (claim : Aff → Cl) (piece : Nat) (d : Bool) (p : P)
    (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) :
    skel (ownOf claim piece d p sent laid key) =
      skOwn p piece sent
        (K3.planOk (S := First.S) (Cl := Claim) p laid [] && K3.Law.fitsVia p && key) := by
  unfold ownOf
  rw [skel_plan, skel_blockVia, planOk_cl (Cl' := Claim)]
  rfl

/-- **THE SKELETON OF WHAT `theStated` MAKES AT A LOOKUP's ADDRESS.** -/
theorem skel_theStated {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (K3.Readers First.S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat) (d : Bool) :
    (theStated claim readers X codes shape ⟨1, some i, pieceAt X i d, .K3⟩).map skel =
      skAt X codes shape (readers i).isSome i d := by
  unfold theStated theWhole skAt
  rw [own_at]
  cases hp : placeAt X i d with
  | none => rfl
  | some p =>
    cases hs : beforeAt codes shape i d with
    | none => rfl
    | some sent =>
      cases hl : laidAt X i d with
      | none => rfl
      | some laid =>
        cases hk : padKeyAt X i d with
        | none => rfl
        | some key =>
          simp only [Option.bind_some, Option.map_some, piece_beq, piece_bne]
          cases hq : quietAt X i d <;> cases hr : readers i <;> cases d <;>
            simp [dress, skel_andThen, skel_quiet, skel_ownOf, skel_caller, hp, ownOf_name, skOwn]

/-- **The lot's sub-protocols' skeletons.** -/
theorem hear_skel (Z : ProofFile.Pub) :
    (K3Lot.hear Z).map skel =
      (K3Lot.addresses Z).filterMap fun x =>
        skAt Z.p.X Z.first.codes Z.first.shape (K3Lot.readersAt Z.p.X x.1).isSome x.1 x.2.1 := by
  unfold K3Lot.hear
  rw [List.map_filterMap]
  refine List.filterMap_congr fun x hx => ?_
  unfold K3Lot.addresses at hx
  obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨dg, -, rfl⟩ := List.mem_map.1 hx
  exact skel_theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape i dg

/-- **The lot returns, and reads nothing of the ground.** -/
theorem lot_skel (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((K3Lot.lot Z).blocks G).map skel =
      (K3Lot.addresses Z).filterMap fun x =>
        skAt Z.p.X Z.first.codes Z.first.shape (K3Lot.readersAt Z.p.X x.1).isSome x.1 x.2.1 :=
  hear_skel Z

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.toldFrom_replicate
#print axioms Johnson.AtFull.Lots.K3.skel_blockVia
#print axioms Johnson.AtFull.Lots.K3.piece_ne
#print axioms Johnson.AtFull.Lots.K3.piece_beq
#print axioms Johnson.AtFull.Lots.K3.own_at
#print axioms Johnson.AtFull.Lots.K3.skel_ownOf
#print axioms Johnson.AtFull.Lots.K3.skel_theStated
#print axioms Johnson.AtFull.Lots.K3.hear_skel
#print axioms Johnson.AtFull.Lots.K3.lot_skel
#print axioms Johnson.AtFull.Lots.K3.planOk_cl
#print axioms Johnson.AtFull.Lots.K3.skel_plan
#print axioms Johnson.AtFull.Lots.K3.skel_caller
#print axioms Johnson.AtFull.Lots.K3.piece_bne
#print axioms Johnson.AtFull.Lots.K3.findSome_two
#print axioms Johnson.AtFull.Lots.K3.ownOf_name
