-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/PlaysAtOwnMats.lean: THE SMALLNESS TEST: THE DEBT "IT PLAYS"
(`PlaysS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT ALL 25 OF THE KIND's DRAWS, AT THE
PROVER THAT THE MAKER `onlineProverFromPublicFiles` BUILDS, WHERE THE LOT's LISTS OF MATRICES ARE THOSE THAT THE KIND
"LOOKUP" MAKES (`K3.matsOwn`, Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean): THE PREMISE ON THE
LISTS' LENGTHS OF `playsS_at_fill` (Johnson/Desc/ProofFile/Honest/K8/PlaysAtFill.lean) IS PAID
THERE. Two theorems; no definition; none of the library's goals.

  `hlen_matsOwn`   under the library's head (h : `P5J.AtMgA`), where the maker returns A at the
                   head's own three files: at each planned link Xl of A.G at l: K3.matsOwn A.G.W l
                   has one entry for each matrix of the link (it is as long as the place's list
                   `ks`)
  **`playsS_at_ownMats`**   l < 25 ⊢ PlaysS ‹the thread at H := A.H› Said
                   (14 * l + (if l = 24 then 5 else 4) + 2)
THE PREMISES LEFT, ALL THREE ON THE MAKER AND ITS FILLING: the maker returns A at a filling P · some
lot of P.lots has, at A.Z and A.G, the halves of `smallLot cells (fun _ G _ l => K3.matsOwn G.W l)`
· every lot of P.lots has there halves at places of other kinds than K8 alone, or these halves.
HOW. `matsOwn_meets_blank` (Johnson/Desc/ProofFile/Honest/K8/MatsScope.lean: in the goals' scope the
plan of link l in the public parameters is the plan of the built segment number l) · `atPure_ok`
(Johnson/Desc/ProofFile/Honest/AtPureLaw.lean) · that the ground has 25 segments: `IM.ground_gets`
(Johnson/IMR/PureJoin.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `omega` on one line, on a number of segments.
Limits. THE TWO PREMISES ON THE LIST OF LOTS ARE NOT PROVED HERE OF ANY FILLING. THAT `onlineProverFromPublicFiles`
RETURNS IS A PREMISE. cells is a letter; so are the thread's other letters. Nothing on whether a
list's entry names the right cells. THE FULL SIZE ALONE. Which of the files that this
head names are rows of the library is for the library's own list to say: it is not said here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtFill
import Johnson.Desc.ProofFile.Honest.K8.MatsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

variable {W₀ Rc Tr X₀ X : Type}
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
include h hA

/-- **The lookup's own lists have the places' lengths.** -/
theorem hlen_matsOwn : ∀ (l : ℕ) (Xl : LinkH), A.G.built[l]? = some Xl →
    (K3.matsOwn A.G.W l).length = (ProofFile.k8Par A.Z A.G Xl l).ks.length := by
  intro l Xl hX
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have h25 : A.G.built.size = 25 := (IM.ground_gets h.scope h.reads hZ hG).1
  have hlt : l < A.G.built.size := (Array.getElem?_eq_some_iff.1 hX).1
  exact (matsOwn_meets_blank h.scope hZ hG (by omega) hX).1

variable (cells : Tr → Cells) {Bk : ProverCoinCounts}
  (hex : ∃ M ∈ P.lots, M.halves A.Z A.G =
    (smallLot cells fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
  (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K8) ∨
    M.halves A.Z A.G = (smallLot cells fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
include hex ho

/-- **IT PLAYS AT ALL 25 DRAWS, AT THE LOOKUP's OWN LISTS.** -/
theorem playsS_at_ownMats (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : ℕ}
    (hl : l < 25) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) :=
  playsS_at_fill cells (fun _ G _ l => K3.matsOwn G.W l) h hA hex ho (hlen_matsOwn h hA) Q test
    carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hlen_matsOwn
#print axioms ProofFile.Honest.K8.playsS_at_ownMats
