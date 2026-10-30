-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorFold.lean: SH₃ (the premise on `PL.shape 0` of the joint between the
batch's shared rounds and the last chain) AT THE START OF THE IOP AS WRITTEN IN LEAN, AT THE SMALL
DOOR: four facts on the first chain's last verifier's state come from "reached", the rest from what
stays in the first table's promise. One structure of premises; statements and proofs.

Why. The names that only carry a fact on the verifier's
state leave the first table's door and become fields of one structure of fold facts
(Johnson/Desc/First/FoldFacts.lean: not imported); the joints beyond the chain then carry "reached"
at the chain's last border beside `ocEnd`. Of `DoorSays` (Johnson/Desc/Last/ShapeDoorSays.lean) that
strikes tidy, fits, weights, sits and their "open". Here the form at the small door.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`DoorStays N₁ Mg₁ links ps Pw V`**: what is still asked of the first table's meaning and table,
    and of the list of rounds: laid, laidOpen: the table's own `evalLaid` says `K13.Law.evalLaidB
    Pw` and is open at the last border · held: `Mg₁.held j t a` is `smpHeld a.2.st a.2.book j t` ·
    indexIn, wIn: V's two places are among the sampled tenants of the open items there · oneIndex,
    oneW: V's two shapes count one answer.
  `FourFacts V s`: `Means.tidy4B s.st`, `bookFitsB s.book`, `First.weightsB s`, `ownSitsB V s`: the
    bodies of the fields tidy, bookFits, weightsOk, ownSits.
  **`doorFirstB_of_fold`**: under `DoorStays`, inside `ocEnd`, at a state without a mark that meets
    `FourFacts`: `doorFirstB`.
  **`sh₃_fold_X`**: as `sh₃_says_X`, at Oc := fun q y => `ocEnd g N₁ Mg₁ links ps q y` ∧ Rc q, Rc a
    letter: ITS PREMISES: hZ · hg · H : `DoorStays` · hR : ∀ q, Rc q → (g q).2.failed = none →
    `FourFacts V (g q).2`.

Every "there is": none in a conclusion.
HOW hR IS PAID FROM THE STRUCTURE OF FOLD FACTS: at Rc q := ∃ a, Rch K a ∧ at_ a = g q: four fields
at (K, a); `K12.Door.atFirstFits s` is `bookFitsB s.book` by its make [as reported, not shown here].
Limits. That the shared chain's promise carries Rc along is the frame's matter (a letter more in
Oc). Of the four fields weightsOk lies (WeightsReached.lean: `weightsOk_field`); bookFits lies
as reported, not shown here; tidy and ownSits are owed. N, Pm₀, Mg₁, N₁, links, ps, Pw, V, split,
T, R, g, X, Rc are letters. NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open OnBytes

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets weightsB openSets sampledIn)
open _root_.Desc.K14 (St)

/-- **WHAT THE DOOR STILL ASKS OF THE FIRST TABLE's MEANING AND TABLE, AND OF THE LIST OF ROUNDS**,
at the small door. -/
structure DoorStays {P₀ W₁ : Type} (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart)
    (ps : List Place) (Pw : K13.Where) (V : OwnSeats) : Prop where
  laid : ∀ a, Mg₁.pub .evalLaid a = K13.Law.evalLaidB Pw a.2
  held : ∀ j t a, Mg₁.held j t a = smpHeld a.2.st a.2.book j t
  laidOpen : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []
  indexIn : V.index ∈ sampledIn N₁ ((openSets links ps (First.start links))[ps.length]?.getD [])
  wIn : V.w ∈ sampledIn N₁ ((openSets links ps (First.start links))[ps.length]?.getD [])
  oneIndex : V.indexShape.answers = 1
  oneW : V.wShape.answers = 1

/-- The bodies of four fields of the structure of fold facts, at one verifier's state. -/
def FourFacts (V : OwnSeats) (s : First.S) : Prop :=
  Means.tidy4B s.st = true ∧ bookFitsB s.book = true ∧ weightsB s = true ∧ ownSitsB V s = true

/-- **THE FIRST CHAIN's TEXT AT THE DOOR, AT THE SMALL DOOR.** -/
theorem doorFirstB_of_fold {A P₀ W₁ : Type} (get : A → P₀ × First.S) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where) (V : OwnSeats)
    (H : DoorStays N₁ Mg₁ links ps Pw V) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) (hF : FourFacts V (get p).2) :
    doorFirstB (get p).2 = true := by
  obtain ⟨t1, t2, t3, t5⟩ := hF
  have t4 := ocEnd_pub get N₁ Mg₁ links ps p y h hm _ H.laidOpen
  have t6 := ocEnd_held get N₁ Mg₁ links ps p y h hm _ H.indexIn
  have t7 := ocEnd_held get N₁ Mg₁ links ps p y h hm _ H.wIn
  rw [H.laid] at t4
  rw [H.held] at t6 t7
  have t8 := ownTwoB_of_sits t5 t2 t6 t7 H.oneIndex H.oneW
  cases hs : (firstOfS (get p).2).isSome with
  | false =>
    unfold doorFirstB
    rw [Option.isSome_eq_false_iff.1 hs |> Option.isNone_iff_eq_none.1]
  | true =>
    exact doorFirstB_of_items t1 t2 t3 ((K13.Law.evalLaidB_iff Pw _).1 t4) (two_of_ownTwoB t8 hs)

/-- **SH₃'s CONCLUSION AND X, AT THE SEATED START AND A COMPUTED PUBLIC PART, AT THE SMALL
DOOR.** -/
theorem sh₃_fold_X {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where)
    (V : OwnSeats) (H : DoorStays N₁ Mg₁ links ps Pw V)
    (Rc : ProofFile.InstPub × First.S → Prop)
    (hR : ∀ q, Rc q → (g q).2.failed = none → FourFacts V (g q).2) (X : St → Bool)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ fun k d => doorX (ProofFile.pAt Z) (1 + T.l₂.length) k d &&
        (k != 1 + T.l₂.length || X d))
      (fun q y => ocEnd g N₁ Mg₁ links ps q y ∧ Rc q) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true ∧
      X b.1.2 = true := by
  refine ⟨?_, x_at_last N Pm₀ _ split T.p₂ T.l₂ (ProofFile.pAt Z) (1 + T.l₂.length) X b hb⟩
  refine sh₃_of_first (ProofFile.pAt Z) R g
    (fun q a d => ((ProofFile.seatedAt o Z Np c).start₃ q a d).toOption) T N _ _ split (fun d hd => ?_)
    (fun q y hq hm => doorFirstB_of_fold g N₁ Mg₁ links ps Pw V H q y hq.1 hm (hR q hq.2 hm))
    (ProofFile.hmark_at o Z Np c g hg) (ProofFile.hstart_at o Z Np c g hg) (ahead_at_seat hZ) b s hb hs
  have h' : (Pm₀.shape (1 + T.l₂.length) d && (doorX (ProofFile.pAt Z) (1 + T.l₂.length)
      (1 + T.l₂.length) d && (1 + T.l₂.length != 1 + T.l₂.length || X d))) = true := hd
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').2).1
  rw [doorX_at] at h2
  exact h2

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.doorFirstB_of_fold
#print axioms VerifiableInference.Desc.Last.sh₃_fold_X
