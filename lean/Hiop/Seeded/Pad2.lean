-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Pad2.lean: a second small object, all three of whose protocols have a real round.

Definitions, statements and proofs. A toy: nothing here is about the protocol of the release. This
file states no goal of the release.

THREE INDICES: the two bits, and one index OUT OF RANGE (`none`), which is encoded as the bit 0 is.
The encoding is that of `pad` (Hiop/Seeded/Pad.lean) at the index's bit i: the committer's
randomness is two bits (r₁, r₂); the encoded index the one symbol i + r₁; two seeds; the honest
answer at the seed s is i · s + r₂. Each verifier reads the encoded index(es). AT THE INDEX OUT OF
RANGE ALL THREE HONEST SIDES STOP, at every verifier's randomness: a stop that hangs on the private
input, and tells it.
  The offline protocol, one round: the prover sends AN ORACLE that holds the symbol, and a run value
    in the clear; the verifier reads the oracle's one position and the symbol of the encoded index,
    and compares.
  Link, one round: the prover sends (the sum of the two symbols, a run value); the verifier reads
    both symbols and compares.
  A session, two rounds. Round 1, local: the prover sends ((the symbol, a run value), a number); the
    verifier message is a block of 32 bits. Round 2, shared: the prover sends the block's second
    bit back. The verifier reads the symbol and compares both.
The run value is a coin of the prover's, sent in the clear. The number in round 1 is 0 here: it is
the place for the nonce of a compiled run's search.

Main names (namespace Hiop.Seeded.Two).
  `plainRound`, `Blk`, `rT`, `rL`, `rB1`, `rB2`; `testP`, `linkP`, `sessP`, `annB`: rounds,
    protocols, the session's marks (round 1 local, round 2 shared).
  `sideT`, `sideL`, `sideB`: the honest sides; the session's is handed the number of the copy.
  `simT`, `simL`, `simB`: simulators; `exactT`, `exactL`, `exactB`: at an index in range they are
    exact at every verifier's randomness. `stopsT`, `stopsL`, `stopsB`: out of range every value of
    it is a stop.
  `acceptT`, `acceptL`, `acceptB`: the verifiers accept the honest sides.
  `localT`, `localL`, `localB`: the verifiers' decisions hang on what is read alone.
  `pad2`: the object. `pad2_readsG`: each verifier reads one position of an encoded index; the
    encoding hides, at both seeds, AT ALL THREE INDICES.
The honest sides, the simulators and the proofs that these are exact follow those of
Hiop/Seeded/Pad.lean (`bitSide`, `bitSim`, `output_bitSide`).

Limits. A toy. The word has one symbol, so every budget of reads b ≥ 1 is the whole word: there is
no position that is not read, and no salt of a table's leaf hides anything that the pad r₁ does not
hide already. THE INDEX DECODER ANSWERS ONE FIXED INDEX AT EVERY WORD, and no seed is a collision
seed. It cannot do better: the word is wholly padded. So the languages for which the three protocols
are to be sound (HolographicProtocol.SoundAtR, Hiop/RecInterface.lean) hold every word, and soundness holds at this
object for lack of a case.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.GameMembers

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded.Two
open Prob Iop Compile.Lifetime Hiop.Seeded
open scoped ENNReal

/-! ## Rounds and protocols -/

/-- A round without an oracle: the prover sends a plain part in P; the verifier message is in C. -/
def plainRound (P C : Type) [Fintype C] [Nonempty C] (d : P) : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := P
  Chal := C
  dOrc := ()
  dPlain := d

/-- A block of 32 bits. -/
abbrev Blk : Type := Fin 1 → Fin 32 → Bool

/-- The round of the offline protocol: AN ORACLE of one symbol, a bit; the plain part is a bit. -/
def rT : Round where
  Orc := Bool
  Pos := Unit
  Sym := fun _ => Bool
  rd := fun o _ => o
  Plain := Bool
  Chal := Unit
  dOrc := false
  dPlain := false

def rL : Round := plainRound (Bool × Bool) Unit (false, false)
def rB1 : Round := plainRound ((Bool × Bool) × ℕ) Blk ((false, false), 0)
def rB2 : Round := plainRound Bool Unit false

/-- the one position of the offline protocol's oracle -/
def posT : OPos [rT] := ((.inl ()) : Unit ⊕ Empty)

theorem oposT_eq (p : OPos [rT]) : p = posT :=
  match (p : Unit ⊕ Empty) with
  | .inl () => rfl
  | .inr e => e.elim

instance : DecidableEq (OPos [rT]) := fun a b => isTrue ((oposT_eq a).trans (oposT_eq b).symm)

theorem no_oposL (p : OPos [rL]) : False :=
  match (p : Empty ⊕ Empty) with
  | .inl e => e.elim
  | .inr e => e.elim

theorem no_oposB (p : OPos [rB1, rB2]) : False :=
  match (p : Empty ⊕ (Empty ⊕ Empty)) with
  | .inl e => e.elim
  | .inr (.inl e) => e.elim
  | .inr (.inr e) => e.elim

/-- what was sent in the one round: the oracle's symbol, the plain part -/
def orT (τ : Tr [rT]) : Bool := τ.1.1
def plT (τ : Tr [rT]) : Bool := τ.1.2
def plL (τ : Tr [rL]) : Bool × Bool := τ.1.2
/-- round 1's plain part, its verifier message, round 2's plain part -/
def plB1 (τ : Tr [rB1, rB2]) : (Bool × Bool) × ℕ := τ.1.2
def chB1 (τ : Tr [rB1, rB2]) : Blk := τ.2.1
def plB2 (τ : Tr [rB1, rB2]) : Bool := τ.2.2.1.2

def testP (Y : Type) : InteractiveOracleProof Y (oneExternalString 1 Bool) where
  shape := [rT]
  blinded := fun _ => true
  extReads := fun _ _ => ({0} : Finset (Fin 1))
  reads := fun _ _ _ => {posT}
  accept := fun _ y τ => orT τ == y 0

def linkP (Y : Type) : InteractiveOracleProof Y (twoExternalStrings 1 Bool) where
  shape := [rL]
  blinded := fun _ => false
  extReads := fun _ _ => ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1))
  reads := fun _ _ _ => ∅
  accept := fun _ y τ => (plL τ).1 == xor (y.1 0) (y.2 0)

def sessP (Y : Type) : InteractiveOracleProof Y (oneExternalString 1 Bool) where
  shape := [rB1, rB2]
  blinded := fun _ => false
  extReads := fun _ _ => ({0} : Finset (Fin 1))
  reads := fun _ _ _ => ∅
  accept := fun _ y τ => ((plB1 τ).1.1 == y 0) && (plB2 τ == chB1 τ 0 1)

/-- The session's marks: round 1 is local and only the slot sends; round 2 is shared and only the
shared part is sent. -/
def annB : RoundSplits [rB1, rB2] :=
  ((RAnn.ofSlot .lo rB1, (RAnn.ofShared .sh rB2, PUnit.unit)) :
    RAnn rB1 × (RAnn rB2 × PUnit))

/-! ## Honest sides and simulators -/

/-- the bit of an index; that of the index out of range is 0 -/
def bit (i : Option Bool) : Bool := i.getD false

/-- the private inputs -/
abbrev WT : Type := Option Bool × (Bool × Bool) × Bool
abbrev WL : Type := Option Bool × ((Bool × Bool) × Bool) × ((Bool × Bool) × Bool)
abbrev WB : Type := Option Bool × (Bool × Bool) × Bool × ℕ

def sideT (Y : Type) : Honest (testP Y) WT where
  Coin := Bool
  ext := fun w _ => xor (bit w.1) w.2.1.1
  strat := fun w _ κ =>
    (((xor (bit w.1) w.2.1.1, κ), fun _ => ()) : (Bool × Bool) × (Unit → Unit))
  Bad := ∅
  Hid := fun w _ => {_ρ | w.1 = none}

def sideL (Y : Type) : Honest (linkP Y) WL where
  Coin := Bool
  ext := fun w => (fun _ => xor (bit w.1) w.2.1.1.1, fun _ => xor (bit w.1) w.2.2.1.1)
  strat := fun w _ κ =>
    ((((), (xor (xor (bit w.1) w.2.1.1.1) (xor (bit w.1) w.2.2.1.1), κ)), fun _ => ()) :
      (Unit × (Bool × Bool)) × (Unit → Unit))
  Bad := ∅
  Hid := fun w _ => {_ρ | w.1 = none}

def sideB (Y : Type) : Honest (sessP Y) WB where
  Coin := Bool
  ext := fun w _ => xor (bit w.1) w.2.1.1
  strat := fun w _ κ =>
    ((((), ((xor (bit w.1) w.2.1.1, κ), 0)), fun c => (((), c 0 1), fun _ => ())) :
      (Unit × ((Bool × Bool) × ℕ)) × (Blk → (Unit × Bool) × (Unit → Unit)))
  Bad := ∅
  Hid := fun w _ => {_ρ | w.1 = none}

/-- the symbols of the oracle that are shown: o at its one position -/
def orcT (o : Bool) : (p : OPos [rT]) → Option (OSym [rT] p)
  | .inl _ => some o
  | .inr e => nomatch e

def viewT {Y : Type} (o κ : Bool) (ans : Fin 1 → Option Bool) : DView (testP Y) :=
  ⟨((κ, ()) : Bool × Unit), ans, orcT o⟩

def viewL {Y : Type} (pl : Bool × Bool) (ans : Fin 1 ⊕ Fin 1 → Option Bool) : DView (linkP Y) :=
  ⟨((pl, ()) : (Bool × Bool) × Unit), ans, fun _ => none⟩

def viewB {Y : Type} (pl : (Bool × Bool) × ℕ) (e : Bool) (ans : Fin 1 → Option Bool) :
    DView (sessP Y) :=
  ⟨((pl, (e, ())) : ((Bool × Bool) × ℕ) × (Bool × Unit)), ans, fun _ => none⟩

/-- It repeats the symbol that it is handed, and draws the run value. -/
def simT {Y : Type} : SimOf (testP Y) :=
  fun _ _ ans => (unif Bool).map fun κ => some (viewT ((ans (0 : Fin 1)).getD false) κ ans)

def simL {Y : Type} : SimOf (linkP Y) :=
  fun _ _ ans => (unif Bool).map fun κ =>
    some (viewL (xor ((ans (.inl 0)).getD false) ((ans (.inr 0)).getD false), κ) ans)

/-- the second bit of round 1's verifier message -/
def echoOf (ρ : Rho [rB1, rB2]) : Bool := (ρ.1 : Blk) 0 1

def simB {Y : Type} : SimOf (sessP Y) :=
  fun _ ρ ans => (unif Bool).map fun κ =>
    some (viewB (((ans (0 : Fin 1)).getD false, κ), 0) (echoOf ρ) ans)

theorem extAnsT {Y : Type} (y : Y) (ρ : Rho (testP Y).shape) (b : Bool) :
    ((testP Y).extAns y ρ fun _ => b) 0 = some b := by
  unfold InteractiveOracleProof.extAns
  exact if_pos (Finset.mem_singleton_self 0)

theorem extAnsB {Y : Type} (y : Y) (ρ : Rho (sessP Y).shape) (b : Bool) :
    ((sessP Y).extAns y ρ fun _ => b) 0 = some b := by
  unfold InteractiveOracleProof.extAns
  exact if_pos (Finset.mem_singleton_self 0)

theorem extAnsL {Y : Type} (y : Y) (ρ : Rho (linkP Y).shape) (b b' : Bool) :
    ((linkP Y).extAns y ρ (fun _ => b, fun _ => b')) (.inl 0) = some b ∧
      ((linkP Y).extAns y ρ (fun _ => b, fun _ => b')) (.inr 0) = some b' := by
  unfold InteractiveOracleProof.extAns
  exact ⟨if_pos (Finset.mem_insert_self _ _),
    if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

theorem exactT {Y : Type} (w : WT) (hw : w.1 ≠ none) (y : Y) (ρ : Rho (testP Y).shape) :
    (sideT Y).output w y ρ = simT y ρ ((testP Y).extAns y ρ ((sideT Y).ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideT Y).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun h0 => hw h0
  rw [if_neg hm]
  show _ = (unif Bool).map fun κ => some (viewT
    ((((testP Y).extAns y ρ fun _ => xor (bit w.1) w.2.1.1) 0).getD false) κ _)
  rw [extAnsT]
  refine congrArg (fun f => PMF.map f (unif Bool)) (funext fun κ => congrArg some ?_)
  obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
  show (⟨_, _, _⟩ : DView (testP Y)) = ⟨_, _, _⟩
  congr 1
  funext p
  rw [oposT_eq p]
  exact if_pos (Or.inl (Finset.mem_singleton_self posT))

theorem exactL {Y : Type} (w : WL) (hw : w.1 ≠ none) (y : Y) (ρ : Rho (linkP Y).shape) :
    (sideL Y).output w y ρ = simL y ρ ((linkP Y).extAns y ρ ((sideL Y).ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideL Y).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun h0 => hw h0
  rw [if_neg hm]
  show _ = (unif Bool).map fun κ => some (viewL
    (xor ((((linkP Y).extAns y ρ
          (fun _ => xor (bit w.1) w.2.1.1.1, fun _ => xor (bit w.1) w.2.2.1.1)) (.inl 0)).getD
        false)
      ((((linkP Y).extAns y ρ
          (fun _ => xor (bit w.1) w.2.1.1.1, fun _ => xor (bit w.1) w.2.2.1.1)) (.inr 0)).getD
        false), κ) _)
  rw [(extAnsL y ρ _ _).1, (extAnsL y ρ _ _).2]
  refine congrArg (fun f => PMF.map f (unif Bool)) (funext fun κ => congrArg some ?_)
  obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
  show (⟨_, _, _⟩ : DView (linkP Y)) = ⟨_, _, _⟩
  congr 1
  funext p
  exact (no_oposL p).elim

theorem exactB {Y : Type} (w : WB) (hw : w.1 ≠ none) (y : Y) (ρ : Rho (sessP Y).shape) :
    (sideB Y).output w y ρ = simB y ρ ((sessP Y).extAns y ρ ((sideB Y).ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideB Y).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun h0 => hw h0
  rw [if_neg hm]
  show _ = (unif Bool).map fun κ => some (viewB
    (((((sessP Y).extAns y ρ fun _ => xor (bit w.1) w.2.1.1) 0).getD false, κ), 0) (echoOf ρ) _)
  rw [extAnsB]
  refine congrArg (fun f => PMF.map f (unif Bool)) (funext fun κ => congrArg some ?_)
  obtain ⟨c, c', ρ'⟩ := (ρ : Blk × Unit × Unit)
  show (⟨_, _, _⟩ : DView (sessP Y)) = ⟨_, _, _⟩
  congr 1
  funext p
  exact (no_oposB p).elim

/-- Out of range every value of the verifier's randomness is a stop. -/
theorem stopsT {Y : Type} (w : WT) (hw : w.1 = none) (y : Y) (ρ : Rho (testP Y).shape) :
    ρ ∈ (sideT Y).Hid w y := hw

theorem stopsL {Y : Type} (w : WL) (hw : w.1 = none) (y : Y) (ρ : Rho (linkP Y).shape) :
    ρ ∈ (sideL Y).Hid w y := hw

theorem stopsB {Y : Type} (w : WB) (hw : w.1 = none) (y : Y) (ρ : Rho (sessP Y).shape) :
    ρ ∈ (sideB Y).Hid w y := hw

/-! ## The verifiers accept, and decide by what is read -/

theorem acceptT {Y : Type} (w : WT) (y : Y) (κ : Bool) (ρ : Rho (testP Y).shape) :
    (testP Y).accept y ((sideT Y).ext w) (((sideT Y).strat w y κ).run ρ).1 = true := by
  obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
  show (xor (bit w.1) w.2.1.1 == xor (bit w.1) w.2.1.1) = true
  exact beq_self_eq_true _

theorem acceptL {Y : Type} (w : WL) (y : Y) (κ : Bool) (ρ : Rho (linkP Y).shape) :
    (linkP Y).accept y ((sideL Y).ext w) (((sideL Y).strat w y κ).run ρ).1 = true := by
  obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
  show (xor (xor (bit w.1) w.2.1.1.1) (xor (bit w.1) w.2.2.1.1) ==
    xor (xor (bit w.1) w.2.1.1.1) (xor (bit w.1) w.2.2.1.1)) = true
  exact beq_self_eq_true _

theorem acceptB {Y : Type} (w : WB) (y : Y) (κ : Bool) (ρ : Rho (sessP Y).shape) :
    (sessP Y).accept y ((sideB Y).ext w) (((sideB Y).strat w y κ).run ρ).1 = true := by
  obtain ⟨c, c', ρ'⟩ := (ρ : Blk × Unit × Unit)
  show ((xor (bit w.1) w.2.1.1 == xor (bit w.1) w.2.1.1) && (c 0 1 == c 0 1)) = true
  rw [beq_self_eq_true, beq_self_eq_true]
  rfl

theorem localT (Y : Type) : (testP Y).IsLocal := by
  intro x y y' τ τ' _ _ hext hrd
  show (orT τ == (show Fin 1 → Bool from y) 0) = (orT τ' == (show Fin 1 → Bool from y') 0)
  have h1 : orT τ = orT τ' := hrd posT (Finset.mem_singleton_self posT)
  have h2 : (show Fin 1 → Bool from y) 0 = (show Fin 1 → Bool from y') 0 :=
    hext (0 : Fin 1) (Finset.mem_singleton_self (0 : Fin 1))
  rw [h1, h2]

theorem localL (Y : Type) : (linkP Y).IsLocal := by
  intro x y y' τ τ' _ hpl hext _
  show ((plL τ).1 == xor (y.1 0) (y.2 0)) = ((plL τ').1 == xor (y'.1 0) (y'.2 0))
  have h1 : plL τ = plL τ' := congrArg Prod.fst hpl
  have h2 : y.1 0 = y'.1 0 := hext (.inl 0) (Finset.mem_insert_self _ _)
  have h3 : y.2 0 = y'.2 0 :=
    hext (.inr 0) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [h1, h2, h3]

theorem localB (Y : Type) : (sessP Y).IsLocal := by
  intro x y y' τ τ' hρ hpl hext _
  show (((plB1 τ).1.1 == (show Fin 1 → Bool from y) 0) && (plB2 τ == chB1 τ 0 1)) =
    (((plB1 τ').1.1 == (show Fin 1 → Bool from y') 0) && (plB2 τ' == chB1 τ' 0 1))
  have h1 : plB1 τ = plB1 τ' := congrArg Prod.fst hpl
  have h2 : plB2 τ = plB2 τ' := congrArg (fun z : ((Bool × Bool) × ℕ) × (Bool × Unit) => z.2.1) hpl
  have h3 : chB1 τ = chB1 τ' := congrArg (fun z : Blk × (Unit × Unit) => z.1) hρ
  have h4 : (show Fin 1 → Bool from y) 0 = (show Fin 1 → Bool from y') 0 :=
    hext (0 : Fin 1) (Finset.mem_singleton_self (0 : Fin 1))
  rw [h1, h2, h3, h4]

/-! ## The object -/

def pad2 : HolographicProtocol (Option Bool) Unit where
  wordLength := 1
  Symbol := Bool
  EncodingRandomness := Bool × Bool
  encodeIndex := fun i r _ => xor (bit i) r.1
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i r s => xor (bit i && s) r.2
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => some (some false)
  offline := testP _
  link := linkP _
  maxBatchSize := 1
  onlineBatch := ⟨sessP _, annB⟩
  honestOfflineProver := sideT _
  honestLinkProver := sideL _
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w _ => xor (bit w.1) w.2.1.1,
                               strat0 := fun _ _ =>
                                 (((), fun _ => (((), false), fun _ => ())) :
                                   Unit × (Unit → (Unit × Bool) × (Unit → Unit))),
                               strat := fun _ _ _ _ =>
                                 ((((), ((false, false), 0)), fun _ => ((), fun _ => ())) :
                                   (Unit × ((Bool × Bool) × ℕ)) × (Blk → Unit × (Unit → Unit))),
                               Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- Each verifier reads one position of an encoded index; the encoding hides, at both seeds and at
all three indices. -/
theorem pad2_readsG (b : ℕ) : ReadsG pad2 (fun _ => True) b 1 1 1 1 where
  cntT := fun _ _ => card_le_one_fin _
  cntLp := fun _ _ => by
    show (({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).filter fun p => p.isLeft).card ≤ 1
    decide
  cntLc := fun _ _ => by
    show (({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).filter fun p => p.isRight).card ≤ 1
    decide
  cntO := fun _ _ => card_le_one_fin _
  hidE := fun S _ s _ i i' => pad_reads.hidE S (card_le_one_fin S) s (bit i) (bit i')

end Hiop.Seeded.Two

#print axioms Hiop.Seeded.Two.exactT
#print axioms Hiop.Seeded.Two.exactL
#print axioms Hiop.Seeded.Two.exactB
#print axioms Hiop.Seeded.Two.stopsB
#print axioms Hiop.Seeded.Two.acceptB
#print axioms Hiop.Seeded.Two.localB
#print axioms Hiop.Seeded.Two.pad2_readsG
