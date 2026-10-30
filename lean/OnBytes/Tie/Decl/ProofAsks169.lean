-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/ProofAsks169.lean: which strings of calls with the number 169 the asking half of a
proof file's typing asks: no string but those of the calls that hash the parameter bytes of the
three chains.

OnBytes/Tie/Decl/PinUnseen.lean names that law (`ProofOnly169`) and proves what it buys. Here it is
proved, after the pattern of OnBytes/Tie/EntryAsks169.lean (the entry's reading) and over its two
frames (OnBytes/ChecksWithHashAsArgument/M/Chain/EngineKeepsAt.lean, OnBytes/ChecksWithHashAsArgument/M/Entry/RoadKeepsAt.lean): a
property of computations that pure and bind keep passes through the twin's reader of a chain, if
every call of the hash under a number other than 169 has it, and the call under 169 on the
description's parameter bytes. The frame is carried on through the place in the binding tree, the
tail and the proof file. Statements and proofs.

Main names:
  `okR_need_bind`: in a lawful monad: behind a step that takes the value of an option, the rest is
    asked only at that value.
  `ok_climbAt`, `ok_readPlaceAt`, `okR_readTailAt`, `okR_readProofAt`: the frame, at letters.
  `keeps3 p₁ p₂ p₃`: "every string of a call with the number 169 that is asked is the string of the
    call on p₁, p₂ or p₃", as a property that pure and bind keep.
  `proofOnly169`: THE LAW: `ProofOnly169` holds of every asking half.
  `pin_unseen_all`: so: with the property "a call with the number 169", under EVERY family g at
    whose three strings the table holds g's own values, the pinned asking half has the value of the
    asking half itself. No premise but the three equations.
Limits: on every path, whatever the oracle answers. Nothing on how often these strings are asked, on
the other strings, or on values. Nothing on the reading of a key file. No probability. Nothing on
soundness.

-/
import OnBytes.Tie.Decl.PinUnseen
import OnBytes.Tie.EntryAsks169
import OnBytes.ChecksWithHashAsArgument.M.Model.SpineKeeps

set_option autoImplicit false

namespace OnBytes.Tie

section Frame

open OnBytes.Proof hiding climb readPlace Reading need Reading.fromStart readerName readNamed
    requestItem readTail readProof check
open OnBytes.TwoPort.M OnBytes.TwoPort.M.Proof
open OnBytes.Params

variable {m : Type → Type} [Monad m] (k : Keeps m)

/-- Behind a step that takes the value of an option, the rest is asked only at that value. -/
theorem okR_need_bind [LawfulMonad m] {α β : Type} (why : String) {x : Option α}
    {g : α → Reading m β} (hg : ∀ a, x = some a → OkR k (g a)) : OkR k (need why x >>= g) := by
  intro s
  rw [Reading.run_bind]
  unfold need
  simp only [ExceptT.run_mk, pure_bind]
  cases x with
  | none => exact k.ok_pure _
  | some a => exact hg a rfl s

variable (h : HashM m) (hh : ∀ n t i s b, n % 65536 ≠ 169 → k.ok (h n t i s b))
include hh

theorem ok_climbAt (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat), k.ok (climb h cfg b levels x p i)
  | 0, _, _, _ => k.ok_pure _
  | levels + 1, x, p, i => by
    unfold climb
    split
    · exact k.ok_pure _
    · dsimp only
      split <;>
        exact k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun _ => ok_climbAt cfg b levels _ _ _

theorem ok_readPlaceAt (s : LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    k.ok (readPlace h s cfg closing b i) := by
  unfold readPlace
  split
  · exact k.ok_pure _
  · split
    · exact k.ok_pure _
    · split
      · exact k.ok_pure _
      · split
        · exact k.ok_pure _
        · refine k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun leaf => ?_
          exact k.ok_bind _ _ (ok_climbAt k h hh _ _ _ _ _ _) fun _ => k.ok_pure _

theorem okR_readTailAt [LawfulMonad m] (p : TailPublic) (dry : FirstEnd) (first : ChainRead)
    (b : ByteArray) (h2 : k.ok (h 169 0 1 Fmt.zero32 p.shared.given.bytes))
    (h3 : k.ok (h 169 0 1 Fmt.zero32 p.second.given.bytes)) :
    OkR k (readTail h p dry first b) := by
  unfold readTail
  dsimp only
  refine okR_bind k (RoadKeeps.ok_need k _ _) fun seal1 => ?_
  refine okR_bind k (RoadKeeps.ok_needM k _ _ (ok_readPlaceAt k h hh _ _ _ _ _)) fun place => ?_
  refine okR_bind k (RoadKeeps.ok_needM k _ _ (RoadKeepsAt.ok_tableKey k h hh _ _ _ _ _))
    fun key => ?_
  refine okR_bind k (RoadKeeps.ok_need k _ _) fun x => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine okR_need_bind k _ fun spec2 e2 => ?_
  have p2 : spec2.base.params = p.shared.given.bytes := RoadKeepsAt.params_of_describe e2
  refine okR_bind k (RoadKeepsAt.ok_readNamed k h hh _ spec2 _ _ (p2 ▸ h2)) fun shared => ?_
  refine okR_bind k (RoadKeeps.ok_need k _ _) fun seal2 => ?_
  refine okR_bind k (RoadKeeps.ok_need k _ _) fun rounds3 => ?_
  refine okR_need_bind k _ fun spec3 e3 => ?_
  have p3 : spec3.base.params = p.second.given.bytes := RoadKeepsAt.params_of_describe e3
  refine okR_bind k (RoadKeepsAt.ok_readNamed k h hh _ spec3 _ _ (p3 ▸ h3)) fun second => ?_
  exact okR_pure k _

theorem okR_readProofAt [LawfulMonad m] (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray)
    (h1 : k.ok (h 169 0 1 Fmt.zero32 c.first.given.bytes))
    (h2 : k.ok (h 169 0 1 Fmt.zero32 c.shared.given.bytes))
    (h3 : k.ok (h 169 0 1 Fmt.zero32 c.second.given.bytes)) :
    OkR k (readProof h c table copy request words block file) := by
  unfold readProof
  dsimp only
  split <;> refine okR_bind k (by first | exact okR_throw k _ | exact okR_pure k _) fun x => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine SpineKeeps.okR_guard k _ fun _ => ?_
    refine SpineKeeps.okR_guard k _ fun _ => ?_
    refine okR_bind k (RoadKeeps.ok_need k _ _) fun x => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine okR_need_bind k _ fun spec1 e1 => ?_
    have p1 : spec1.base.params = c.first.given.bytes := RoadKeepsAt.params_of_describe e1
    refine okR_bind k (RoadKeepsAt.ok_readNamed k h hh _ spec1 _ _ (p1 ▸ h1)) fun first => ?_
    refine okR_bind k (okR_readTailAt k h hh (tailPublic c table) _ _ _ h2 h3) fun r => ?_
    exact SpineKeeps.okR_guard k _ fun _ => okR_pure k _

end Frame

open OnBytes.TwoPort
open OnBytes.Slice (IsCall169)
open OnBytes.Params (TableName ProofChains)
open OnBytes.Proof (FirstEnd ProofRead)
open _root_.Run (bytesToBits)

/-- "Every string of a call with the number 169 that is asked is the string of the call on p₁, p₂ or
p₃": pure has the property, and bind keeps it. -/
def keeps3 (p₁ p₂ p₃ : ByteArray) : M.Keeps (ZKCP.OComp 256) where
  ok := fun x => (Rom.toRom x).AsksIn fun _ s =>
    IsCall169 s → s = strPar p₁ ∨ s = strPar p₂ ∨ s = strPar p₃
  ok_pure := fun _ => trivial
  ok_bind := fun x g hx hg => by
    show (Rom.toRom (x.bind g)).AsksIn _
    rw [Rom.toRom_bind]
    exact Rom.OComp.AsksIn.bind hg hx

/-- A call of the asking hash under a number other than 169 has the property. -/
theorem ok3_HM (p₁ p₂ p₃ : ByteArray) (n t i : ℕ) (st bs : ByteArray) (hn : n % 65536 ≠ 169) :
    (keeps3 p₁ p₂ p₃).ok (Fmt.HM Run.askB n t i st bs) := by
  unfold Fmt.HM
  split
  · exact (keeps3 p₁ p₂ p₃).ok_bind _ _
      ⟨fun h => absurd h (not169 _ _ _ _ _ _ hn), fun _ => trivial⟩ fun _ =>
      (keeps3 p₁ p₂ p₃).ok_bind _ _
        ⟨fun h => absurd h (not169 _ _ _ _ _ _ hn), fun _ => trivial⟩ fun _ =>
        (keeps3 p₁ p₂ p₃).ok_pure _
  · exact ⟨fun h => absurd h (not169 _ _ _ _ _ _ hn), fun _ => trivial⟩

/-- The call that hashes p has the property, if p is one of the three. -/
theorem ok3_digest (p₁ p₂ p₃ p : ByteArray) (hp : p = p₁ ∨ p = p₂ ∨ p = p₃) :
    (keeps3 p₁ p₂ p₃).ok (Fmt.HM Run.askB 169 0 1 Fmt.zero32 p) := by
  unfold Fmt.HM
  rw [if_neg (by decide)]
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  rcases hp with e | e | e
  · exact Or.inl (by rw [e]; rfl)
  · exact Or.inr (Or.inl (by rw [e]; rfl))
  · exact Or.inr (Or.inr (by rw [e]; rfl))

/-- **THE LAW.** -/
theorem proofOnly169 {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains)
    (table : TableName) (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) : ProofOnly169 asm c table copy request words block file := by
  have e : (keeps3 c.first.given.bytes c.shared.given.bytes c.second.given.bytes).ok
      (typedP asm c table copy request words block file) := by
    unfold typedP askedP
    refine (keeps3 _ _ _).ok_bind _ _ ((keeps3 _ _ _).ok_bind _ _
      (okR_readProofAt (keeps3 _ _ _) _ (ok3_HM _ _ _) c table copy request words block file
        (ok3_digest _ _ _ _ (Or.inl rfl)) (ok3_digest _ _ _ _ (Or.inr (Or.inl rfl)))
        (ok3_digest _ _ _ _ (Or.inr (Or.inr rfl))) Session.start) fun r => ?_) fun _ =>
      (keeps3 _ _ _).ok_pure _
    cases r <;> exact (keeps3 _ _ _).ok_pure _
  exact e

/-- **So the pin is not seen**, under every family at whose three strings the table holds the
family's own values. -/
theorem pin_unseen_all {Out : Type} [DecidablePred IsCall169] (asm : ProofRead → Option Out)
    (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) (T : List Bool → _root_.Iop.Dig 256)
    (g : Rom.Fam (Rom.rom 256))
    (h1 : T (strPar c.first.given.bytes) = g () (strPar c.first.given.bytes))
    (h2 : T (strPar c.shared.given.bytes) = g () (strPar c.shared.given.bytes))
    (h3 : T (strPar c.second.given.bytes) = g () (strPar c.second.given.bytes)) :
    (pinP IsCall169 T (typedPR asm c table copy request words block file)).det g =
      (typedPR asm c table copy request words block file).det g :=
  pin_unseen asm c table copy request words block file
    (proofOnly169 asm c table copy request words block file) T g h1 h2 h3

end OnBytes.Tie

#print axioms OnBytes.Tie.proofOnly169
#print axioms OnBytes.Tie.pin_unseen_all
