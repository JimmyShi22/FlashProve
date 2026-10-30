-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttChain.lean: STEPS ON THE CHAIN's SHAPE THAT READ NOTHING OF THE TABLES THAT
look AND lookHeard CARRY. stripC, the shape's part of strip; BlindS f: f commutes with it; the laws by
which such steps are put together; and the steps behind the batching and at the clearing of an
attention link.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.AtFull.Shape.Scope.Sim
import Johnson.AtFull.Shape.LettersAtX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims.Law.Tests (lsTailG lsTailU testsGC partB behindG)
open VerifiableInference.Desc.K9.Shape (gTw)

variable {X X₀ : Verify.Public}

/-- The chain's shape with no table of a call in look and lookHeard. -/
def stripC (c : ChainSh) : ChainSh :=
  ChainSh.mk c.marked c.here c.tl c.led c.tables c.rowsOwed c.core c.reply c.indexMasks c.pile
    c.atEnd c.check c.link (c.look.map stripH) (c.lookHeard.map stripH) c.own c.head c.att c.fin

theorem strip_is (a : ShA) : strip a = (stripC a.1, a.2) := rfl

theorem relC {a a' : ShA} (h : RelX X X₀ a a') : stripC a.1 = stripC a'.1 := by
  have e := h.eq
  rw [strip_is, strip_is] at e
  exact congrArg Prod.fst e

theorem rel_of {a a' : ShA} (h : stripC a.1 = stripC a'.1) (f : a.2 = a'.2) : RelX X X₀ a a' := by
  unfold RelX
  rw [strip_is, strip_is, h, f]

/-- The step reads nothing of the tables, and leaves them. -/
def BlindS (f : ChainSh → Except String ChainSh) : Prop :=
  ∀ c, f (stripC c) = (f c).map stripC

/-- A blind step goes alike. -/
theorem blind_alike {f : ChainSh → Except String ChainSh} (hf : BlindS f) {a a' : ShA}
    (h : RelX X X₀ a a') : Alike (RelX X X₀) (liftQ f a) (liftQ f a') := by
  have e : (f a.1).map stripC = (f a'.1).map stripC := by
    rw [← hf, ← hf, relC h]
  unfold liftQ
  cases h1 : f a.1 with
  | error x =>
    cases h2 : f a'.1 with
    | error y => exact Or.inr ⟨rfl, rfl⟩
    | ok c' =>
      rw [h1, h2] at e
      cases e
  | ok c =>
    cases h2 : f a'.1 with
    | error y =>
      rw [h1, h2] at e
      cases e
    | ok c' =>
      rw [h1, h2] at e
      have ec : stripC c = stripC c' := by
        have := Except.ok.inj e
        exact this
      exact Or.inl ⟨_, _, rfl, rfl, rel_of ec h.forms⟩

theorem blind_bind {f g : ChainSh → Except String ChainSh} (hf : BlindS f) (hg : BlindS g) :
    BlindS fun c => (f c).bind g := by
  intro c
  show (f (stripC c)).bind g = ((f c).bind g).map stripC
  rw [hf]
  cases f c with
  | error e => rfl
  | ok x =>
    show g (stripC x) = (g x).map stripC
    exact hg x

theorem blind_if {p : ChainSh → Bool} (hp : ∀ c, p (stripC c) = p c)
    {f : ChainSh → Except String ChainSh} (hf : BlindS f) (e : String) :
    BlindS fun c => if p c then f c else .error e := by
  intro c
  show (if p (stripC c) then f (stripC c) else .error e) = (if p c then f c else .error e).map stripC
  rw [hp]
  split
  · exact hf c
  · rfl

theorem lsTailU_strip (c : ChainSh) : lsTailU (stripC c) = stripC (lsTailU c) := by
  obtain ⟨m, h, tl, led, tb, ro, co, rp, im, pl, ae, ck, lk, lo, lh, ow, hd, at', fi⟩ := c
  cases tl <;> cases led <;> rfl

theorem lsTailG_blind : BlindS lsTailG := by
  intro c
  unfold lsTailG
  have e : partB (stripC c) = partB c := rfl
  rw [e]
  split
  · show Except.ok (lsTailU (stripC c)) = Except.ok (stripC (lsTailU c))
    rw [lsTailU_strip]
  · rfl

theorem testsGC_blind (nU : Array Nat) : BlindS (testsGC nU) := by
  intro c
  obtain ⟨m, h, tl, led, tb, ro, co, rp, im, pl, ae, ck, lk, lo, lh, ow, hd, at', fi⟩ := c
  cases tl with
  | none => rfl
  | some t =>
    cases led with
    | none => rfl
    | some L =>
      cases tb with
      | none => rfl
      | some fs =>
        show (VerifiableInference.Desc.First.TailClaims.Law.Tests.testsG nU t L).map _ =
          ((VerifiableInference.Desc.First.TailClaims.Law.Tests.testsG nU t L).map _).map _
        cases VerifiableInference.Desc.First.TailClaims.Law.Tests.testsG nU t L <;> rfl

theorem behindG_blind {gT : ChainSh → Bool} (hT : ∀ c, gT (stripC c) = gT c) (nU : Array Nat) :
    BlindS (behindG gT nU) := by
  have := blind_if hT (blind_bind lsTailG_blind (testsGC_blind nU))
    "the tests behind the adding: the shape"
  exact this

theorem gTw_strip (w) (c : ChainSh) : gTw w (stripC c) = gTw w c := rfl

theorem stripC_mk (m h tl led tb ro co rp im pl ae ck lk lo lh ow hd at' fi) : stripC (ChainSh.mk m h tl led tb ro co rp im pl ae ck lk lo lh ow hd at' fi) =
    ChainSh.mk m h tl led tb ro co rp im pl ae ck lk (lo.map stripH) (lh.map stripH) ow hd at' fi := rfl

theorem chain_eta (c : ChainSh) : c = ChainSh.mk c.marked c.here c.tl c.led c.tables c.rowsOwed c.core
    c.reply c.indexMasks c.pile c.atEnd c.check c.link c.look c.lookHeard c.own c.head c.att c.fin := rfl

theorem sC_setRowsOwed (c : ChainSh) (v) : (stripC c).setRowsOwed v = stripC (c.setRowsOwed v) := by
  obtain ⟨m, h, tl, led, tb, ro, co, rp, im, pl, ae, ck, lk, lo, lh, ow, hd, at', fi⟩ := c
  rfl
theorem sC_setLed (c : ChainSh) (v) : (stripC c).setLed v = stripC (c.setLed v) := by
  obtain ⟨m, h, tl, led, tb, ro, co, rp, im, pl, ae, ck, lk, lo, lh, ow, hd, at', fi⟩ := c
  rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.blind_alike
#print axioms Johnson.AtFull.Shape.Scope.behindG_blind
