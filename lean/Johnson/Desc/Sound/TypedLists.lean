-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/TypedLists.lean: THE KEY FILE'S NAMED HYPOTHESIS ON SOUNDNESS FROM THREE TYPED
LISTS OF PROVED BLOCKS, ONE FOR EACH HASH CHAIN, AND TIES OF THE FOLD'S BLOCKS TO THEM.

The setting. The library has the key file's protocol as three typed lists of bare blocks, one for
each chain, from the joint "the stored table decodes with the record" through two joints to the end
(`KObj.KThree`, Johnson/E/KObj/KeyThree.lean). `KeySoundOfBlocks` (Johnson/Desc/Sound/KeyRule.lean)
speaks of a key file whose decision is the three folds in a row, and leaves the conditions and
relations at the boundaries as parameters.

What is said.
  `RL St W A Z`: typed blocks in a row from the joint A to the joint Z, each joint with a reading of
    the chain's statements (St) and of the chain's witness (W) at it.
  `RL.on`, `RL.rel`: the conditions and relations at the chain's boundaries, by the boundary's
    number, WRITTEN as the typed joints', read.
  `RL.Ties L ps`: the list has as many typed blocks as the chain has blocks; each typed block is
    good; each block of the chain is tied to its typed block (`PieceTie`,
    Johnson/Desc/Sound/TypedRow.lean).
  `eachGoodOfLists`: then the chain meets the premise of the rule of composition (`EachGood`).
  `BK.pass`, `BK.pass_good`: the typed block that hands its statement on: the partner of a block of
    the fold that has no typed partner (a seal).
  `KeyLists`, `KeyLists.Tied`: three such lists in a row, with what is asked: the ties; across a
    chain's end the two readings agree (equations).
  `KeySoundOfLists`, `keySoundOfLists`: at lists from `jWf` to `jEnd` whose first reading gives back
    the instance and the stored table: with `Three.Fits`, `RowFit` and the errors' size:
    `CompilerSoundnessConditionStatements.keySound`.
Trials: `ties_trial_short`, `ties_trial_long`: a chain with fewer or with more blocks than the list
  has no ties; those of Johnson/Desc/Sound/TypedRow.lean for one block.

Limits. A rule: no block of the protocol is tied here, and nothing bounds an error. Those of
KeyRule.lean and TypedRow.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyPaid
import Johnson.Desc.Sound.TypedRow
import Johnson.E.KObj.Obj
import Ior.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace KObj
open Iop

/-- **The typed block that hands its statement on**: no round; the verifier says yes; the witness is
handed back as it is. -/
def BK.pass (A : JK) : BK A A := ⟨IOR.pure some (ExtMap.id A.E), fun _ _ w => w, ()⟩

theorem BK.pass_good (A : JK) : (BK.pass A).Good where
  point := ⟨()⟩
  isLocal := ⟨fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ q _ _ hE _ => hE q (Finset.mem_singleton_self q)⟩
  know := by
    intro a ha
    show ∀ b w, (BK.pass A).R.red.out a () = some b → _ → A.relR a w
    intro b w hb hw
    have e : a = b := Option.some.inj hb
    subst e
    exact hw.elim id fun h => absurd ha h

end KObj

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)

/-! ## 1 Typed blocks in a row, with readings -/

/-- **Typed blocks in a row from the joint A to the joint Z**, each joint with a reading of the
chain's statements and of the chain's witness at it. -/
inductive RL (St W : Type) : JK → JK → Type 1
  | nil {A : JK} (rd : St → A.X × A.E.Str) (wr : W → A.W) : RL St W A A
  | cons {A B Z : JK} (rd : St → A.X × A.E.Str) (wr : W → A.W) (k : BK A B) (l : RL St W B Z) :
      RL St W A Z

namespace RL
variable {St W : Type}

/-- The readings at the first joint. -/
def rd0 : {A Z : JK} → RL St W A Z → St → A.X × A.E.Str
  | _, _, .nil rd _ => rd
  | _, _, .cons rd _ _ _ => rd
def wr0 : {A Z : JK} → RL St W A Z → W → A.W
  | _, _, .nil _ wr => wr
  | _, _, .cons _ wr _ _ => wr

/-- The readings at the last joint. -/
def rdZ : {A Z : JK} → RL St W A Z → St → Z.X × Z.E.Str
  | _, _, .nil rd _ => rd
  | _, _, .cons _ _ _ l => l.rdZ
def wrZ : {A Z : JK} → RL St W A Z → W → Z.W
  | _, _, .nil _ wr => wr
  | _, _, .cons _ _ _ l => l.wrZ

/-- The number of typed blocks. -/
def len : {A Z : JK} → RL St W A Z → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ _ l => l.len + 1

/-- **The condition at the boundary with the number i**: the typed joint's, read. Behind the last
joint: the last joint's. -/
def on : {A Z : JK} → RL St W A Z → ℕ → St → Prop
  | A, _, .nil rd _, _ => fun a => A.on (rd a)
  | A, _, .cons rd _ _ _, 0 => fun a => A.on (rd a)
  | _, _, .cons _ _ _ l, i + 1 => l.on i

/-- **The relation at the boundary with the number i.** -/
def rel : {A Z : JK} → RL St W A Z → ℕ → St → W → Prop
  | A, _, .nil rd wr, _ => fun a w => A.relR (rd a) (wr w)
  | A, _, .cons rd wr _ _, 0 => fun a w => A.relR (rd a) (wr w)
  | _, _, .cons _ _ _ l, i + 1 => l.rel i

theorem on_zero {A Z : JK} (L : RL St W A Z) : L.on 0 = fun a => A.on (L.rd0 a) := by
  cases L <;> rfl

theorem rel_zero {A Z : JK} (L : RL St W A Z) :
    L.rel 0 = fun a w => A.relR (L.rd0 a) (L.wr0 w) := by
  cases L <;> rfl

theorem on_len {A Z : JK} (L : RL St W A Z) : L.on L.len = fun a => Z.on (L.rdZ a) := by
  induction L with
  | nil rd wr => rfl
  | cons rd wr k l ih => exact ih

theorem rel_len {A Z : JK} (L : RL St W A Z) :
    L.rel L.len = fun a w => Z.relR (L.rdZ a) (L.wrZ w) := by
  induction L with
  | nil rd wr => rfl
  | cons rd wr k l ih => exact ih

end RL

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **The chain's blocks are tied to the list's typed blocks, one to one**, and each typed block is
good. -/
def RL.Ties : {A Z : JK} → RL (S × F.E.Str) W A Z → List (Piece C F S Cl W) → Prop
  | _, _, .nil _ _, [] => True
  | _, _, .nil _ _, _ :: _ => False
  | _, _, .cons _ _ _ _, [] => False
  | _, _, .cons rd wr k l, p :: ps => k.Good ∧ PieceTie p k rd l.rd0 wr l.wr0 ∧ l.Ties ps

theorem RL.ties_len : ∀ {A Z : JK} (L : RL (S × F.E.Str) W A Z) (ps : List (Piece C F S Cl W)),
    L.Ties ps → ps.length = L.len
  | _, _, .nil _ _, [], _ => rfl
  | _, _, .nil _ _, _ :: _, h => h.elim
  | _, _, .cons _ _ _ _, [], h => h.elim
  | _, _, .cons _ _ _ l, _ :: ps, h => congrArg (· + 1) (l.ties_len ps h.2.2)

/-- The premise of the rule of composition, with the boundaries' numbers moved by one. -/
theorem eachGood_shift (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ),
      EachGood (fun j => on (j + 1)) (fun j => R (j + 1)) i l → EachGood on R (i + 1) l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1, eachGood_shift on R l (i + 1) h.2⟩

/-- **A chain that is tied to a list of good typed blocks meets the premise of the rule of
composition**, at the typed joints' conditions and relations, read. -/
theorem eachGoodOfLists : ∀ {A Z : JK} (L : RL (S × F.E.Str) W A Z)
    (ps : List (Piece C F S Cl W)), L.Ties ps → EachGood L.on L.rel 0 ps
  | _, _, .nil _ _, [], _ => trivial
  | _, _, .nil _ _, _ :: _, h => h.elim
  | _, _, .cons _ _ _ _, [], h => h.elim
  | A, _, .cons rd wr k l, p :: ps, h => by
    refine ⟨?_, eachGood_shift _ _ ps 0 (eachGoodOfLists l ps h.2.2)⟩
    have g := goodOfTie p k rd l.rd0 wr l.wr0 h.1 h.2.1
    show (p.bk (fun a => A.on (rd a)) (l.on 0) (fun a w => A.relR (rd a) (wr w)) (l.rel 0)).Good
    rw [l.on_zero, l.rel_zero]
    exact g

/-- A chain with fewer blocks than the list has no ties. -/
theorem ties_trial_short {A Z : JK} (L : RL (S × F.E.Str) W A Z) (ps : List (Piece C F S Cl W))
    (h : ps.length < L.len) : ¬ L.Ties ps := fun ht => by
  rw [L.ties_len ps ht] at h
  exact Nat.lt_irrefl _ h

/-- Nor has a chain with more. -/
theorem ties_trial_long {A Z : JK} (L : RL (S × F.E.Str) W A Z) (ps : List (Piece C F S Cl W))
    (h : L.len < ps.length) : ¬ L.Ties ps := fun ht => by
  rw [L.ties_len ps ht] at h
  exact Nat.lt_irrefl _ h

/-! ## 2 Three lists in a row -/

section
variable {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ : Type}

/-- **Three typed lists in a row for a file's three chains**, from the joint A through J₁ and J₂ to
the joint Z. -/
structure KeyLists (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (A Z : JK) : Type 1 where
  J₁ : JK
  J₂ : JK
  L₁ : RL (S₁ × (EAll D all).Str) W A J₁
  L₂ : RL (S₂ × (EAll D all).Str) W J₁ J₂
  L₃ : RL (S₃ × (EAll D all).Str) W J₂ Z

variable {T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W} {A Z : JK}

/-- **The conditions and relations at all boundaries, written.** -/
def KeyLists.places (K : KeyLists T A Z) : Places D all S₁ S₂ S₃ W :=
  ⟨K.L₁.on, K.L₁.rel, K.L₂.on, K.L₂.rel, K.L₃.on, K.L₃.rel⟩

/-- What is asked of the three lists. -/
structure KeyLists.Tied (K : KeyLists T A Z) : Prop where
  tie₁ : RL.Ties (F := frameAt D all D.key₁ T.ft₁) K.L₁ (T.p₁ :: T.l₁)
  tie₂ : RL.Ties (F := frameAt D all D.key₂ T.ft₂) K.L₂ (T.p₂ :: T.l₂)
  tie₃ : RL.Ties (F := frameAt D all D.key₃ T.ft₃) K.L₃ (T.p₃ :: T.l₃)
  /-- what the second chain's first statement is read as, is what the first chain's last is -/
  seam₁ : ∀ x b, K.L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2) = K.L₁.rdZ b
  /-- the witness is read alike on both sides of the seam -/
  wit₁ : ∀ w, K.L₂.wr0 w = K.L₁.wrZ w
  /-- the like at the third chain's first statement, where it has one -/
  seam₂ : ∀ x b s, T.in₃ (T.out₂ x b.1) = some s → K.L₃.rd0 (s, b.2) = K.L₂.rdZ b
  wit₂ : ∀ w, K.L₃.wr0 w = K.L₂.wrZ w
  /-- where the last test says yes, the last joint's relation holds of the last witness -/
  last : ∀ x b, T.fin x b.1 = true → Z.relR (K.L₃.rdZ b) (K.L₃.wrZ T.wEnd)

theorem KeyLists.Tied.len₁ {K : KeyLists T A Z} (h : K.Tied) : 1 + T.l₁.length = K.L₁.len := by
  have e := RL.ties_len (F := frameAt D all D.key₁ T.ft₁) K.L₁ _ h.tie₁
  rw [List.length_cons] at e
  omega
theorem KeyLists.Tied.len₂ {K : KeyLists T A Z} (h : K.Tied) : 1 + T.l₂.length = K.L₂.len := by
  have e := RL.ties_len (F := frameAt D all D.key₂ T.ft₂) K.L₂ _ h.tie₂
  rw [List.length_cons] at e
  omega
theorem KeyLists.Tied.len₃ {K : KeyLists T A Z} (h : K.Tied) : 1 + T.l₃.length = K.L₃.len := by
  have e := RL.ties_len (F := frameAt D all D.key₃ T.ft₃) K.L₃ _ h.tie₃
  rw [List.length_cons] at e
  omega

/-- The relations at the chains' ends fit together. -/
theorem KeyLists.Tied.glued {K : KeyLists T A Z} (h : K.Tied) : T.Glued K.places where
  glue₁ := by
    intro x b w hm
    have h' : orOff (K.L₂.on 0) (K.L₂.rel 0) (T.in₂ (T.out₁ x b.1), b.2) w := hm
    rw [K.L₂.on_zero, K.L₂.rel_zero] at h'
    show orOff (K.L₁.on (1 + T.l₁.length)) (K.L₁.rel (1 + T.l₁.length)) b w
    rw [h.len₁, K.L₁.on_len, K.L₁.rel_len]
    have h2 : K.J₁.relR (K.L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2)) (K.L₂.wr0 w) ∨
        ¬ K.J₁.on (K.L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2)) := h'
    rw [h.seam₁ x b, h.wit₁ w] at h2
    exact h2
  glue₂ := by
    intro x b w hm
    obtain ⟨s, hs, hm⟩ := hm
    have h' : orOff (K.L₃.on 0) (K.L₃.rel 0) (s, b.2) w := hm
    rw [K.L₃.on_zero, K.L₃.rel_zero] at h'
    show orOff (K.L₂.on (1 + T.l₂.length)) (K.L₂.rel (1 + T.l₂.length)) b w
    rw [h.len₂, K.L₂.on_len, K.L₂.rel_len]
    have h2 : K.J₂.relR (K.L₃.rd0 (s, b.2)) (K.L₃.wr0 w) ∨ ¬ K.J₂.on (K.L₃.rd0 (s, b.2)) := h'
    rw [h.seam₂ x b s hs, h.wit₂ w] at h2
    exact h2
  ends := by
    intro x b hb
    show orOff (K.L₃.on (1 + T.l₃.length)) (K.L₃.rel (1 + T.l₃.length)) b T.wEnd
    rw [h.len₃, K.L₃.on_len, K.L₃.rel_len]
    exact Or.inl (h.last x b hb)

end

/-! ## 3 The key file -/

/-- **The key file's hypothesis on soundness, from three typed lists of good blocks and ties.** The
lists go from the library's joint in front of a key file's protocol (`jWf`: no collision; decodes)
to its end (`jEnd`). -/
def KeySoundOfLists : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (K : KeyLists T (jWf Kc.conf) jEnd)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (hf : T.Fits),
    K.Tied →
    (∀ rec y, K.L₁.rd0 (T.in₁ rec, (y, fun _ => [])) = (rec, y)) →
    RowFit (DK.at a) all all →
    Err.Below (Err.timesShared (2 ^ Tl.W.depthReqT) (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).ann
      ((T.row tFk tJk t3k yes₂ yes₂ yes₂).links
        (T.snd tFk tJk t3k K.places yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃)).err) U.εs →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U)

theorem keySoundOfLists : KeySoundOfLists := by
  intro a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N early late
    all S₁ S₂ S₃ X₁ X₂ Cl W T K P Tl U hf hK hfirst hfit below
  exact keySoundOfBlocks a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP
    eL N early late all S₁ S₂ S₃ X₁ X₂ Cl W T K.places yes₂ yes₂ yes₂ hf.shape₁
    hf.shape₂ hf.shape₃ P Tl U hf
    (eachGoodOfLists (F := frameAt (DK.at a) all (DK.at a).key₁ T.ft₁) K.L₁ _ hK.tie₁)
    (eachGoodOfLists (F := frameAt (DK.at a) all (DK.at a).key₂ T.ft₂) K.L₂ _ hK.tie₂)
    (eachGoodOfLists (F := frameAt (DK.at a) all (DK.at a).key₃ T.ft₃) K.L₃ _ hK.tie₃)
    hK.glued hfit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun rec y h => by
      have h' : K.L₁.on 0 (T.in₁ rec, (y, fun _ => [])) →
          ∃ w, K.L₁.rel 0 (T.in₁ rec, (y, fun _ => [])) w := h
      rw [K.L₁.on_zero, K.L₁.rel_zero] at h'
      have h2 : Kc.conf.free (K.L₁.rd0 (T.in₁ rec, (y, fun _ => []))) →
          ∃ w, Kc.conf.RwfR (K.L₁.rd0 (T.in₁ rec, (y, fun _ => []))) (K.L₁.wr0 w) := h'
      rw [hfirst rec y] at h2
      exact (keyL_iff Kc rec y).2 fun hfr => (h2 hfr).elim fun _ hw => hw)
    below

end VerifiableInference.Desc.Sound

#print axioms KObj.BK.pass_good
#print axioms VerifiableInference.Desc.Sound.eachGoodOfLists
#print axioms VerifiableInference.Desc.Sound.ties_trial_short
#print axioms VerifiableInference.Desc.Sound.ties_trial_long
#print axioms VerifiableInference.Desc.Sound.KeyLists.Tied.glued
#print axioms VerifiableInference.Desc.Sound.keySoundOfLists
