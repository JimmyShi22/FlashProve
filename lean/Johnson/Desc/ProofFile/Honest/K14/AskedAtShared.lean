-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AskedAtShared.lean: kind K14: WHAT THIS KIND ASKS OF THE SHARED
CHAIN's LETTERS (Asked: nine equations, Honest/K14/LettersVar.lean) HELD AGAINST THE LETTERS AT THE
IOP AS WRITTEN IN LEAN (lettersShared, Honest/Thread/SharedHead.lean), AT EVERY TYPE Wt OF WITNESSES
AND EVERY WAY ℓ TO READ THIS KIND's WORDS OFF ONE (Honest/K14/Thread2.lean: WitLens). Each of the
nine as a lemma or a named premise; Asked; and terms at which no premise is left. Statements with
their proofs; two definitions (KpOurs, kp2).

THE NINE. This kind's public parameters are qAt Zp Np: those that the IOP's maker reads out of the
planner's chains. qAt IS THE LIBRARY's (an abbreviation, Johnson/Desc/K1/Law/SitsShared.lean); IT IS
NOT DEFINED HERE: it is exported into this namespace, and the files that write "qAt" in this
namespace have it by that one line.

By unfolding, at all letters:
  at_split, at_first, at_item   (1) the two messages differ in code; (7) the first state; (8) the
                      item's number: lettersShared has the very terms
  at_bs               **(5) THE LIST OF MEMBERS IS THIS KIND's chainOf**
                      (Johnson/Desc/K14/Blocks.lean), carried to the IOP's type of claims, at the
                      planner's chains, at the two proximity tests and the closing that the IOP lays
                      (tests and last of Johnson/Desc/K12/Seat/Fill.lean)

On a letter that lettersShared leaves open: the premise is the equation itself:
  (2) Mg, (3) shape, (4) order, (6) wit   premises hMg, hsh, hord, hwit of asked_atShared. Each says
                      that the letter is what this kind's maker (mgWords, form2, InOrder, witL)
                      makes of it

On the letter keeps: lettersShared lays it BY THE MEMBER's PLACE, this kind BY THE MEMBER's NUMBER:
  KpOurs, place_to8, at_keeps   (9) under KpOurs: at the eight places of the shared chain the letter
                      Kp is this kind's clause keeps2 at the member's number. A definition: a
                      premise's form
  piece_at            the member number b of the shared chain, 1 ≤ b ≤ 8, stands at a place whose
                      piece is b
  kp2, kpOurs_kp2     a term for Kp: at a place whose piece is 1 to 8: keeps2 at that number;
                      elsewhere a letter
  kind_at, kpOurs_kpBy   **keeps laid by the place's kind** (Honest/Thread/KeepsBy.lean: kpBy) meets
                      KpOurs, where the shared chain's own family has this kind's clause, at the
                      pieces 1 to 8, AT TWO KINDS: this kind's and the sending's (two of the eight
                      places are of the sending's kind). Of the family at another kind nothing is
                      asked

Then:
  asked_atShared      **Asked at lettersShared**, under these five premises
  asked_laid          **Asked WITH NO PREMISE**, where this kind's makers are laid at the five
                      letters, over Mg₀, shape₀, rest, Kp₀ that stay free; at every ℓ
  asked_pair          the same where the witness is a pair whose second component is this kind's
                      family of words (WitLens.snd); of the first component this kind reads nothing
  at_valid            valid there is «the input is this run's, and Vd»: so a sentence on all valid
                      inputs is a sentence on the one input w, under Vd w

kp2 reads of a place the piece alone: it is meant at the shared chain's places, and lettersShared
reads Kp at no other. asked_laid AND asked_pair STAND AT Kp := kp2 ALONE. Where keeps is laid as
kpBy f₂: asked_atShared under kpOurs_kpBy; or Kp := kp2 Q sentU (kpBy f₂), which is kpBy f₂ outside
the pieces 1 to 8.

What is not claimed. That the thread at these letters holds at any run. Anything on the ten fields
that stay letters but what the premises say. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.LettersVar
import Johnson.Desc.ProofFile.Honest.Thread.SharedHead
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.K1.Law.SitsShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words InOrder)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS sharedPlaces)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (TS)
open Desc.K14 (P14 St first p14Of beforePointOf chainOf)
open Desc.K14.Honest (Inputs)

-- This kind's public parameters at the IOP as written in Lean, out of the planner's chains: the
-- library's qAt (Johnson/Desc/K1/Law/SitsShared.lean), under its own name in this namespace too.
export VerifiableInference.Desc.K1 (qAt)

/-- **AT THE EIGHT PLACES OF THE SHARED CHAIN THE LETTER keeps BY THE PLACE IS THIS KIND's CLAUSE BY
THE MEMBER's NUMBER.** It is a definition: a premise's form, on the letter Kp of lettersShared. -/
def KpOurs (Q : P14) (sentU : Array OracleNotice) (Kp : Place → St → St → Prop) : Prop :=
  ∀ b, 1 ≤ b → b ≤ 8 → ∀ x, (sharedPlaces true)[b]? = some x →
    ∀ s s', Kp x s s' ↔ keeps2 Q sentU b s s'

/-- **A term for that letter**: at a place whose piece is 1 to 8 this kind's clause at that number;
elsewhere a letter. It reads of a place the piece alone: meant at the shared chain's places. -/
def kp2 (Q : P14) (sentU : Array OracleNotice) (Kp₀ : Place → St → St → Prop) :
    Place → St → St → Prop :=
  fun x s s' => if 1 ≤ x.piece ∧ x.piece ≤ 8 then keeps2 Q sentU x.piece s s' else Kp₀ x s s'

/-- The member number b of the shared chain, 1 ≤ b ≤ 8, stands at a place whose piece is b. -/
theorem piece_at (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) (x : Place)
    (hx : (sharedPlaces true)[b]? = some x) : x.piece = b := by
  match b, h1, h8, hx with
  | 1, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 2, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 3, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 4, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 5, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 6, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 7, _, _, hx => exact (Option.some.inj hx) ▸ rfl
  | 8, _, _, hx => exact (Option.some.inj hx) ▸ rfl

/-- The term meets the premise. -/
theorem kpOurs_kp2 (Q : P14) (sentU : Array OracleNotice) (Kp₀ : Place → St → St → Prop) :
    KpOurs Q sentU (kp2 Q sentU Kp₀) := by
  intro b h1 h8 x hx s s'
  unfold kp2
  rw [piece_at b h1 h8 x hx, if_pos ⟨h1, h8⟩]

/-- The member number b of the shared chain, 1 ≤ b ≤ 8, stands at a place of this kind or of the
sending's. -/
theorem kind_at (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) (x : Place)
    (hx : (sharedPlaces true)[b]? = some x) : x.kind = .K14 ∨ x.kind = .K1 := by
  match b, h1, h8, hx with
  | 1, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl
  | 2, _, _, hx => exact (Option.some.inj hx) ▸ Or.inr rfl
  | 3, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl
  | 4, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl
  | 5, _, _, hx => exact (Option.some.inj hx) ▸ Or.inr rfl
  | 6, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl
  | 7, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl
  | 8, _, _, hx => exact (Option.some.inj hx) ▸ Or.inl rfl

/-- **So does keeps laid BY THE PLACE's KIND** (Honest/Thread/KeepsBy.lean: kpBy), where the shared
chain's own family f₂ has AT THIS KIND AND AT THE SENDING's, at each place whose piece is 1 to 8,
this kind's clause at that number. Of f₂ at another kind nothing is asked. -/
theorem kpOurs_kpBy (Q : P14) (sentU : Array OracleNotice)
    (f₂ : VerifiableInference.Desc.KindName → Place → St → St → Prop)
    (h14 : ∀ x : Place, 1 ≤ x.piece → x.piece ≤ 8 →
      ∀ s s', f₂ .K14 x s s' ↔ keeps2 Q sentU x.piece s s')
    (h1 : ∀ x : Place, 1 ≤ x.piece → x.piece ≤ 8 →
      ∀ s s', f₂ .K1 x s s' ↔ keeps2 Q sentU x.piece s s') : KpOurs Q sentU (kpBy f₂) := by
  intro b hb1 hb8 x hx s s'
  have hp := piece_at b hb1 hb8 x hx
  show f₂ x.kind x s s' ↔ _
  rcases kind_at b hb1 hb8 x hx with hk | hk
  · rw [hk, ← hp]
    exact h14 x (by omega) (by omega) s s'
  · rw [hk, ← hp]
    exact h1 x (by omega) (by omega) s s'

/-- Each of the members 0 to 8 has a place. -/
theorem place_to8 (b : Nat) (h8 : b ≤ 8) : ∃ x, (sharedPlaces true)[b]? = some x := by
  match b, h8 with
  | 0, _ => exact ⟨_, rfl⟩
  | 1, _ => exact ⟨_, rfl⟩
  | 2, _ => exact ⟨_, rfl⟩
  | 3, _ => exact ⟨_, rfl⟩
  | 4, _ => exact ⟨_, rfl⟩
  | 5, _ => exact ⟨_, rfl⟩
  | 6, _ => exact ⟨_, rfl⟩
  | 7, _ => exact ⟨_, rfl⟩
  | 8, _ => exact ⟨_, rfl⟩

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc TableKey → Prop)
  (Rd : Nat → Common W₀ Rc TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc TableKey)

/-! ## The nine equations, one by one -/

/-- (1) split: by unfolding, at all letters. -/
theorem at_split : (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
    Rd Kp w).split = true := rfl

/-- (5) **bs: THE LIST OF MEMBERS IS THE SHARED CHAIN's, at the planner's chains, at the two
proximity tests and the closing that the IOP as written in Lean lays**: by unfolding, at all
letters. -/
theorem at_bs : (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
    Rd Kp w).bs =
      ((chainOf Zp.p.chains (qAt Zp Np) (tests Np) last).retype (Cl' := ProofFile.Cl)).blocksInOrder := rfl

/-- (7) first: by unfolding, at all letters. -/
theorem at_first : (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
    Rd Kp w).first = first (qAt Zp Np).codes := rfl

/-- (8) item: by unfolding, at all letters. -/
theorem at_item : (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
    Rd Kp w).item = (qAt Zp Np).item := rfl

/-- (9) **keeps**: where the letter by the place is this kind's clause at the eight places. -/
theorem at_keeps (sentU : Array OracleNotice) (h : KpOurs (qAt Zp Np) sentU Kp) :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).keeps = keepsAll (qAt Zp Np) sentU (lettersShared Zp Np cF H N Mg shape nothingLeft order
        wit table fixed n₁ n₂ Vd Rd Kp w).keeps := by
  funext b s s'
  unfold keepsAll
  split
  · rename_i hb
    show (∀ x, (sharedPlaces true)[b]? = some x → Kp x s s') = keeps2 (qAt Zp Np) sentU b s s'
    refine propext ⟨fun g => ?_, fun g x hx => (h b hb.1 hb.2 x hx s s').2 g⟩
    obtain ⟨x, hx⟩ := place_to8 b hb.2
    exact (h b hb.1 hb.2 x hx s s').1 (g x hx)
  · rfl

/-- **What a sentence on all valid inputs is there: a sentence on the run's own input.** -/
theorem at_valid (P : Common W₀ Rc TableKey → Prop) :
    (∀ v, (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).valid v → P v) ↔ (Vd w → P w) :=
  ⟨fun h hw => h w ⟨rfl, hw⟩, fun h v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact h hV⟩

/-! ## Asked -/

variable {sentU : Array OracleNotice} {holds : Coins Bk → Common W₀ Rc TableKey → Inputs}

/-- **Asked AT lettersShared**, at every type of witnesses and every way ℓ to read it: four of the
nine equations by unfolding; (2), (3), (4), (6) are premises on its open letters Mg, shape, order,
wit: each premise is the equation itself; (9) under KpOurs. -/
theorem asked_atShared (ℓ : WitLens Wt) (hMg : Mg = fun v => mgWords ℓ (qAt Zp Np) N (Mg v))
    (hsh : shape = form2 (qAt Zp Np) shape) (hord : order = fun s => InOrder s.st)
    (hwit : wit = witL ℓ (qAt Zp Np) sentU holds wit) (hKp : KpOurs (qAt Zp Np) sentU Kp) :
    Asked ℓ
      (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
      (qAt Zp Np) sentU Zp.p.chains (tests Np) last holds where
  split := rfl
  Mg := hMg
  shape := hsh
  order := hord
  bs := rfl
  wit := hwit
  first := rfl
  item := rfl
  keeps :=
    at_keeps Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w sentU hKp

/-- **THE PREMISES CAN BE MET: Asked, WITH NO PREMISE, where this kind's makers are laid at the five
open letters**, over letters Mg₀, shape₀, rest, Kp₀ that stay free; at every ℓ. -/
theorem asked_laid (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (shape₀ : Nat → St → Bool) (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
    (Kp₀ : Place → St → St → Prop) :
    Asked ℓ (lettersShared Zp Np cF H N (fun v => mgWords ℓ (qAt Zp Np) N (Mg₀ v))
      (form2 (qAt Zp Np) shape₀) nothingLeft (fun s => InOrder s.st)
      (witL ℓ (qAt Zp Np) sentU holds rest) table fixed n₁ n₂ Vd Rd (kp2 (qAt Zp Np) sentU Kp₀) w)
      (qAt Zp Np) sentU Zp.p.chains (tests Np) last holds :=
  asked_atShared Zp Np cF H N _ _ nothingLeft _ _ table fixed n₁ n₂ Vd Rd _ w ℓ rfl
    (by
      funext b s
      show form2 (qAt Zp Np) shape₀ b s = form2 (qAt Zp Np) (form2 (qAt Zp Np) shape₀) b s
      unfold form2
      split <;> rfl)
    rfl (witL_idem ℓ (qAt Zp Np) sentU holds rest) (kpOurs_kp2 _ _ Kp₀)

/-- **AT THE PAIR**: the witness is a pair whose second component is this kind's family of words;
the first component α stays a variable, and this kind reads nothing of it. -/
theorem asked_pair (α : Type)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ (α × Words Cb.Gl.E)) (shape₀ : Nat → St → Bool)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → α × Words Cb.Gl.E)
    (Kp₀ : Place → St → St → Prop) :
    Asked (WitLens.snd α)
      (lettersShared Zp Np cF H N (fun v => mgWords (WitLens.snd α) (qAt Zp Np) N (Mg₀ v))
        (form2 (qAt Zp Np) shape₀) nothingLeft (fun s => InOrder s.st)
        (witL (WitLens.snd α) (qAt Zp Np) sentU holds rest) table fixed n₁ n₂ Vd Rd
        (kp2 (qAt Zp Np) sentU Kp₀) w)
      (qAt Zp Np) sentU Zp.p.chains (tests Np) last holds :=
  asked_laid Zp Np cF H N nothingLeft table fixed n₁ n₂ Vd Rd w (WitLens.snd α) Mg₀ shape₀ rest Kp₀

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.piece_at
#print axioms ProofFile.Honest.K14.kpOurs_kp2
#print axioms ProofFile.Honest.K14.kind_at
#print axioms ProofFile.Honest.K14.kpOurs_kpBy
#print axioms ProofFile.Honest.K14.place_to8
#print axioms ProofFile.Honest.K14.at_split
#print axioms ProofFile.Honest.K14.at_bs
#print axioms ProofFile.Honest.K14.at_first
#print axioms ProofFile.Honest.K14.at_item
#print axioms ProofFile.Honest.K14.at_keeps
#print axioms ProofFile.Honest.K14.at_valid
#print axioms ProofFile.Honest.K14.asked_atShared
#print axioms ProofFile.Honest.K14.asked_laid
#print axioms ProofFile.Honest.K14.asked_pair
