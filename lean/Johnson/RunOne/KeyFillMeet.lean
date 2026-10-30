-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- The proof of promise_at₁ is general in the source (promise_atG, with «every leaf is shown» beside) and promise_at₁ is a call of it.
/-
Johnson/RunOne/KeyFillMeet.lean: THE MEETING: THE FILLING IN THE WOVEN TABLES' READING, AT THE KEY FILE's OWN DESCRIPTION AND SEATS. Other files (not named here) hold a member of PIN · hasSmp · NoColl at the key file's own description and stored public files, at fillG (Johnson/Desc/Key/KeyFill.lean), one tenant at a time;
Johnson/RunOne/KeyFillSeed.lean holds the tables' one reading filled (baseK), at a family, under premises on the plan. Here the two are laid together, at the first chain.
  FitsAt · HoldsAt           Sound.SeatFits (Johnson/Desc/Sound/MsgSig.lean) | KeyFillOracles.lean's FrameHolds AT ONE MEMBER · fitsAt_of_noFault: Sound.seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean) ends at FitsAt to the letter
  wordOf_famStrs_at · oracles_at   the ONE y' := pull Fr y₀ (famStrs …) serves member i wherever FitsAt i ∧ HoldsAt i: nothing is asked of the other members
  promise_atG                THE ONE THEOREM, GENERAL IN THE SOURCE (the chain's records A · recOf' · src): ShownAt ∧ PIN ∧ hasSmp ∧ NoColl at the reading gAt: the three chains' readings are calls of it (Johnson/RunOne/KeyFillChains.lean)
  promise_at₁                promiseK_h₁ WITH EVERY PREMISE ON THE PLAN ASKED AT THE MEMBERS OF I ALONE (FitsAt · HoldsAt · Tie · meetsB)
  zOf | βOf · reads_of       THE RECORD AT EVERY SEED: the canonical words of a seed's coordinates and factor read as the seed
  xOf · exists_statement · stateOf   a message's record with the kind's own sample row; a statement that holds each member's at its number; the chain's start with that statement laid in
  member_h₁                  PUBLIC PREMISES ALONE ⟹ for every instance, maker's record, messages that can be sent, SEEDS and stored side: ∃ a state, a witness and oracles of the rule's own type: PIN ∧ hasSmp ∧ NoColl at B.h₁ at the seats of I
  holdsB · holdsAt_of_B      the frame's fact as a plain test on public data, for evaluation
  member_fk₁                 AT F := Key.descriptionFromSource X N P · Fr := the tables' fr₁ D · B := baseK csKey six numSix atSix … (plan₁ (oneAt X)).orc · I := the numbers 0 | 1 | 2 (seats (0,0) (1,0) (5,0)).
                             PREMISES LEFT: three «seatFaultAt … = none» · three «holdsB … = true» · 0 < the ranges' stages: SEVEN CLOSED TESTS ON PUBLIC DATA
  ToyM.member                a control: member_h₁'s premises are met together at the toy: closed
THE STATE IS A VALUE OF THE FIRST CHAIN's STATE TYPE LAID BY HAND: NOT A STATE THAT THE CHAIN's BLOCKS REACH: it meets no border's book-keeping test and none of the promise's other fields: THIS IS A MEMBER OF «PIN · hasSmp · NoColl», NOT OF A BORDER's PROMISE.
OBJECT: Key.descriptionFromSource X N P · fr₁ D · BaseSt.h₁ (Johnson/RunOne/KeyOneReading.lean) · seatFaultAt (Johnson/Desc/SeatAt.lean) · USER: imported by Johnson/Top/Fire/Code/RowsNine.lean, Johnson/RunOne/KeyFillRecord.lean · LETTERS: X N P D · decT · recOf.
NOT SAID: the three Booleans and the frame's fact at any files (evaluations; none is run here) · that the description's codes are csKey and its sendings' shapes and radii the six's · PINW · the second and third chain · an honest run. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeedToy
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.RunOne.KeyRowsAtFk

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (ReadsOne Tie sampleRow)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {XI : Type} (F : FileDescription XI)

/-- Sound.SeatFits (Johnson/Desc/Sound/MsgSig.lean), at one member. -/
def FitsAt (i : Fin l.length) : Prop :=
  ∃ o n, F.oracleAt (seat i).1 = some o ∧ o.tenants[(seat i).2]? = some n ∧
    o.logLength = aOf cs (l.get i).1 ∧ n.main = (l.get i).1.mainRows * (l.get i).1.mainDeg ∧
    n.mask = (l.get i).1.maskRows * 3 ∧
    ((l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) ∧
    (o.tenants.map fun t => t.main + t.mask).sum = o.words ∧
    ((l.get i).1.mainDeg = 1 ∨ (l.get i).1.mainDeg = 3)

theorem seatFits_iff : Sound.SeatFits F cs l seat ↔ ∀ i, FitsAt cs l seat F i := Iff.rfl

/-- **Sound.seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean) ends at FitsAt.** -/
theorem fitsAt_of_noFault (i : Fin l.length) (tag : String) (h : seatFaultAt F cs tag (l.get i).1 (seat i).1 (seat i).2 = none) : FitsAt cs l seat F i :=
  Sound.seat_of_noFault F cs tag _ _ _ h

/-- FrameHolds, at one member. -/
def HoldsAt (Fr : Sound.Frame) (i : Fin l.length) : Prop :=
  ∃ k : Fin Fr.all.length, (Fr.all.get k).no = (seat i).1 ∧ aOf cs (l.get i).1 ≤ (Fr.all.get k).a

theorem wordOf_famStrs_at (hinj : Function.Injective seat) (cell : ℕ → Option (ℕ × List UInt64)) (f : ∀ i : Fin l.length, (OmAt cs l i).Str)
    (i : Fin l.length) (hS : FitsAt cs l seat F i) (k : ℕ) (hk : k < 2 ^ aOf cs (l.get i).1) :
    wordOf F (famStrs cs l seat F cell f) (seat i).1 (seat i).2 k = rawOf cs (l.get i).1 (l.get i).2 (f i) k := by
  obtain ⟨o, n, ho, ht, hlog, hmain, hmask, hm, hsum, hdeg⟩ := hS
  obtain ⟨σ, hσ, h1, h2⟩ := rawOf_lengths cs _ _ hm hdeg (f i) k hk
  rw [hσ]
  exact wordOf_strsOfWords F cell _ ho hsum ht (by rw [hlog]; exact hk) ((famWords_seat cs l seat hinj f i k).trans hσ) (h1.trans hmain.symm) (h2.trans hmask.symm)

/-- **The one y' serves member i wherever its seat fits and the frame holds its tree.** -/
theorem oracles_at (Fr : Sound.Frame) (hinj : Function.Injective seat) (y₀ : Fr.E.Str) (f : ∀ i : Fin l.length, (OmAt cs l i).Str)
    (i : Fin l.length) (hS : FitsAt cs l seat F i) (hFr : HoldsAt cs l seat Fr i) :
    Sound.ShownAt F cs l seat (Sound.strsOf Fr (pull Fr y₀ (famStrs cs l seat F (fun _ => none) f))) i ∧
      symsW cs (l.get i).1 (l.get i).2 (wordOf F (Sound.strsOf Fr (pull Fr y₀ (famStrs cs l seat F (fun _ => none) f))) (seat i).1 (seat i).2) = f i := by
  obtain ⟨k, hno, hle⟩ := hFr
  have hw : ∀ x, x < 2 ^ aOf cs (l.get i).1 →
      wordOf F (Sound.strsOf Fr (pull Fr y₀ (famStrs cs l seat F (fun _ => none) f))) (seat i).1 (seat i).2 x = rawOf cs (l.get i).1 (l.get i).2 (f i) x := fun x hx =>
    (wordOf_pull F Fr y₀ _ _ _ x (posL_isSome _ _ _ k hno (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hle)))).trans
      (wordOf_famStrs_at cs l seat F hinj (fun _ => none) f i hS x hx)
  obtain ⟨_, _, _, _, _, _, _, hm, _, _⟩ := id hS
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hw x hx]
    exact rawOf_shown cs _ _ (f i) x hx
  · rw [symsW_of_agree cs _ _ _ _ hw]
    exact symsW_rawOf cs _ _ hm (f i)

end

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- **THE ONE THEOREM, GENERAL IN THE SOURCE**: the filling's promise at the reading gAt … recOf' src, whatever the chain's records A, its reader of the instance recOf' and its source src of the messages' records: every premise on the plan is asked at the members of I alone. -/
theorem promise_atG {A : Type} (recOf' : A → Option Rec) (src : A → ℕ → Option (OnBytes.Codes × ℕ × OnBytes.Oracle)) {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (y₀ : Fr.E.Str) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) src i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  have harr := arr_at l num at_ hinj
  obtain ⟨W, hW⟩ := (fam_hW_iff cs l (seatAt l num at_) (seedIsS cs l num (rowIsK cs l) src) (famArr l (seatAt l num at_) num) decT recOf' hinj c₀ () _).2
    (agreeOff_of_apart cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (fun i => ofU cs (l.get i).1 (l.get i).2 (m₀ i)) fun i i' e => hnum (by rw [← harr i, ← harr i', e]))
  refine ⟨W, pull Fr y₀ (famStrs cs l (seatAt l num at_) F (fun _ => none) f), rfl, fun i hi => ?_⟩
  obtain ⟨hsh, hsy⟩ := oracles_at cs l (seatAt l num at_) F Fr hinj y₀ f i (hS i hi) (hFr i hi)
  obtain ⟨o, _, ho, _, hlog, _, _, hm, _, _⟩ := id (hS i hi)
  have hL : ∀ o', F.oracleAt (seatAt l num at_ i).1 = some o' → o'.logLength = aOf cs (l.get i).1 := fun o' ho' => by
    obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact hlog
  have hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F (Sound.strsOf Fr (pull Fr y₀ (famStrs cs l (seatAt l num at_) F (fun _ => none) f))) (seatAt l num at_ i).1 (seatAt l num at_ i).2)) =
      (OmAt cs l i).C.enc (m₀ i) (r₀ i) := by
    rw [hsy]
    exact hf i
  have hu := uniq_seedIsS cs l num (rowIsK cs l) src i (uniqK cs l i (hT i hi))
  obtain ⟨hh, hn⟩ := fam_noColl_honest cs l (seatAt l num at_) F (seedIsS cs l num (rowIsK cs l) src) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT
    recOf' hinj i hL hm hu _ _ (meetsB_sound cs _ _ (hB i hi)) a _ (m₀ i) (r₀ i) (ρ i) _ (hs i hi) hw
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hh
  have hM := fam_honest_member cs l (seatAt l num at_) F (seedIsS cs l num (rowIsK cs l) src) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT
    recOf' hinj i hL hm hu a _ o z (m₀ i) (r₀ i) (ρ i) ho hz (hs i hi) hsh hw
  obtain ⟨o', x, e1, e2, _⟩ := id (hs i hi)
  have heq := smp_eq cs l (seatAt l num at_) num (rowIsK cs l) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT recOf' src hinj hap harr i a o' x e1 e2
  refine ⟨hsh, ⟨o, z, ho, heq.trans hz, ?_⟩, ?_, fun o z ho hz m m' hm hm' => hn o z ho (heq.symm.trans hz) m m' hm hm'⟩
  · show Member F (famG cs l (seatAt l num at_) (seedIsS cs l num (rowIsK cs l) src) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT recOf') o
      (seatAt l num at_ i).1 (seatAt l num at_ i).2 _ z
      (msgOf (famG cs l (seatAt l num at_) (seedIsS cs l num (rowIsK cs l) src) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT recOf') W
        (seatAt l num at_ i).1 (seatAt l num at_ i).2)
    rw [hW i]
    exact hM
  · show (smpOf cs l (rowIsK cs l) (famArr l (seatAt l num at_) num) src a (seatAt l num at_ i).1 (seatAt l num at_ i).2).isSome = true
    rw [heq]
    exact hh

/-- **promiseK_h₁ WITH EVERY PREMISE ON THE PLAN ASKED AT THE MEMBERS OF I ALONE.** -/
theorem promise_at₁ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (y₀ : Fr.E.Str) (a : Xi × FirstState) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₁_eq]
  obtain ⟨W, y', hy, h⟩ := promise_atG cs l num at_ decT (fun a : Xi × FirstState => recOf a.1) (src₁ orc₁) F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ r₀ ρ hsend hs c₀
  exact ⟨W, y', hy, fun i hi => (h i hi).2⟩

/-! ## The record, at every seed -/

/-- The canonical words of a seed's coordinates | factor. -/
def zOf (i : Fin l.length) (ρ : (OmAt cs l i).Z.D) : List OnBytes.E := List.ofFn fun t : Fin (bitsZ cs (l.get i).1) => OnBytes.E.ofTriple (ofE (ρ.1 t))
def βOf (i : Fin l.length) (ρ : (OmAt cs l i).Z.D) : OnBytes.E := OnBytes.E.ofTriple (ofE ((ρ.2 : GEˣ) : GE))

/-- **Every seed of the library's sample map is read off words.** -/
theorem reads_of (i : Fin l.length) (ρ : (OmAt cs l i).Z.D) : ReadsOne cs (l.get i).1 (zOf cs l i ρ) (βOf cs l i ρ) ρ := by
  refine ⟨le_of_eq (List.length_ofFn).symm, fun t => ?_, ?_⟩
  · show OnBytes.Slice.readE ((zOf cs l i ρ).getD t.val OnBytes.zeroE) = ρ.1 t
    have ht : t.val < (zOf cs l i ρ).length := by
      unfold zOf
      rw [List.length_ofFn]
      exact t.isLt
    rw [List.getD_eq_getElem _ _ ht]
    unfold zOf
    rw [List.getElem_ofFn, OnBytes.Slice.readE_ofTriple, toE_ofE]
  · unfold βOf
    rw [OnBytes.Slice.readE_ofTriple, toE_ofE]

/-- A message's record: the member's shape, marked, the kind's own sample row at the seed's words and the canonical words of the library's answer. -/
def xOf (i : Fin l.length) (o : ℕ) (ρ : (OmAt cs l i).Z.D) (m : (OmAt cs l i).Msg) : OnBytes.Oracle :=
  { shape := (l.get i).1, sampled := true
    sampleRows := #[sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o (zOf cs l i ρ) (βOf cs l i ρ) 0 (OnBytes.E.ofTriple (ofE ((OmAt cs l i).Z.val ρ m ())))] }

theorem rowIsK_xOf (i : Fin l.length) (o : ℕ) (ρ : (OmAt cs l i).Z.D) (m : (OmAt cs l i).Msg) : rowIsK cs l i o (xOf cs l i o ρ m) ρ ((OmAt cs l i).Z.val ρ m) := by
  refine ⟨zOf cs l i ρ, βOf cs l i ρ, _, rfl, rfl, reads_of cs l i ρ, ?_⟩
  funext s
  rw [OnBytes.Slice.readE_ofTriple, toE_ofE]
  cases s
  rfl

open Classical in
/-- **A statement that holds given records at given numbers**, one-to-one on I. BETWEEN THEM STAND FILLERS: the type's default message (no rows, unsampled, no sample row): at the key file's letters the three records stand at 0 · 1 · 1 + 2 · stages. -/
theorem exists_statement (I : Fin l.length → Prop) (no : Fin l.length → ℕ) (hno : ∀ i i', I i → I i' → no i = no i' → i = i') (x : Fin l.length → OnBytes.Oracle) :
    ∃ St : OnBytes.Statement, St.codes = cs ∧ ∀ i, I i → St.oracles[no i]? = some (x i) := by
  let N : ℕ := (Finset.univ.sup no) + 1
  let g : Fin N → OnBytes.Oracle := fun k => if h : ∃ i, I i ∧ no i = k.val then x h.choose else default
  refine ⟨{ codes := cs, oracles := (List.ofFn g).toArray }, rfl, fun i hi => ?_⟩
  have hlt : no i < N := Nat.lt_succ_of_le (Finset.le_sup (f := no) (Finset.mem_univ i))
  show (List.ofFn g).toArray[no i]? = some (x i)
  rw [List.getElem?_toArray, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
  have hex : ∃ i', I i' ∧ no i' = no i := ⟨i, hi, rfl⟩
  show some (if h : ∃ i', I i' ∧ no i' = no i then x h.choose else default) = some (x i)
  rw [dif_pos hex, hno _ _ hex.choose_spec.1 hi hex.choose_spec.2]

/-- The first chain's start with a statement laid in. A VALUE OF THE TYPE: no state that the blocks reach. -/
def stateOf (b : LookupRecord) (St : OnBytes.Statement) : FirstState := { chainStart cs b with d := { (chainStart cs b).d with st := St } }

/-- **PUBLIC PREMISES ALONE: A MEMBER OF PIN · hasSmp · NoColl AT B.h₁, AT EVERY MESSAGE THAT CAN BE SENT AND EVERY SEED.** -/
theorem member_h₁ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true)
    (no : Fin l.length → ℕ) (horc : ∀ i, I i → orc₁ (num i) = some (no i)) (hno : ∀ i i', I i → I i' → no i = no i' → i = i')
    (x : Xi) (b : LookupRecord) (y₀ : Fr.E.Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (c₀ : Cells) :
    ∃ (s : FirstState) (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) (Sound.strsOf Fr y') := by
  obtain ⟨St, hc, hx⟩ := exists_statement cs l I no hno fun i => xOf cs l i (no i) (ρ i) (m₀ i)
  refine ⟨stateOf cs b St, ?_⟩
  refine promise_at₁ cs l num at_ decT recOf orc₁ F I Fr hinj hap hnum hS hFr hT hB y₀ (x, stateOf cs b St) m₀ r₀ ρ hsend (fun i hi => ?_) c₀
  refine ⟨no i, xOf cs l i (no i) (ρ i) (m₀ i), ?_, rfl, rowIsK_xOf cs l i (no i) (ρ i) (m₀ i)⟩
  show (orc₁ (num i)).bind (stAt St) = some (cs, no i, xOf cs l i (no i) (ρ i) (m₀ i))
  rw [horc i hi]
  exact (stAt_eq St (no i) cs (no i) _).2 ⟨hc, rfl, hx i hi⟩

end

/-! ## The frame's fact, as a plain test -/

/-- Does the frame's list hold the tree number j at a depth of at least a. ON PUBLIC DATA ALONE: FOR EVALUATION. -/
def holdsB (Fr : Sound.Frame) (j a : ℕ) : Bool := Fr.all.any fun t => t.no == j && decide (a ≤ t.a)

theorem holdsAt_of_B (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (Fr : Sound.Frame) (i : Fin l.length)
    (h : holdsB Fr (seat i).1 (aOf cs (l.get i).1) = true) : HoldsAt cs l seat Fr i := by
  obtain ⟨t, ht, h2⟩ := List.any_eq_true.1 h
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  exact ⟨k, h2.1, h2.2⟩

/-! ## At the key file's own letters -/

section
open OnBytes.Params VerifiableInference.Desc.Sound
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)

/-- The number under which the first chain's statement holds member i's message. -/
def noSix (one : OneTime) (i : Fin six.length) : ℕ := ((KeyRows1.plan₁ one).orc (numSix i)).getD 0

theorem noSix_eq (one : OneTime) (i : Fin six.length) (hi : numSix i < 3) :
    noSix one i = if i.val = 0 then 0 else if i.val = 1 then 1 else 1 + 2 * one.ranges.stages.length := by
  obtain ⟨a, ha⟩ := i
  have h3 : a < 3 := hi
  interval_cases a <;> rfl

theorem orc_noSix (one : OneTime) (i : Fin six.length) (hi : numSix i < 3) : (KeyRows1.plan₁ one).orc (numSix i) = some (noSix one i) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (plan₁_orc_some one _ hi)
  unfold noSix
  rw [ho]
  rfl

theorem noSix_inj (one : OneTime) (hst : 0 < one.ranges.stages.length) (i i' : Fin six.length) (hi : numSix i < 3) (hi' : numSix i' < 3) (h : noSix one i = noSix one i') : i = i' := by
  rw [noSix_eq one i hi, noSix_eq one i' hi'] at h
  have h3 : i.val < 3 := hi
  have h3' : i'.val < 3 := hi'
  apply Fin.ext
  split_ifs at h <;> omega

/-- **AT THE KEY FILE's OWN DESCRIPTION, THE TABLES' OWN FRAME AND THE WOVEN TABLES' READING: A MEMBER OF PIN · hasSmp · NoColl AT THE FIRST CHAIN's THREE SEATS**, at every message that can be sent and every seed. THE RADII ARE six's: 6130 · 3131959 · 3138896 (W's: nW's, Johnson/Top/H/KeyFamilies.lean; 3145534 is, as reported, the largest at which meetsB holds, not the frame's). The tags t0 t1 t2 are any: seatFaultAt lays them into a fault's words alone. -/
theorem member_fk₁ (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (x : Xi) (b : LookupRecord) (y₀ : (fr₁ D).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i)) (c₀ : Cells) :
    ∃ (s : FirstState) (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') := by
  refine member_h₁ Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc (Fk X N P) (fun i => numSix i < 3) (fr₁ D) seat_inj_six shapesApart_six
    (fun a b h => Fin.ext h) ?_ ?_ (fun i _ => tie_six i) (fun i _ => List.all_eq_true.1 meets_six _ (List.get_mem six i))
    (noSix (oneAt X)) (fun i hi => orc_noSix (oneAt X) i hi) (fun i i' hi hi' h => noSix_inj (oneAt X) hst i i' hi hi' h) x b y₀ m₀ r₀ ρ hsend c₀
  · rintro ⟨a, ha⟩ (h3 : a < 3)
    interval_cases a
    · exact fitsAt_of_noFault _ six _ _ _ t0 n0
    · exact fitsAt_of_noFault _ six _ _ _ t1 n1
    · exact fitsAt_of_noFault _ six _ _ _ t2 n2
  · rintro ⟨a, ha⟩ (h3 : a < 3)
    interval_cases a
    · exact holdsAt_of_B _ six _ _ _ f0
    · exact holdsAt_of_B _ six _ _ _ f1
    · exact holdsAt_of_B _ six _ _ _ f2

end

/-! ## A control: the premises are met together -/

namespace ToyM
open VerifiableInference.Desc.Key.Fill.Toy
open Johnson.RunOne.KeyRows23.ToyB (num at_ apartT orcP)

/-- **CLOSED: member_h₁ AT THE TOY, at a partial plan**: for every seed and every instance. -/
theorem member (x : Xi) (b : LookupRecord) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D) :
    ∃ (s : FirstState) (W : Wit Unit Unit Fill.Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length, i.val = 0 →
      PIN (FW 15) (baseK (Rec := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) (Sound.strsOf (FrD 1) y') W ∧
      hasSmp (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) = true ∧
      NoColl (FW 15) (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s) (Sound.strsOf (FrD 1) y') := by
  obtain ⟨s, W, y', _, h⟩ := member_h₁ cs l num at_ (fun _ _ => none) (fun _ => none) orcP (FW 15) (fun i => i.val = 0) (FrD 1) seat_inj apartT Fin.val_injective
    (fun i _ => fits i) (fun i _ => holds i) (fun i _ => ToyK.tieT i) (fun i _ => List.all_eq_true.1 meets _ (List.get_mem l i))
    (fun _ => 0) (fun i hi => by
      show orcP i.val = some 0
      rw [hi]
      rfl) (fun i i' hi hi' _ => Fin.ext (hi.trans hi'.symm)) x b
    ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (fun _ _ => 1) (fun _ _ => 0) ρ (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩) ()
  exact ⟨s, W, y', h⟩

end ToyM

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.fitsAt_of_noFault
#print axioms Johnson.RunOne.KeyRows23.wordOf_famStrs_at
#print axioms Johnson.RunOne.KeyRows23.oracles_at
#print axioms Johnson.RunOne.KeyRows23.promise_atG
#print axioms Johnson.RunOne.KeyRows23.promise_at₁
#print axioms Johnson.RunOne.KeyRows23.reads_of
#print axioms Johnson.RunOne.KeyRows23.rowIsK_xOf
#print axioms Johnson.RunOne.KeyRows23.exists_statement
#print axioms Johnson.RunOne.KeyRows23.member_h₁
#print axioms Johnson.RunOne.KeyRows23.holdsAt_of_B
#print axioms Johnson.RunOne.KeyRows23.noSix_inj
#print axioms Johnson.RunOne.KeyRows23.member_fk₁
#print axioms Johnson.RunOne.KeyRows23.ToyM.member
