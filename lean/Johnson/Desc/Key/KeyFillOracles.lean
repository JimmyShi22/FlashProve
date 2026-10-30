-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- ShownAt of Johnson/Desc/Sound/MsgSig.lean is written Sound.ShownAt, to tell it from the tables' own Key.ShownAt.
/-
Johnson/Desc/Key/KeyFillOracles.lean: FROM PLAIN STRINGS TO THE RULE OF COMPOSITION's OWN ORACLES: what Johnson/Desc/Key/KeyFillStrs.lean | KeyFillNoColl.lean show at some y : Strs stands at strsOf Fr y' for some y' : Fr.E.Str (strsOf:
Johnson/Desc/Sound/MsgAt.lean), where the frame holds each member's tree at its depth.
  posL_spec · posL_isSome   the library's posL (OnBytes/Maker/Stage.lean): a position that it gives spells the tree's number and the leaf; it gives one where the list holds the number at a depth that reaches the leaf
  pull Fr y₀ y              the rule's oracles PULLED BACK from plain strings: at the position ⟨i, x⟩ the column of the tree with i's number at leaf x; the stored table's side is y₀'s
  colAt_pull · wordOf_pull  wherever posL gives a position, colAt | wordOf read the plain strings' own column | word. NOTHING ONE-TO-ONE IS ASKED: a position spells the only (tree, leaf) that reaches it
  FrameHolds                PUBLIC: for each member the frame's list holds its tree's number at a depth of at least aOf
  exists_oracles            R14: seat injective · SeatFits · FrameHolds ⟹ ONE y' : Fr.E.Str (its stored table's side any) such that AT strsOf Fr y' every member's leaves are shown, its word is below 2 ^ a the raw word of f i, and symsW reads f i
  fam_at_word               the common heart, with the strings a letter: shown and read as f i at every member ⟹ a Member, hasSmp and NoColl at every member
  fam_promise_at_oracles    PIN ∧ hasSmp ∧ NoColl at all seats AT strsOf Fr y', at a witness whose tables at the seats are the messages' (a premise)
  fam_promise_form_at_oracles   under public premises alone; at a sample's tie that reads no record and IS MADE OF THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS («meets» by fiat), and at a silly laying (the second table)
  Toy.holds · Toy.not_holds (A PLANT: the frame holds the tree too shallow) · Toy.promise_at_oracles (closed)
«famStrs = strsOf Fr y'» AS Strs IS NOT CLAIMED AND NOT MEANT: a frame is one chain's; a told tree that it lacks is empty in strsOf.
OBJECT: strsOf | colAt (Johnson/Desc/Sound/MsgAt.lean); the library's posL · USER: Johnson/Desc/Key/KeyFillLay.lean · LETTERS: Fr · F · cs · l · seat · y₀ · f · seedIs · a · W.
NOT SAID: that (a, y') lies in a boundary's condition (in front of its sending a tree holds empty columns there); that behind a sending's block the prover's oracle is this; that a real description's frames hold its trees at their depths.
At l := [] all is true for nothing. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillNoCollAt
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob OnBytes.Maker

/-! ## The library's posL -/

theorem posL_spec (L : List LeftT) (j x : ℕ) (p : PosL L) (h : posL L j x = some p) : (L.get p.1).no = j ∧ p.2.val = x := by
  unfold posL at h
  obtain ⟨i, _, hi⟩ := List.exists_of_findSome?_eq_some h
  by_cases h1 : (L.get i).no = j
  · rw [if_pos h1] at hi
    by_cases h2 : x < 2 ^ (L.get i).a
    · rw [dif_pos h2] at hi
      obtain rfl := Option.some.inj hi
      exact ⟨h1, rfl⟩
    · rw [dif_neg h2] at hi
      exact nomatch hi
  · rw [if_neg h1] at hi
    exact nomatch hi

theorem posL_isSome (L : List LeftT) (j x : ℕ) (k : Fin L.length) (hno : (L.get k).no = j) (hx : x < 2 ^ (L.get k).a) : (posL L j x).isSome = true := by
  by_contra hn
  have hnone : posL L j x = none := Option.not_isSome_iff_eq_none.1 hn
  unfold posL at hnone
  have hk := List.findSome?_eq_none_iff.1 hnone k (List.mem_finRange k)
  rw [if_pos hno, dif_pos hx] at hk
  exact nomatch hk

/-! ## The pull-back -/

/-- **The rule's oracles, pulled back from plain strings.** -/
def pull (Fr : Frame) (y₀ : Fr.E.Str) (y : Strs) : Fr.E.Str := (y₀.1, fun p : PosL Fr.all => y.col (Fr.all.get p.1).no p.2.val)

theorem colAt_pull (Fr : Frame) (y₀ : Fr.E.Str) (y : Strs) (j x : ℕ) (h : (posL Fr.all j x).isSome = true) : colAt Fr (pull Fr y₀ y) j x = y.col j x := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hp
  show ((posL Fr.all j x).map (pull Fr y₀ y).2).getD [] = _
  rw [hp]
  show y.col (Fr.all.get p.1).no p.2.val = y.col j x
  rw [h1, h2]

theorem wordOf_pull {XI : Type} (F : FileDescription XI) (Fr : Frame) (y₀ : Fr.E.Str) (y : Strs) (j t x : ℕ) (h : (posL Fr.all j x).isSome = true) :
    wordOf F (strsOf Fr (pull Fr y₀ y)) j t x = wordOf F y j t x := by
  show ((F.oracleAt j).bind fun o => o.cut t (colAt Fr (pull Fr y₀ y) j x)) = ((F.oracleAt j).bind fun o => o.cut t (y.col j x))
  rw [colAt_pull Fr y₀ y j x h]

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

/-- **The frame holds each member's tree at its depth**: on the frame and the plan's letters alone. -/
def FrameHolds (Fr : Frame) : Prop :=
  ∀ i : Fin l.length, ∃ k : Fin Fr.all.length, (Fr.all.get k).no = (seat i).1 ∧ aOf cs (l.get i).1 ≤ (Fr.all.get k).a

variable {XI : Type} (F : FileDescription XI)

/-- **R14: ONE y' OF THE RULE's OWN TYPE SERVES ALL MEMBERS.** -/
theorem exists_oracles (Fr : Frame) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (hFr : FrameHolds cs l seat Fr) (y₀ : Fr.E.Str)
    (f : ∀ i : Fin l.length, (OmAt cs l i).Str) :
    ∃ y' : Fr.E.Str, y'.1 = y₀.1 ∧ ∀ i : Fin l.length, Sound.ShownAt F cs l seat (strsOf Fr y') i ∧
      (∀ k, k < 2 ^ aOf cs (l.get i).1 → wordOf F (strsOf Fr y') (seat i).1 (seat i).2 k = rawOf cs (l.get i).1 (l.get i).2 (f i) k) ∧
      symsW cs (l.get i).1 (l.get i).2 (wordOf F (strsOf Fr y') (seat i).1 (seat i).2) = f i := by
  refine ⟨pull Fr y₀ (famStrs cs l seat F (fun _ => none) f), rfl, fun i => ?_⟩
  obtain ⟨k, hno, hle⟩ := hFr i
  have hw : ∀ x, x < 2 ^ aOf cs (l.get i).1 →
      wordOf F (strsOf Fr (pull Fr y₀ (famStrs cs l seat F (fun _ => none) f))) (seat i).1 (seat i).2 x = rawOf cs (l.get i).1 (l.get i).2 (f i) x := fun x hx =>
    (wordOf_pull F Fr y₀ _ _ _ x (posL_isSome _ _ _ k hno (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hle)))).trans
      (wordOf_famStrs cs l seat F hinj hS (fun _ => none) f i x hx)
  obtain ⟨_, _, _, _, _, _, _, hm, _, _⟩ := hS i
  refine ⟨fun x hx => ?_, hw, ?_⟩
  · rw [hw x hx]
    exact rawOf_shown cs _ _ (f i) x hx
  · rw [symsW_of_agree cs _ _ _ _ hw]
    exact symsW_rawOf cs _ _ hm (f i)

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

/-- **THE COMMON HEART, WITH THE STRINGS A LETTER.** -/
theorem fam_at_word (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (a : A) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hf : ∀ i, (OmAt cs l i).upW (f i) = (OmAt cs l i).C.enc (m₀ i) (r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (y : Strs) (hy : ∀ i, Sound.ShownAt F cs l seat y i ∧ symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2) = f i) (i : Fin l.length) :
    (∃ o z, F.oracleAt (seat i).1 = some o ∧ (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z ∧
        Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 (m₀ i))) ∧
      hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true ∧
      NoColl F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y := by
  obtain ⟨hsh, hsy⟩ := hy i
  obtain ⟨o, _, ho, _, hlog, _, _, hm, _, _⟩ := hS i
  have hL : ∀ o', F.oracleAt (seat i).1 = some o' → o'.logLength = aOf cs (l.get i).1 := fun o' ho' => by
    obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact hlog
  have hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2)) = (OmAt cs l i).C.enc (m₀ i) (r₀ i) := by
    rw [hsy]
    exact hf i
  obtain ⟨hh, hn⟩ := fam_noColl_honest cs l seat F seedIs arr lay decT recOf hinj i hL hm (uniq i) _ _ (allMeet_sound cs l hB i) a y (m₀ i) (r₀ i) (ρ i) _ (hs i) hw
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hh
  exact ⟨⟨o, z, ho, hz, fam_honest_member cs l seat F seedIs arr lay decT recOf hinj i hL hm (uniq i) a y o z (m₀ i) (r₀ i) (ρ i) ho hz (hs i) hsh hw⟩, hh, hn⟩

/-- **PIN AND ITS PROMISE AT ALL SEATS, AT THE RULE's OWN ORACLES.** -/
theorem fam_promise_at_oracles {Tok : Type} (Fr : Frame) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (hFr : FrameHolds cs l seat Fr)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (W : Wit Cells Tok Tab) (hW : ∀ i, msgOf (famG cs l seat seedIs arr lay decT recOf) W (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ y' : Fr.E.Str, y'.1 = y₀.1 ∧ ∀ i : Fin l.length, PIN F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a (strsOf Fr y') W ∧
      hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true ∧
      NoColl F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a (strsOf Fr y') := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  obtain ⟨y', h1, hy⟩ := exists_oracles cs l seat F Fr hinj hS hFr y₀ f
  refine ⟨y', h1, fun i => ?_⟩
  obtain ⟨⟨o, z, ho, hz, hM⟩, hh, hn⟩ := fam_at_word cs l seat F seedIs arr lay decT recOf hinj hS uniq hB a f m₀ r₀ ρ hf hs (strsOf Fr y')
    (fun i => ⟨(hy i).1, (hy i).2.2⟩) i
  refine ⟨⟨o, z, ho, hz, ?_⟩, hh, hn⟩
  rw [hW i]
  exact hM

/-- **UNDER PUBLIC PREMISES ALONE, AT THE RULE's OWN ORACLES**: at a tie made of the message itself and a silly laying. -/
theorem fam_promise_form_at_oracles (recOf' : Unit → Option Rec) (c₀ : Cells) (Fr : Frame) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (hFr : FrameHolds cs l seat Fr) (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length,
        PIN F (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf') (seat i).1 (seat i).2 () (strsOf Fr y') W ∧
        hasSmp (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf') (seat i).1 (seat i).2 () = true ∧
        NoColl F (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf') (seat i).1 (seat i).2 () (strsOf Fr y') := by
  have hu : ∀ (i : Fin l.length) (a : Unit) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i)) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) (m₀ i)) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  refine ⟨fun i _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i), hu, padW cs l seat c₀ m₀, ?_⟩
  exact fam_promise_at_oracles cs l seat F _ arr (fun _ _ _ p => p) decT recOf' Fr hinj hS hFr hu hB y₀ () m₀ r₀ ρ hsend (fun i => ⟨rfl, rfl⟩) (padW cs l seat c₀ m₀)
    (msgOf_padW cs l seat _ arr decT recOf' hinj c₀ m₀)

end

/-! ## The toy -/

namespace Toy

/-- A frame that holds the tree number 0 at the depth d; no stored table to speak of. -/
def FrD (d : ℕ) : Frame := ⟨0, [⟨0, d⟩], fun _ => 0, 0⟩

theorem holds : FrameHolds cs l seat (FrD 1) := by
  rintro ⟨k, hk⟩
  have hk' : k < 2 := hk
  interval_cases k
  · exact ⟨⟨0, Nat.zero_lt_one⟩, rfl, Nat.le_of_eq rfl⟩
  · exact ⟨⟨0, Nat.zero_lt_one⟩, rfl, Nat.le_of_eq rfl⟩

/-- **A PLANT: the frame holds the tree too shallow.** -/
theorem not_holds : ¬ FrameHolds cs l seat (FrD 0) := by
  intro h
  obtain ⟨⟨k, hk⟩, _, hle⟩ := h ⟨0, by decide⟩
  have hk' : k < 1 := hk
  interval_cases k
  exact Nat.not_succ_le_zero 0 hle

/-- **CLOSED: AT THE TOY, PIN · hasSmp · NoColl AT BOTH MEMBERS, AT THE RULE's OWN ORACLES.** -/
theorem promise_at_oracles {Rec : Type} (arr : ℕ → ℕ → ℕ) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Unit) (recOf : Unit → Option Rec) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
        PIN (FW 15) (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () (strsOf (FrD 1) y') W ∧
        hasSmp (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () = true ∧
        NoColl (FW 15) (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () (strsOf (FrD 1) y') := by
  obtain ⟨sd, hu, W, y', _, h⟩ := fam_promise_form_at_oracles cs l seat (FW 15) arr decT recOf () (FrD 1) seat_inj fits holds meets
    ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (fun _ _ => 1) (fun _ _ => 0) (fun _ => Classical.arbitrary _)
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)
  exact ⟨sd, hu, W, y', h⟩

end Toy

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.posL_spec
#print axioms VerifiableInference.Desc.Key.Fill.posL_isSome
#print axioms VerifiableInference.Desc.Key.Fill.colAt_pull
#print axioms VerifiableInference.Desc.Key.Fill.wordOf_pull
#print axioms VerifiableInference.Desc.Key.Fill.exists_oracles
#print axioms VerifiableInference.Desc.Key.Fill.fam_at_word
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_at_oracles
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_form_at_oracles
#print axioms VerifiableInference.Desc.Key.Fill.Toy.holds
#print axioms VerifiableInference.Desc.Key.Fill.Toy.not_holds
#print axioms VerifiableInference.Desc.Key.Fill.Toy.promise_at_oracles
