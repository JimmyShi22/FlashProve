-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RootsWhole.lean:
IN THE GOALS' SCOPE: THE COUNT OF ROOTS IN THE VERIFIER's STATE AT EVERY CUT OF THE
FIRST CHAIN's FLAT LIST, TO THE CHAIN's END, FROM THE FOLD's RETURN ALONE: NO PREMISE BUT THE
BLOCKS' OWN TESTS ON THE PLAN.

WHY A FILE OF ITS OWN. MsgsBehind.lean's theorems take K1Told or K2Told.

The statement "the piece's base is the number of trees that the state has
counted" wants the roots alone. So: the roots' steps stand here; MsgsPlaces.lean and
MsgsBehind.lean import this file and call it. UNTURNED: step_of_cuts, front_len (out
of MsgsPlaces.lean) and flat_len (out of MsgsBehind.lean).
  step_of_cuts: between two cuts next to each other the fold takes the block's step. flat_len: 358.
      front_len: 353 blocks stand in front of the blocks behind the last link.
  finish_yes: **354, the proximity test: what the fold's own step gives**: the kind's block passes
      its test on the plan · the place is the maker's (proximityTestParametersAt … Ps) and does not send its own first
      mask · where the state in front stands at the finish the mask is noted (K12's mask_of_step at
      the step's yes) · the lot's own decision accepts between the fold's two states · the block's
      rounds and told oracles are the lot's. (The lines of Johnson/IMR/RootsEnd.lean's proof, here
        under a
      name; RootsEnd.lean keeps its own.)
  roots_behind_step: **353 ≤ j < 358 · c.blocksInOrder[j]? = some b · b.planOk = true · the fold's returns r₀
      at j and r₁ at j + 1 ⇒ r₁.1.roots = r₀.1.roots + rootsOf b.rounds.** 353: k2_roots through
      alone_step · 354: K12's atFinish_roots · 355, 356: K13's atM3_roots, atM4_roots_w ·
      357: the state is handed back.
  roots_at_cut_whole: **k ≤ 358 · every block of c.blocksInOrder.take k passes its test on the plan ·
      foldBlocks ft (c.blocksInOrder.take k) s R C = .ok r ⇒ r.1.roots = s.roots + rootsOf (declOf
      (c.blocksInOrder.take k))**, at every ft and every first state s.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope.
User: BaseIsRoots.lean; MsgsBehind.lean. Letters: none.
OVER WHICH FILES: RootsEnd.lean and what it imports; PlacesScope.lean, BackSeat.lean,
SealSeat.lean. Compiled with the whole library.
Limits. In scope alone (the numbers 353 to 358 are this folder's back_numbers and places_scope). No
member. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.RootsEnd
import Johnson.IMR.PlacesScope
import Johnson.IMR.SealSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First hiding Col
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts atFinish)
open Johnson.G.OfPlan (rootsOf)
open ProofFile (Cl)

/-- Between two cuts next to each other the fold takes the block's step. -/
theorem step_of_cuts {ft j : Nat} {l : List (Block S Cl)} {b : Block S Cl} (hb : l[j]? = some b)
    {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (l.take j) s rs cols = .ok r₀)
    (f₁ : foldBlocks ft (l.take (j + 1)) s rs cols = .ok r₁) :
    ∃ n, b.step ft r₀.1 (r₀.2.1.take b.rounds.length) r₀.2.2 = .ok (r₁.1, n) := by
  rw [List.take_add_one, hb] at f₁
  obtain ⟨u, r, q, g0, g1⟩ := Keeps.foldBlocks_split ft [b] _ _ _ _ _ f₁
  rw [f₀] at g0
  cases g0
  obtain ⟨-, t', k, hstep, h3⟩ := foldBlocks_cons_ok.1 g1
  simp only [foldBlocks, Except.ok.injEq] at h3
  subst h3
  exact ⟨k, hstep⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem flat_len (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.blocksInOrder.length = 358 := by
  rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]

/-- In scope 353 blocks stand in front of the blocks behind the last link. -/
theorem front_len (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (Meaning.K2.frontOf c).length = 353 := by
  have h1 : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]
  have e := (seat_frontP carriedAll_roots seatCarry_roots O (oksAt_all _ _)).1
  rw [e, List.length_append] at h1
  have h2 : (Meaning.K2.backOf c).length = 5 := by
    unfold Meaning.K2.backOf
    rw [List.length_append, List.length_map, (IM.back_of O).1]
    rfl
  omega

/-- **354, THE PROXIMITY TEST AT THE FIRST CHAIN's FINISH: WHAT THE FOLD's OWN STEP GIVES**: the
kind's block passes its test on the plan; the place is the maker's and does not send its own first
mask; where the state in front stands at the finish the mask is noted; the lot's own decision
accepts between the fold's two states; the block's rounds and told oracles are the lot's. -/
theorem finish_yes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {ft : Nat} {s : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl}
    (hb : c.blocksInOrder[354]? = some b) (hp : b.planOk = true) {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take 354) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (354 + 1)) s R C = .ok r₁) :
    (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Block T12 Unit).planOk = true ∧
      (H2U.p12OfMade Z.made).nums.ownMask = false ∧
      (∃ Ps, H2U.p12OfMade Z.made = H2U.proximityTestParametersAt ⟨1, none, 2, .K12⟩ Ps) ∧
      (∀ fo, r₀.1.here = .fin fo → fo.mask.isSome = true) ∧
      (∃ rs gs, (atFinish (H2U.p12OfMade Z.made)).decide r₀.1 rs gs = .ok r₁.1) ∧
      b.rounds = (atFinish (H2U.p12OfMade Z.made)).rounds ∧
      b.oracles = (atFinish (H2U.p12OfMade Z.made)).oracles := by
  obtain ⟨-, ⟨k1, k1', e1, -, eb1, hl1⟩, -, -⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 1 k1 e1).symm.trans hb)
  rw [List.take_add_one, hb] at f₁
  obtain ⟨u, rs₀, cols₀, g0, g1⟩ := Keeps.foldBlocks_split ft [_] _ _ _ _ _ f₁
  rw [f₀] at g0
  cases g0
  obtain ⟨hlen, t', k, hstep, h3⟩ := foldBlocks_cons_ok.1 g1
  simp only [foldBlocks, Except.ok.injEq] at h3
  subst h3
  -- the block's test on the plan; the place is the maker's; first arm
  have hpk : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Block T12 Unit).planOk = true := by
    have a1 : (k1.planOk && k1.hasNoClaimsAndNothingAfter) = true := hp
    rw [Bool.and_eq_true] at a1
    have a2 : k1'.planOk = true := by rw [← IM.alone_planOk hl1]; exact a1.1
    rw [eb1] at a2
    exact VerifiableInference.Desc.K12.Seat.atFinish_planOk _ (IM.retype_planOk _ a2).1
  obtain ⟨Ps, hX⟩ : ∃ Ps, H2U.placesOfMade Z.made = .ok Ps := by
    cases hX : H2U.placesOfMade Z.made with
    | error e =>
      exfalso
      have hp' := hpk
      unfold H2U.p12OfMade at hp'
      rw [hX] at hp'
      simp [proximityTestKind, H2U.noP12] at hp'
    | ok Ps => exact ⟨Ps, rfl⟩
  have ep : H2U.p12OfMade Z.made = H2U.proximityTestParametersAt ⟨1, none, 2, .K12⟩ Ps.L := by
    unfold H2U.p12OfMade
    rw [hX]
  have ho : (H2U.p12OfMade Z.made).nums.ownMask = false := by
    have hp' := hpk
    rw [ep] at hp' ⊢
    rw [H2K.Made.nums_of_planOk _ _ hp']
    exact places_L_own hX
  have r1 : k1.rounds = (atFinish (H2U.p12OfMade Z.made)).rounds := by
    rw [IM.alone_rounds hl1, eb1]
    rfl
  have s1 := ((IM.step_alone hl1 (fun e => nomatch e) ft u t' k _ _).mp hstep).1
  rw [eb1] at s1
  obtain ⟨fo, t'', hfo, -, -, hk, -⟩ :=
    VerifiableInference.Desc.K12.Seat.atFinish_step _ ft u t' _ _ k s1
  have y1 := (Block.step_ok.1 s1).2.2.1
  have hmask : fo.mask ≠ none := by
    obtain ⟨-, hr'⟩ := H2K.Made.seat_pays guardedProximityTestParts _ hpk (atFinish (H2U.p12OfMade Z.made))
      (H2K.Made.keeps_atFinish _)
    obtain ⟨-, -, -, Rr, -, -, er⟩ := H2K.Made.rounds_top _ _ hr'
    dsimp only at hlen hk
    rw [r1, er] at hlen hk
    generalize List.take (List.length (_ :: Rr)) rs₀ = q at hlen hk
    cases q with
    | nil => simp at hlen
    | cons q0 rs' => exact H2K.JointK.mask_of_step _ _ t'' ft k q0 rs' _ hpk hk ho
  have hm : ∀ fo', u.here = .fin fo' → fo'.mask.isSome = true := fun fo' h' => by
    obtain rfl : fo = fo' := Here.fin.inj (hfo.symm.trans h')
    exact Option.isSome_iff_ne_none.2 hmask
  refine ⟨hpk, ho, ⟨_, ep⟩, hm, ⟨_, _, y1⟩, r1, ?_⟩
  show k1.oracles = _
  rw [IM.alone_oracles hl1, eb1]
  rfl

/-- **THE FIVE BEHIND THE LAST LINK: the count of roots grows by what the block's rounds declare.**
No premise but the block's own test on the plan and the fold's two returns. -/
theorem roots_behind_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : Nat} {s : S}
    {R : List Fmt.RoundView} {C : List OpenedColumn} {j : Nat} {b : Block S Cl} (h353 : 353 ≤ j) (h358 : j < 358)
    (hb : c.blocksInOrder[j]? = some b) (hp : b.planOk = true) {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take j) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (j + 1)) s R C = .ok r₁) :
    r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ _ _ _ _ n hstep
  obtain ⟨-, -, ⟨k2, k2', e2, -, eb2, hl2⟩, ⟨k3, k3', w, e3, -, hw, eb3, hl3⟩⟩ := IM.back_of O
  obtain rfl | rfl | rfl | rfl | rfl : j = 353 ∨ j = 354 ∨ j = 355 ∨ j = 356 ∨ j = 357 := by omega
  · obtain ⟨q0, q0', eq0, hq0, n0, a0, hlq⟩ := back_zero O
    obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 0 q0 eq0).symm.trans hb)
    exact alone_step hlq ((k2Pure_all carriedAll_roots seatCarry_roots Z Bs.G₀ (fun _ _ => trivial)
      fun _ _ _ => trivial).1 q0' hq0).1 hp _ _ _ _ hd
  · obtain ⟨hpk, ho, -, hm, ⟨rs, gs, y1⟩, er, -⟩ := finish_yes hS hR O hb hp f₀ f₁
    rw [er]
    exact VerifiableInference.Desc.K12.Coin.atFinish_roots _ hpk ho _ _ _ _ hm y1
  · obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 2 k2 e2).symm.trans hb)
    subst eb2
    have hd' : (K13.atM3 (Cl := Unit) (K13.whereOf Z)).decide r₀.1 rs' gs' = .ok r₁.1 :=
      (IM.alone_underR hl2).2 _ _ _ _ hd
    show r₁.1.roots = r₀.1.roots + rootsOf k2.rounds
    rw [IM.alone_rounds hl2]
    exact K13.Law.atM3_roots hd'
  · obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 3 k3 e3).symm.trans hb)
    subst eb3
    have hd' : (K13.atM4 (Cl := Unit) (K13.whereOf Z) w).decide r₀.1 rs' gs' = .ok r₁.1 :=
      (IM.alone_underR hl3).2 _ _ _ _ hd
    show r₁.1.roots = r₀.1.roots + rootsOf k3.rounds
    rw [IM.alone_rounds hl3]
    exact K13.Law.atM4_roots_w hw hd'
  · obtain ⟨kL, -, ebL, hlL⟩ := IM.seal_seated O
    obtain rfl := Option.some.inj ((IM.back_numbers hS hR O).2.symm.trans hb)
    subst ebL
    have hd' := (IM.alone_underR hlL).2 _ _ _ _ hd
    obtain ⟨_, -, e⟩ := Keeps.emap_ok hd'
    have e0 : rootsOf c.last.rounds = 0 := by
      rw [IM.alone_rounds hlL]
      rfl
    show r₁.1.roots = r₀.1.roots + rootsOf c.last.rounds
    rw [e0, ← e]
    rfl

/-- **IN THE GOALS' SCOPE: THE COUNT OF ROOTS AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST, TO ITS
END**: from any first state, at any number of the first tree. -/
theorem roots_at_cut_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (ft : Nat) (s : S)
    (R : List Fmt.RoundView) (C : List OpenedColumn) :
    ∀ (k : Nat), k ≤ 358 → (∀ b ∈ c.blocksInOrder.take k, b.planOk = true) →
      ∀ r : S × List Fmt.RoundView × List OpenedColumn, foldBlocks ft (c.blocksInOrder.take k) s R C = .ok r →
        r.1.roots = s.roots + rootsOf (H2K.First.declOf (c.blocksInOrder.take k)) := by
  intro k
  induction k with
  | zero => exact fun _ hp r h => roots_at_cut_paid O 0 (Nat.zero_le _) hp ft s R C r h
  | succ k ih =>
    intro hk hp r h
    by_cases hf : k + 1 ≤ 353
    · exact roots_at_cut_paid O (k + 1) (by rw [front_len hS hR O]; exact hf) hp ft s R C r h
    · obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[k]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [flat_len hS hR O]; omega)⟩
      have e : c.blocksInOrder.take (k + 1) = c.blocksInOrder.take k ++ [b] := by
        rw [List.take_add_one, hb]
        rfl
      have h' := h
      rw [e] at h'
      obtain ⟨t₀, r₀, c₀, f₀, -⟩ := Keeps.foldBlocks_split ft [b] _ _ _ _ _ h'
      have i3 := ih (by omega) (fun x hx => hp x (by rw [e]; exact List.mem_append_left _ hx)) _ f₀
      have a3 := roots_behind_step hS hR O (by omega) (by omega) hb
        (hp b (by rw [e]; exact List.mem_append_right _ List.mem_cons_self)) f₀ h
      rw [a3, i3, e]
      show _ = s.roots + rootsOf ((c.blocksInOrder.take k ++ [b]).flatMap (·.rounds))
      rw [List.flatMap_append, H2K.First.rootsOf_append]
      simp [H2K.First.declOf, Nat.add_assoc]

#print axioms finish_yes
#print axioms roots_behind_step
#print axioms roots_at_cut_whole

end Meaning.Carry
