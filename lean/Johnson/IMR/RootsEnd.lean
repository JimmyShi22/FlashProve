-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RootsEnd.lean: THE SECOND LAW (the first: descPure_bookOrd, Johnson/IMR/BookPaid.lean):
at onlineDescription's value, behind a
yes of F.run: THE FIRST CHAIN's END COUNTS AS MANY ROOTS AS THE FIRST CHAIN's DECLARED ROUNDS SEND:
e₁.roots = rootsOf F.roundsDeclaredByBlocks.1, and F.roundsDeclaredByBlocks.1 = F.plans.1. NO PREMISE BUT THE MAKER's YES AND THE RUN's.
AT EVERY o.


SealLast · SpeltRoots at the plain road: NEITHER IS ASKED HERE: the first is had by seal_seated
(over ProofFile.head_seal and ProofFile's law on the last spot); THE SECOND BECAUSE THE COUNT
IN FRONT OF THE CHAIN's OWN PROXIMITY TEST ("F:2") COMES BY THE WALK, block by block
(Johnson/IMR/RootsSeat.lean), and not by K12's guard and the place's number "free": so
PlanLike, the count of rounds named "BAT" and the plain road's planner are not
spent.

Main theorems (namespace Meaning.Carry).
  roots_at_end: O : Open o pol lay KL F Z Bs base c A B · hr : F.run x v₁ v₂ v₃ = true ⇒ FOR EVERY
      e₁ with chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁:
      e₁.roots = rootsOf (c.blocksInOrder.flatMap (·.rounds)) ∧ c.blocksInOrder.flatMap (·.rounds) = Z.D.1.
  descPure_rootsDecl: IN THE FORM OF THE ROW's FIRST LAW (descPure_bookOrd, BookPaid.lean above): h
      : ProofFile.onlineDescription o pol lay KL = .ok F · hr ⇒ ∃ Z A B c e₁, ProofFile.pureRoad.pub o pol lay KL = .ok Z
      ∧ F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ chainAt … =
      .ok e₁ ∧ e₁.roots = rootsOf F.roundsDeclaredByBlocks.1 ∧ F.roundsDeclaredByBlocks.1 = F.plans.1.
  SMALL ONES. alone_step (a block that the seat lays alone over a lot's block has the lot's block's
      sentence) · back_zero (the first block behind the links is K2's lot's own, alone: by
      chain_back_any and lot_of_kind) · four · places_L_own (the maker lays the first chain's
      last test with ownMask := false).
THE ROAD. hr gives every block's test on the plan and F.roundsDeclaredByBlocks.1 = F.plans.1 (by
FileDescription.planOk_parts_of_run). The first record counts no root (start_empty). IN FRONT OF "F:2":
foldBlocks_roots over frontOf c (seat_frontP at seatCarry_roots) and "F:1" (k2Pure_all: every
block of K2's lot, wherever it stands). ACROSS "F:2": atFinish_roots; "the mask has come" by
mask_of_step (Johnson/Desc/K12/Law/MaskIffOwn.lean) AT THE STEP's YES
THAT THE FOLD HOLDS (foldBlocks_cons_ok); the
first arm by places_L_own with nums_of_planOk. BEHIND: atM3_roots,
atM4_roots_w, chainEnd_roots, through back_of and seal_seated.
EVERY "THERE IS", WALKED (descPure_rootsDecl). Z: the plain road's public part's value. A, B, c:
pinned by the equation on F as far as the first law pins them. e₁: the chain's decision's value.
OBJECT · USER · LETTERS. Object: F := ProofFile.onlineDescription o's value, c := F.first; not verify(). User:
K12's files. Letters: none.






Compiled with the whole library.
Limits. No member: that F.run ever says yes is not shown. What the number is is not said. Nothing on
the trees' numbers or on the book (the first law). Book-keeping: no draw, no error. Nothing on
soundness.
-/
import Johnson.IMR.RootsSeat
import Johnson.IMR.SealSeat
import Johnson.IMR.BookSeat
import Johnson.Desc.K12.Law.RootsAcross
import Johnson.Desc.K12.Law.MaskIffOwn
import Johnson.Desc.K12.Law.TopH
import Johnson.Desc.K12.Law.SeatKeeps
import Johnson.Desc.K12.Law.PlacesNums
import Johnson.Desc.K12.Law.MadeRounds
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts atFinish)
open Meaning.K2 (frontOf backOf)
open H2K.First (RootsStep rootsOf_append declOf foldBlocks_roots)
open Johnson.G.OfPlan (rootsOf)
open IM (LaidAlone)
open ProofFile (Cl)

/-- A block that the seat lays alone over a lot's block, as Chain.blocksInOrder lays it. -/
theorem alone_step {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) (W : PrR b') : PrR b.asBare :=
  (carried_roots fun s : S => s.roots).under
    ((bare_underP b).trans ⟨IM.alone_underR h, fun hp => IM.alone_planOk h ▸ hp,
      IM.alone_oracles h⟩) W

/-- A list of four, by its length and its members. -/
theorem four {α : Type} {l : List α} {a0 a1 a2 a3 : α} (hl : l.length = 4)
    (h0 : l[0]? = some a0) (h1 : l[1]? = some a1) (h2 : l[2]? = some a2) (h3 : l[3]? = some a3) :
    l = [a0, a1, a2, a3] := by
  apply List.ext_getElem?
  intro i
  rcases i with _ | _ | _ | _ | i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp)]

/-- The maker lays the first chain's last test as one that does not send its own first mask. -/
theorem places_L_own {m : Johnson.G.OfPlan.Made} {X : H2U.Places4}
    (h : H2U.placesOfMade m = .ok X) : X.L.nums.ownMask = false := by
  simp only [H2U.placesOfMade, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The first block behind the links is K2's lot's own, alone. -/
theorem back_zero (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ k0 b', c.back[0]? = some k0 ∧ b' ∈ (ProofFile.k2Pure Z).blocks Bs.G₀ ∧
      ∃ name a, LaidAlone ProofFile.sameReply k0 b' name a := by
  obtain ⟨-, -, -, hall⟩ := IM.base_made O.made
  obtain ⟨sv, hsv, -, hat⟩ := IM.chain_back_any hall (IM.makers_K9 Z Bs.G₀) O.places O.chain
  obtain rfl : sv = true := hsv.2 (IM.base_has_K13 O)
  obtain ⟨b, e, sp, -, L, hL, b', hb', -, ep, h⟩ := hat 0 .K2 rfl (by decide)
  obtain rfl : L = ProofFile.k2Pure Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  exact ⟨b, b', e, hb', _, _, h⟩

/-- **book_numbers_first_chain, THE SECOND LAW, AT AN OPENING OF onlineDescription: NO PREMISE BUT THE RUN's
YES.** -/
theorem roots_at_end (O : IM.Open o pol lay KL F Z Bs base c A B) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∀ e₁ : S, chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ →
      e₁.roots = rootsOf (c.blocksInOrder.flatMap (·.rounds)) ∧ c.blocksInOrder.flatMap (·.rounds) = Z.D.1 := by
  obtain ⟨h4, ⟨k1, k1', e1, -, eb1, hl1⟩, ⟨k2, k2', e2, -, eb2, hl2⟩,
    ⟨k3, k3', w, e3, -, hw, eb3, hl3⟩⟩ := IM.back_of O
  obtain ⟨k0, k0', e0, hk0, n0, a0, hl0⟩ := back_zero O
  obtain ⟨kL, -, ebL, hlL⟩ := IM.seal_seated O
  intro e₁ he
  obtain ⟨efl, hfront⟩ := seat_frontP carriedAll_roots seatCarry_roots O (oksAt_all _ _)
  have hb := four h4 e0 e1 e2 e3
  have hfl : c.blocksInOrder = (frontOf c ++ [k0.asBare]) ++
      (k1.asBare :: [k2.asBare, k3.asBare, c.last.asBare]) := by
    rw [efl]
    unfold backOf
    rw [hb]
    simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  have PP := FileDescription.planOk_parts_of_run hr
  have eF := O.desc
  subst eF
  have hpl : ∀ b ∈ c.blocksInOrder, b.planOk = true := fun b hb => (PP.blocks₁ b hb).1
  have hdecl : c.blocksInOrder.flatMap (·.rounds) = Z.D.1 := PP.decl₁
  refine ⟨?_, hdecl⟩
  have m1 : k1.asBare ∈ c.blocksInOrder := by rw [hfl]; simp
  have m2 : k2.asBare ∈ c.blocksInOrder := by rw [hfl]; simp
  have m3 : k3.asBare ∈ c.blocksInOrder := by rw [hfl]; simp
  have mL : c.last.asBare ∈ c.blocksInOrder := by rw [hfl]; simp
  -- K12's block's test on the plan; the place is the maker's; first arm
  have hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Block T12 Unit).planOk = true := by
    have a1 : (k1.planOk && k1.hasNoClaimsAndNothingAfter) = true := hpl _ m1
    rw [Bool.and_eq_true] at a1
    have a2 : k1'.planOk = true := by rw [← IM.alone_planOk hl1]; exact a1.1
    rw [eb1] at a2
    exact VerifiableInference.Desc.K12.Seat.atFinish_planOk _ (IM.retype_planOk _ a2).1
  have ho : (H2U.p12OfMade Z.made).nums.ownMask = false := by
    cases hX : H2U.placesOfMade Z.made with
    | error e =>
      exfalso
      have hp' := hp
      unfold H2U.p12OfMade at hp'
      rw [hX] at hp'
      simp [proximityTestKind, H2U.noP12] at hp'
    | ok Ps =>
      have ep : H2U.p12OfMade Z.made = H2U.proximityTestParametersAt ⟨1, none, 2, .K12⟩ Ps.L := by
        unfold H2U.p12OfMade
        rw [hX]
      have hp' := hp
      rw [ep] at hp' ⊢
      rw [H2K.Made.nums_of_planOk _ _ hp']
      exact places_L_own hX
  have r1 : k1.asBare.rounds = (atFinish (H2U.p12OfMade Z.made)).rounds := by
    rw [Block.asBare_rounds, IM.alone_rounds hl1, eb1]
    rfl
  -- the fold, cut in front of the test and behind it
  have hf := Keeps.chainAt_fold "the first chain" 0 c.blocksInOrder _ e₁ _ he
  rw [hfl] at hf
  obtain ⟨t, rs₀, cols₀, hpre, hrest⟩ := Keeps.foldBlocks_split 0 _ _ _ _ _ _ hf
  obtain ⟨hlen, t', k, hstep, h3⟩ := foldBlocks_cons_ok.1 hrest
  -- in front: the walk
  have hwalk := foldBlocks_roots (fun s : S => s.roots) 0 (frontOf c ++ [k0.asBare])
    (fun b hb => by
      rcases List.mem_append.1 hb with hb | hb
      · exact hfront b hb
      · obtain rfl := List.mem_singleton.1 hb
        exact alone_step hl0
          ((k2Pure_all carriedAll_roots seatCarry_roots Z Bs.G₀ (fun _ _ => trivial)
            fun _ _ _ => trivial).1 k0' hk0).1)
    (fun b hb => hpl b (by rw [hfl]; exact List.mem_append_left _ hb)) _ _ _ _ hpre
  have h00 : (ProofFile.startS Z x.pub).roots = 0 := (Meaning.K2.start_empty O.pub x.pub).2
  -- across
  have s1 := ((IM.step_alone hl1 (fun e => nomatch e) 0 t t' k _ _).mp hstep).1
  rw [eb1] at s1
  obtain ⟨fo, t'', hfo, -, -, hk, -⟩ :=
    VerifiableInference.Desc.K12.Seat.atFinish_step _ 0 t t' _ _ k s1
  have y1 := (Block.step_ok.1 s1).2.2.1
  have hmask : fo.mask ≠ none := by
    obtain ⟨-, hr'⟩ := H2K.Made.seat_pays guardedProximityTestParts _ hp (atFinish (H2U.p12OfMade Z.made))
      (H2K.Made.keeps_atFinish _)
    obtain ⟨-, -, -, R, -, -, er⟩ := H2K.Made.rounds_top _ _ hr'
    rw [r1, er] at hlen hk
    generalize List.take (List.length (_ :: R)) rs₀ = q at hlen hk
    cases q with
    | nil => simp at hlen
    | cons r0 rs' => exact H2K.JointK.mask_of_step _ _ t'' 0 k r0 rs' _ hp hk ho
  have hacross := VerifiableInference.Desc.K12.Coin.atFinish_roots _ hp ho t t' _ _
    (fun fo' h' => by
      obtain rfl : fo = fo' := VerifiableInference.Desc.First.Here.fin.inj (hfo.symm.trans h')
      exact Option.isSome_iff_ne_none.2 hmask) y1
  -- behind
  have w2 : PrR k2' := by
    rw [eb2]
    exact carriedAll_roots.retype ((carried_roots fun s : S => s.roots).under
      (b := VerifiableInference.Desc.K13.atM3 (VerifiableInference.Desc.K13.whereOf Z))
      ⟨⟨rfl, fun _ _ _ _ h => h⟩, fun h => (Bool.and_eq_true _ _ ▸ h).1, rfl⟩
      fun _ _ _ _ _ h => VerifiableInference.Desc.K13.Law.atM3_roots h)
  have w3 : PrR k3' := by
    rw [eb3]
    exact carriedAll_roots.retype fun _ _ _ _ _ h =>
      VerifiableInference.Desc.K13.Law.atM4_roots_w hw h
  have wL : PrR kL := by
    rw [ebL]
    exact carriedAll_roots.retype (seatCarry_roots.theSeal _)
  have hbehind := foldBlocks_roots (fun s : S => s.roots) 0
    [k2.asBare, k3.asBare, c.last.asBare]
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact alone_step hl2 w2
      · exact alone_step hl3 w3
      · exact alone_step hlL wL)
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact hpl _ m2
      · exact hpl _ m3
      · exact hpl _ mL) t' _ _ _ h3
  have e9 : e₁.roots = t'.roots + rootsOf (declOf [k2.asBare, k3.asBare, c.last.asBare]) := hbehind
  have e8 : t.roots = (ProofFile.startS Z x.pub).roots + rootsOf (declOf (frontOf c ++ [k0.asBare])) :=
    hwalk
  rw [hfl, List.flatMap_append, List.flatMap_cons, r1, rootsOf_append, rootsOf_append, e9, hacross,
    e8, h00]
  show _ = rootsOf (declOf (frontOf c ++ [k0.asBare])) + (_ +
    rootsOf (declOf [k2.asBare, k3.asBare, c.last.asBare]))
  omega

/-- **In the form of the row's first law** (descPure_bookOrd). -/
theorem descPure_rootsDecl (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      e₁.roots = rootsOf F.roundsDeclaredByBlocks.1 ∧ F.roundsDeclaredByBlocks.1 = F.plans.1 := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open h
  obtain ⟨e₁, -, -, -, -, -, -, -, j₁, -⟩ := (FileDescription.run_ok _ x v₁ v₂ v₃).1 hr
  have eF := O.desc
  subst eF
  exact ⟨Z, A, B, c, e₁, O.pub, rfl, j₁, roots_at_end O hr e₁ j₁⟩

end

#print axioms back_zero
#print axioms roots_at_end
#print axioms descPure_rootsDecl

end Meaning.Carry
