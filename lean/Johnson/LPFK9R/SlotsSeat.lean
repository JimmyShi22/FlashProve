-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SlotsSeat.lean: AT EVERY STATE THAT IS REACHED IN FRONT OF WHAT STANDS BEHIND THE
LAST
LINK: WHERE A LEDGER AND A LINK OF THE NUMBER m ARE OPEN, THE LEDGER HAS THE PLAN's NUMBER OF SLOTS
OF LINK m, AND ITS LIST LS HAS AS MANY COEFFICIENTS. The payer of the field "slots" of
`FoldMore` (Johnson/Desc/First/FoldMore.lean). Definitions and theorems.

How. `SlotsInv` (Johnson/Desc/First/Link/Law/SlotsWalk.lean) is carried along "reached" in the make
of `looks_at_reached` (Johnson/LPFK9R/LooksSeat.lean), through
`SeatKeeps` (Johnson/IMR/SeatKeeps.lean). TWO OF ITS TWENTY-ONE FIELDS
CANNOT BEAR THIS PROPERTY AS THEY ARE STATED, and are left idle here (their premises okB, okP are
`False`): `frames` speaks of every W, and the number of slots that "opened" lays is W's; `openQ`'s
premise is asked at the letters of EVERY link, and the head's number is right at the head's link
alone. So the two lots that spend them are paid here anew, AT THE SEAT's OWN W AND AT THE PLACES
WHOSE SWITCH STANDS AT THE HEAD: `framesLot_slots`, `k2Pure_slots`; and the joining of the lots
(`twelve_slots`, `thePure_slots`) is Johnson/IMR/SeatKeeps.lean's text with these two laid in.

What is said.
  `nsAtZ Z nH m`: **the plan's term**: `nsW Z.p.built.links Z.p.X nH m`: link m's number of slots by
    the frame's own letters; nH where the frame has none.
  `HeadSpots Z nH`: ON PUBLIC DATA ALONE: at each place of kind K2 whose switch stands at the head:
    the frame has no letters at its link, which is not link 0, and the head's plan has nH slots.
  `seatKeeps_slots`: the nineteen fields. `descPure_slots`. `slots_reach_front`.
  `slots_at_reached`, `slots_at_rch`: **THE INVARIANT**, at `Reach` and `RchAt`.
  `slots_field`: **in the letters of `FoldMore.slots`**: G.ns = nsAtZ Z nH m ∧ G.LS.size = G.ns,
where
    the open link's number is m.

Limits. `HeadSpots` is a premise: shown of no Z. THAT nsAtZ IS THE BUILT LINK's OWN FIELD ns
(`At.nsAt`) IS NOT SHOWN HERE: the frame's letters read the program's public data W (W.A[g].ns |
W.G[g].ns | W.H.ns), the built link bears a number of its own. That the open link's number is the
place's is `FoldFacts.frameIs`'s. Up to the last link's end. Nothing on soundness.

-/
import Johnson.LPFK9R.LooksSeat
import Johnson.Desc.First.Link.Law.SlotsEnds
import Johnson.Desc.First.Link.Law.SlotsClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Meaning.K2
open ProofFile (Lot Ground Pub)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-- **The nineteen fields**; `frames` and `openQ` idle. -/
theorem seatKeeps_slots (nsOf : ℕ → ℕ × ℕ) :
    SeatKeeps (KeepsSlots nsOf) (fun _ => False) (fun _ => False) where
  refl := keeps_reflS _
  trans := keeps_transS _
  frames := fun hB _ => hB.elim
  k1First := fun q gp _ => k1First_wholeS _ q gp
  k1Later := fun q gp l p m a _ => k1Later_wholeS _ q gp l p m a
  reads := fun h => readsQuietAt_wholeS _ h
  k3 := fun c r X cs sh a _ h => theStated_wholeS _ c r X cs sh a h
  k4 := k4C_wholeS _
  k5 := fun W l g bf _ h => k5N_wholeS _ W l g bf h
  k6 := fun h => k6S_wholeS _ h
  k7 := k7Of_wholeS _
  k8 := k8W_wholeS _
  k11 := k11_wholeS _
  closeOf := closeOf_wholeS _
  batch := fun p _ hf => batch_wholeS _ p hf
  k2 := fun p _ => k2_wholeS _ p
  front := headFront_keepsS _
  openQ := fun _ hP => hP.elim
  finFront := finFront_keepsS _
  finBehind := finBehind_keepsS _

/-- **The plan's term.** -/
def nsAtZ (Z : Pub) (nH m : ℕ) : ℕ := nsW Z.p.built.links Z.p.X nH m

/-- Both numbers. -/
abbrev nsZ (Z : Pub) (nH : ℕ) : ℕ → ℕ × ℕ := nsOfBuilt Z.p.built.links Z.p.X nH

/-- **The links' frames, at the seat's own W.** -/
theorem framesLot_slots (Z : Pub) (nH : ℕ) (G : Ground) :
    LotAll (KeepsSlots (nsZ Z nH)) (ProofFile.framesLot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · rename_i fs hfs
    obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
    obtain ⟨k1, k2, k3⟩ := frames_keepS nH hfs f hf
    unfold ProofFile.frameBlocks at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact quiet_whole k1 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k2 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k3 (fun _ _ _ => rfl) rfl rfl
  · obtain rfl := List.mem_singleton.1 hb'
    exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl

/-- **On public data alone**: the places whose switch stands at the head. -/
def HeadSpots (Z : Pub) (nH : ℕ) : Prop :=
  ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Z = some G → ∀ x ∈ P1K2.pureSpots Z G,
    x.2.stands = .head → ∀ l P, x.1.place.link = some l → P1K2.pureLetters G l = some P →
      nsZ Z nH l = (P.hp.ns, P.hp.ns)

/-- **The code switch's lot, the head's letters asked at the head's places alone.** -/
theorem k2Pure_slots (Z : Pub) (nH : ℕ) (h0 : Z.P.firstTree = 0) (G : Ground)
    (hP : ∀ x ∈ P1K2.pureSpots Z G, x.2.stands = .head → ∀ l P, x.1.place.link = some l →
      P1K2.pureLetters G l = some P → nsZ Z nH l = (P.hp.ns, P.hp.ns)) :
    LotAll (KeepsSlots (nsZ Z nH)) (ProofFile.k2Pure Z) G := by
  have H := seatKeeps_slots (nsZ Z nH)
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
  · rename_i x hfind
    have hxm := List.mem_of_find?_eq_some hfind
    have hx0 : x.2.firstTree = 0 := (pureSpots_firstTree hxm).trans h0
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
    | some b₀ =>
      show Whole _ b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact whole_same (finishPlace_whole H x.2 hx0) rfl (fun _ hx => hx) rfl
      · rename_i hst
        obtain ⟨P, hPe, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, hl, eP⟩ := Option.bind_eq_some_iff.1 hPe
        have hPl : P.l = l := by
          unfold P1K2.pureLetters at eP
          obtain ⟨X', _, rfl⟩ := Option.map_eq_some_iff.1 eP
          rfl
        exact whole_same (Keeps.andThen_whole _ H.trans x.1.name (First.K2.codeSwitchKind x.2)
          (First.K2.headOpened x.1.name x.1.place P) (H.k2 _ hx0)
          (quiet_whole (headOpen_makesS _ P (by rw [hPl]; exact hP x hxm hst l P hl eP))
            (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact whole_same (H.k2 x.2 hx0) rfl (fun _ hx => hx) rfl

/-- The twelve lots. -/
theorem twelve_slots (Z : Pub) (nH : ℕ) (h0 : Z.P.firstTree = 0) (G : Ground)
    (hP : ∀ x ∈ P1K2.pureSpots Z G, x.2.stands = .head → ∀ l P, x.1.place.link = some l →
      P1K2.pureLetters G l = some P → nsZ Z nH l = (P.hp.ns, P.hp.ns)) :
    ∀ L ∈ [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
      ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, K13.lotEnd Z] ++ ProofFile.p4Pure Z,
      LotAll (KeepsSlots (nsZ Z nH)) L G := by
  have H := seatKeeps_slots (nsZ Z nH)
  intro L hL
  unfold ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact framesLot_slots Z nH G
  · exact k1Pure_keeps H Z h0 G
  · exact k2Pure_slots Z nH h0 G hP
  · exact k3Lot_keeps H Z G
  · exact k4Lot_keeps H Z G
  · exact k5LotN_keeps H Z G
  · exact k8Lot_keeps H Z G
  · exact k9Ninth_keeps H Z G
  · exact k11Lot_keeps H Z G
  · exact k13LotEnd_keeps H.refl Z G
  · exact k6Lot_keeps H Z G
  · exact lotAll_of (fun b hb => h1_whole H G b hb) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h)

theorem thePure_slots (Z : Pub) (nH : ℕ) (h0 : Z.P.firstTree = 0) (G : Ground)
    (hP : ∀ x ∈ P1K2.pureSpots Z G, x.2.stands = .head → ∀ l P, x.1.place.link = some l →
      P1K2.pureLetters G l = some P → nsZ Z nH l = (P.hp.ns, P.hp.ns)) :
    LotsKeep (KeepsSlots (nsZ Z nH)) (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_slots Z nH h0 G hP
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotKeeps (KeepsSlots (nsZ Z nH)) L G := by
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact (T L (Or.inl (Or.inl h))).keep
    · exact (T L (Or.inl (Or.inr (Or.inl h)))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inl h))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))).keep
    · exact k12Lot_keeps Z G
    · exact k13Lot_keeps Z G
    · exact k13Lot4_keeps Z G
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))).keep
    · exact (T L (Or.inr h)).keep
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

/-- **AT THE PROOF FILE's SEAT.** -/
theorem descPure_slots {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : Pub} (nH : ℕ) (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hP : HeadSpots Z nH)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides (KeepsSlots (nsZ Z nH)) b := by
  obtain ⟨Z', hZ', h⟩ := ProofFile.Law.descPure_made h
  obtain rfl : Z = Z' := Except.ok.inj (hZ.symm.trans hZ')
  exact pureZ_front (keeps_reflS _) (keeps_transS _) (T := ProofFile.pureSeat o Z)
    (fun G hG => thePure_slots Z nH (pub_firstTree hZ) G (hP G hG)) h

/-- The induction along "reached", over a front stretch of the list. -/
theorem slots_reach_front {Cl P : Type} (nsOf : ℕ → ℕ × ℕ) (ft : ℕ)
    (fr bk : List (Block S Cl)) (start : P → S) (h0 : ∀ z, SlotsInv nsOf (start z))
    (hs : ∀ b ∈ fr, Decides (KeepsSlots nsOf) b) {k : ℕ} {a : P × S}
    (h : Reach ft (fr ++ bk) start k a) (hk : k ≤ fr.length) : SlotsInv nsOf a.2 := by
  induction h with
  | zero z => exact h0 z
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨R, c, _, e⟩ := hy
    have hk' : k < fr.length := hk
    rw [List.getElem?_append_left hk'] at hb
    exact hs b (List.mem_of_getElem? hb) _ _ _ _
      ((Sound.step_ok_iff ft b s s' R c c.length).1 e).2.2.2 (ih (Nat.le_of_lt hk'))

/-- **THE INVARIANT, AT EVERY REACHED STATE UP TO THE LAST LINK's END.** -/
theorem slots_at_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : Pub} (nH : ℕ) (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hP : HeadSpots Z nH)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧
      ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
        k ≤ (frontOf c).length → SlotsInv (nsZ Z nH) a.2 := by
  obtain ⟨A, B, c, e, k0, hk⟩ := descPure_slots nH hZ hP h
  refine ⟨A, B, c, e, k0, fun k a hr hle => ?_⟩
  rw [flat_eq k0] at hr
  exact slots_reach_front _ 0 (frontOf c) (backOf c) (ProofFile.startS Z)
    (fun z => slotsInv_none _ (start_none hZ z)) hk hr hle

/-- **The same at "reached, at a description's first chain"** (`Walk.Tied.RchAt`, ReachAt.lean). -/
theorem slots_at_rch {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : Pub} (nH : ℕ) (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hP : HeadSpots Z nH)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧
      ∀ {Str : Type} (k : ℕ) (a : (ProofFile.InstPub × S) × Str),
        RchAt (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) k a →
        k ≤ (frontOf c).length → SlotsInv (nsZ Z nH) a.1.2 := by
  obtain ⟨A, B, c, e, k0, hk⟩ := slots_at_reached nH hZ hP h
  exact ⟨A, B, c, e, k0, fun k a hr hle =>
    hk k a.1 (Johnson.Desc.First.Walk.Tied.rchAt_raw hr) hle⟩

/-- **In the letters of the field "slots".** -/
theorem slots_field {Z : Pub} {nH : ℕ} {s : S} (h : SlotsInv (nsZ Z nH) s) {G : Fork}
    {L : LinkCtx} {m : ℕ} (hG : s.fork? = some G) (hL : s.link? = some L) (hm : L.link = m) :
    G.ns = nsAtZ Z nH m ∧ G.LS.size = G.ns := by
  subst hm
  exact (slotsAre_iff _ G).1 (h G L hG hL)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatKeeps_slots
#print axioms VerifiableInference.Desc.LinkJoin.framesLot_slots
#print axioms VerifiableInference.Desc.LinkJoin.k2Pure_slots
#print axioms VerifiableInference.Desc.LinkJoin.descPure_slots
#print axioms VerifiableInference.Desc.LinkJoin.slots_at_reached
#print axioms VerifiableInference.Desc.LinkJoin.slots_at_rch
#print axioms VerifiableInference.Desc.LinkJoin.slots_field
