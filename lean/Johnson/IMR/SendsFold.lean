-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsFold.lean: THE HYPOTHESIS SendsAt IS BOUND TOO WIDELY FOR A SENDER WHOSE DECISION
READS
THE STATE: it asks the law AT EVERY STATE with the code table; K2's code switch sends what the
state's frame says: at a state that no fold reaches that need not be the plan's sending: THERE
SendsAt IS FALSE AND seats_at_cut's PREMISE CANNOT BE PROVED. SO ReachedAt · SendsOn · sends_alongR
· seats_at_cutR: THE HYPOTHESIS ON THE SUB-PROTOCOL NUMBER j IS ASKED AT THE STATES THAT THE FOLD
FROM s₀ REACHES IN FRONT OF IT, AND AT NO OTHER: so every theorem along the fold may be used by a
proof.
reached_accepts: whatever stands in front of a reached border has accepted somewhere (for hear_runs
| rest_by (Johnson/IMR/LinkRest.lean), whose law wants «the link's first sub-protocol accepts
somewhere»). SendsAt · sends_along · seats_at_cut stand (true; fit for whoever sends nothing);
seats_at_cut is a call of seats_at_cutR.
KIND-FREE; IT IMPORTS NO FILE OF Johnson/IMR/: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean), ALONG THE FOLD: FROM «EACH SUB-PROTOCOL APPENDS TO THE STATE's
BOOK JUST WHAT THE VERIFIER's OWN LAYOUT LAYS FOR ITS SENDINGS» TO «AT EVERY
STATE THAT THE FOLD REACHES THE BOOK's PLACES AND ITS TREES' SHAPES ARE PREFIXES OF THE PLAN's LISTS».
ON WORDS: «the state» is the verifier's state: the value of type S that the fold carries from sub-protocol (block) to sub-protocol; «the state's book» its list of commitment trees with the oracle messages' places (S.book).
THE MACHINE IS CALLED, NOT TYPED: Johnson/Desc/K12/Coin/BookAppends.lean: Appends codes sends B B' (B' has B's places and shapes, and behind them what laidFrom lays for the list sends from B's number of trees on) · Appends.nil · Appends.trans; BookRides.lean: laidFrom_append · SeatsPrefix · seatsPrefix_iff; Door/DoorIs.lean:
seatsCarried_is. The fold's cut: Johnson/Desc/K15/FoldInv.lean. THIS FILE ADDS THE FOLD OVER IT.
OBJECT. foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out: the form of the conclusion of rchAt_fold (Johnson/Top/H0/Walk/ReachAt.lean). USER. FoldFacts (Johnson/Desc/First/FoldFacts.lean: seatsCarried) · MsgSig | World (placesAre).
LETTERS. codes: the code table, which stays · sn j: the list of sendings of the sub-protocol number j ([] at most of them; several at the proximity test) · ft: the first tree.

  InStep s          the statement has as many oracle messages as the book has places.
  SendsAt ft codes snd b   THE HYPOTHESIS ON ONE SUB-PROTOCOL: where its step accepts from s to s' and s has the code table: s' has it · Appends codes snd s.book s'.book · in step stays in step.
  sends_along       along a list of sub-protocols, the first at number k₀.
  ReachedAt ft bs s₀ j s · SendsOn ft codes G snd b · sends_alongR · seats_at_cutR   THE FORM TO PROVE: the hypothesis at number j is asked at the states that the fold from s₀ reaches in front of j alone. SendsAt.on · Accepts · reached_accepts · fold_last.
  prefix_of_appends   from the empty book: what the sendings in front have appended is a prefix of what all sendings lay.
  seats_at_cut      AT A CHAIN: SendsAt at every sub-protocol · the first state has the code table, an empty book and is in step · the plan's lists L are what all sendings lay ⟹ behind the first k: SeatsPrefix L · in step · the code table. NO «no mark» IS ASKED.
  door_seats · places_are   … in the Door's own Bool (atFirstSeats) and in SmpPlaces.lean's (placesAre L.places).
  (seats_at_cut's last clause: the two counts come out of it: the book's places and trees are as many as the sendings in front lay.)

What is not claimed. SendsAt at any sub-protocol. That the closed constant's L (P5J.At.laid?, Johnson/P5J/LettersAt2.lean) is what the sub-protocols' sendings lay (the plan's side). No soundness.
-/
import Johnson.Desc.K12.Coin.BookAppends
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.Sound.SmpPlaces
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.ProofFile.LotCore

set_option autoImplicit false

namespace IM

open OnBytes (Codes OracleNotice TreeBook)
open VerifiableInference.Desc (Block Chain foldBlocks OpenedColumn placesAre)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Coin (Laid laidFrom laidOf Appends SeatsPrefix)
open ProofFile (Cl)

/-- The statement has as many oracle messages as the book has places. -/
def InStep (s : S) : Prop := s.st.oracles.size = s.book.place.size

/-- **The hypothesis on one sub-protocol.** -/
def SendsAt (ft : ℕ) (codes : Codes) (snd : List (Array OracleNotice)) (b : Block S Cl) : Prop :=
  ∀ (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ), b.step ft s rs cols = .ok (s', n) →
    s.st.codes = codes →
    s'.st.codes = codes ∧ Appends codes snd s.book s'.book ∧ (InStep s → InStep s')

/-- **Along a list of sub-protocols.** -/
theorem sends_along {ft : ℕ} {codes : Codes} {sn : ℕ → List (Array OracleNotice)} :
    ∀ (bs : List (Block S Cl)) (k₀ : ℕ),
    (∀ j b, bs[j]? = some b → SendsAt ft codes (sn (k₀ + j)) b) →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok out → s.st.codes = codes →
      out.1.st.codes = codes ∧
        Appends codes ((List.range' k₀ bs.length).flatMap sn) s.book out.1.book ∧
        (InStep s → InStep out.1)
  | [], k₀, _, s, rs, cols, out, h, hc => by
    obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s rs cols out h
    exact ⟨hc, Appends.nil codes _ _ rfl rfl, id⟩
  | b :: l, k₀, hH, s, rs, cols, out, h, hc => by
    obtain ⟨s', n, -, hs, hl⟩ := VerifiableInference.Desc.foldBlocks_cons ft b l s rs cols out h
    obtain ⟨c1, a1, i1⟩ := hH 0 b rfl s s' _ _ n hs hc
    have hHl : ∀ j b', l[j]? = some b' → SendsAt ft codes (sn (k₀ + 1 + j)) b' := by
      intro j b' hj
      have := hH (j + 1) b' (by simpa using hj)
      rwa [show k₀ + (j + 1) = k₀ + 1 + j by omega] at this
    obtain ⟨c2, a2, i2⟩ := sends_along l (k₀ + 1) hHl s' _ _ out hl c1
    refine ⟨c2, ?_, fun h => i2 (i1 h)⟩
    have e : (List.range' k₀ (b :: l).length).flatMap sn =
        sn (k₀ + 0) ++ (List.range' (k₀ + 1) l.length).flatMap sn := by
      rw [List.length_cons, List.range'_succ, List.flatMap_cons]
      rfl
    rw [e]
    exact a1.trans a2

/-- The sub-protocol's step accepts somewhere. -/
def Accepts (ft : ℕ) (b : Block S Cl) : Prop :=
  ∃ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : ℕ), b.step ft s rs cols = .ok (s', n)

/-- The fold over the first j sub-protocols from s₀ accepts, to s. -/
def ReachedAt (ft : ℕ) (bs : List (Block S Cl)) (s₀ : S) (j : ℕ) (s : S) : Prop :=
  ∃ (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft (bs.take j) s₀ rs cols = .ok r ∧ r.1 = s

/-- **The hypothesis on one sub-protocol, asked at the states of G alone.** -/
def SendsOn (ft : ℕ) (codes : Codes) (G : S → Prop) (snd : List (Array OracleNotice))
    (b : Block S Cl) : Prop :=
  ∀ (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ), G s →
    b.step ft s rs cols = .ok (s', n) → s.st.codes = codes →
    s'.st.codes = codes ∧ Appends codes snd s.book s'.book ∧ (InStep s → InStep s')

theorem SendsAt.on {ft : ℕ} {codes : Codes} {G : S → Prop} {snd : List (Array OracleNotice)}
    {b : Block S Cl} (h : SendsAt ft codes snd b) : SendsOn ft codes G snd b :=
  fun s s' rs cols n _ hy hc => h s s' rs cols n hy hc

/-- One step of the fold, cut off at its end. -/
theorem fold_last {ft k : ℕ} {bs : List (Block S Cl)} {b : Block S Cl} (hb : bs[k]? = some b)
    {s₀ : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (bs.take (k + 1)) s₀ rs cols = .ok out) :
    ∃ (t : S) (rs' : List Fmt.RoundView) (cols' : List OpenedColumn) (n : ℕ),
      foldBlocks ft (bs.take k) s₀ rs cols = .ok (t, rs', cols') ∧
      b.step ft t (rs'.take b.rounds.length) cols' = .ok (out.1, n) := by
  rw [List.take_add_one, hb] at h
  obtain ⟨t, rs', cols', h1, h2⟩ :=
    VerifiableInference.Desc.Keeps.foldBlocks_split ft [b] _ _ _ _ _ h
  obtain ⟨s', n, -, hs, hl⟩ := VerifiableInference.Desc.foldBlocks_cons ft b [] t rs' cols' out h2
  obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s' _ _ out hl
  exact ⟨t, rs', cols', n, h1, hs⟩

/-- Whatever stands in front of a reached border has accepted somewhere. -/
theorem reached_accepts {ft : ℕ} {bs : List (Block S Cl)} {s₀ : S} : ∀ {j : ℕ} {s : S},
    ReachedAt ft bs s₀ j s → ∀ {i : ℕ} {b : Block S Cl}, i < j → bs[i]? = some b → Accepts ft b
  | 0, _, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | j + 1, s, ⟨rs, cols, r, hf, _⟩, i, b, hi, hb => by
    by_cases hj : j < bs.length
    · obtain ⟨t, rs', cols', n, h1, h2⟩ := fold_last (List.getElem?_eq_getElem hj) hf
      by_cases e : i = j
      · subst e
        obtain rfl : bs[i] = b := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hb)
        exact ⟨t, _, _, _, n, h2⟩
      · exact reached_accepts ⟨rs, cols, _, h1, rfl⟩ (by omega) hb
    · have e : bs.take (j + 1) = bs.take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [e] at hf
      have hib : i < bs.length := (List.getElem?_eq_some_iff.1 hb).1
      exact reached_accepts ⟨rs, cols, r, hf, rfl⟩ (by omega) hb

/-- **Along the fold, the hypothesis on each sub-protocol asked at the states that the fold reaches in front of it.** -/
theorem sends_alongR {ft : ℕ} {codes : Codes} {sn : ℕ → List (Array OracleNotice)}
    {bs : List (Block S Cl)} {s₀ : S}
    (h : ∀ j b, bs[j]? = some b → SendsOn ft codes (ReachedAt ft bs s₀ j) (sn j) b)
    (hc : s₀.st.codes = codes) : ∀ (k : ℕ), k ≤ bs.length → ∀ (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft (bs.take k) s₀ rs cols = .ok out →
      out.1.st.codes = codes ∧ Appends codes ((List.range k).flatMap sn) s₀.book out.1.book ∧
        (InStep s₀ → InStep out.1)
  | 0, _, rs, cols, out, hf => by
    rw [List.take_zero] at hf
    obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s₀ rs cols out hf
    exact ⟨hc, Appends.nil codes _ _ rfl rfl, id⟩
  | k + 1, hk, rs, cols, out, hf => by
    have hb := List.getElem?_eq_getElem (l := bs) (i := k) (by omega)
    obtain ⟨t, rs', cols', n, h1, h2⟩ := fold_last hb hf
    obtain ⟨c1, a1, i1⟩ := sends_alongR h hc k (by omega) rs cols _ h1
    obtain ⟨c2, a2, i2⟩ := h k _ hb t out.1 _ _ n ⟨rs, cols, _, h1, rfl⟩ h2 c1
    refine ⟨c2, ?_, fun x => i2 (i1 x)⟩
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact a1.trans a2

/-- From the empty book: what the sendings in front have appended is a prefix of what all lay. -/
theorem prefix_of_appends {codes : Codes} {pre post : List (Array OracleNotice)} {L : Laid}
    {B : TreeBook} (hL : laidOf codes (pre ++ post) = some L)
    (ha : Appends codes pre { trees := #[], place := #[] } B) :
    SeatsPrefix L B ∧ ∃ A, laidOf codes pre = some A ∧ B.place.size = A.places.length ∧
      B.trees.size = A.shapes.length := by
  obtain ⟨A, hA, ep, es⟩ := ha
  obtain ⟨A', R, hA', -, e1, e2⟩ :=
    VerifiableInference.Desc.K12.Coin.laidFrom_append codes pre post 0 L hL
  have hA0 : laidFrom codes 0 pre = some A := hA
  obtain rfl : A = A' := Option.some.inj (hA0.symm.trans hA')
  have ep' : B.place.toList = A.places := by simpa using ep
  have es' : B.trees.toList.map (·.shape) = A.shapes := by simpa using es
  have n1 : B.place.size = A.places.length := by rw [← ep', Array.length_toList]
  have n2 : B.trees.size = A.shapes.length := by
    rw [← es', List.length_map, Array.length_toList]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, A, hA0, n1, n2⟩
  · rw [ep', e1, n1, List.take_left']
    rfl
  · rw [e1, n1, List.length_append]
    omega
  · rw [es', e2, n2, List.take_left']
    rfl
  · rw [e2, n2, List.length_append]
    omega

/-- **AT A CHAIN**, the hypothesis on each sub-protocol asked at the states that the fold reaches in front of it. -/
theorem seats_at_cutR {ft : ℕ} {codes : Codes} {sn : ℕ → List (Array OracleNotice)}
    {c : Chain S Cl} {s₀ : S}
    (h : ∀ j b, c.blocksInOrder[j]? = some b → SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ j) (sn j) b)
    (hc : s₀.st.codes = codes) (hb : s₀.book = { trees := #[], place := #[] }) (hi : InStep s₀)
    {L : Laid} (hL : laidOf codes ((List.range c.blocksInOrder.length).flatMap sn) = some L) {k : ℕ}
    (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn} (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out) :
    SeatsPrefix L out.1.book ∧ InStep out.1 ∧ out.1.st.codes = codes ∧
      ∃ A, laidOf codes ((List.range k).flatMap sn) = some A ∧
        out.1.book.place.size = A.places.length ∧ out.1.book.trees.size = A.shapes.length := by
  obtain ⟨c1, a1, i1⟩ := sends_alongR h hc k hk rs cols out hf
  rw [hb] at a1
  have hsplit : (List.range c.blocksInOrder.length).flatMap sn =
      (List.range k).flatMap sn ++ (List.range' k (c.blocksInOrder.length - k)).flatMap sn := by
    have e : List.range' 0 c.blocksInOrder.length =
        List.range' 0 k ++ List.range' (0 + k) (c.blocksInOrder.length - k) := by
      rw [List.range'_append_1, Nat.add_sub_cancel' hk]
    rw [Nat.zero_add] at e
    rw [← List.flatMap_append, List.range_eq_range', List.range_eq_range', e]
  rw [hsplit] at hL
  obtain ⟨p1, A, hA, n1, n2⟩ := prefix_of_appends hL a1
  exact ⟨p1, i1 hi, c1, A, hA, n1, n2⟩

/-- **AT A CHAIN.** -/
theorem seats_at_cut {ft : ℕ} {codes : Codes} {sn : ℕ → List (Array OracleNotice)}
    {c : Chain S Cl} (h : ∀ j b, c.blocksInOrder[j]? = some b → SendsAt ft codes (sn j) b) {s₀ : S}
    (hc : s₀.st.codes = codes) (hb : s₀.book = { trees := #[], place := #[] }) (hi : InStep s₀)
    {L : Laid} (hL : laidOf codes ((List.range c.blocksInOrder.length).flatMap sn) = some L) {k : ℕ}
    (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn} (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out) :
    SeatsPrefix L out.1.book ∧ InStep out.1 ∧ out.1.st.codes = codes ∧
      ∃ A, laidOf codes ((List.range k).flatMap sn) = some A ∧
        out.1.book.place.size = A.places.length ∧ out.1.book.trees.size = A.shapes.length :=
  seats_at_cutR (fun j b hb' => (h j b hb').on) hc hb hi hL hk hf

/-- In the Door's own Bool. -/
theorem door_seats {Ld : VerifiableInference.Desc.K12.Door.Laid} {s : S}
    (h : SeatsPrefix (VerifiableInference.Desc.K12.Door.toTree Ld) s.book) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld s = true := by
  unfold VerifiableInference.Desc.K12.Door.atFirstSeats
  rw [VerifiableInference.Desc.K12.Door.seatsCarried_is]
  exact (VerifiableInference.Desc.K12.Coin.seatsPrefix_iff _ _).2 h

/-- In SmpPlaces.lean's Bool (placesAre). -/
theorem places_are {L : Laid} {s : S} (h : SeatsPrefix L s.book) (hi : InStep s) :
    placesAre L.places s.st s.book = true := by
  unfold placesAre
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨h.2.1, hi⟩, fun k hk => ?_⟩
  have e : s.book.place.toList[k]? = (L.places.take s.book.place.size)[k]? := by rw [← h.1]
  rw [Array.getElem?_toList, List.getElem?_take, if_pos hk] at e
  exact e

end IM

#print axioms IM.sends_along
#print axioms IM.prefix_of_appends
#print axioms IM.reached_accepts
#print axioms IM.sends_alongR
#print axioms IM.seats_at_cutR
#print axioms IM.seats_at_cut
#print axioms IM.door_seats
#print axioms IM.places_are
