-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/HeldThrough.lean: **"THE RECORD HOLDS THE SAMPLE" (smpHeld) RIDES PAST EVERY BLOCK OF THE SHARED CHAIN, AT A SEAT WHOSE TREE LIES IN THE BOOK IN FRONT.** Statements and proofs, in the
blocks' own decide-form.

smpHeld st B z t (Johnson/Desc/SmpRows.lean) reads: which message the book places at (z, t) (oracleNo: the first such); of that message its shape, its mark, its sample rows; the statement's codes.
noColl_rides | prom_rides (Johnson/Desc/Sound/LedgerRides.lean) ask, at each block, that it says the same in front and behind (hh; hkeep5's second half).
  PlacesGrow B B'      the book behind has no fewer trees, and at every seat whose tree lies in the book in front the same message sits. Reflexive, transitive.
  placesGrow_recv      a receiving has it, where every place of the book in front names a tree of that book (PlacesInBook, Johnson/Desc/Sound/HeldShift.lean): a new message is placed in a new tree.
  placesGrow_same      a reading (the places stand, the trees' count stands) has it.
  smpHeld_rides        PlacesGrow · the codes stand · smpPart of the message that sits at the seat stands: smpHeld stands at such a seat. KIN: smpHeld_same (Johnson/Desc/First/Link/Law/DoorBlind.lean): ONE book, and the
                       triple at EVERY number at once: what a block that sends nothing has. Here the book grows.
  k12_places · seat_places   the proximity test's own block, part by part (after BookThrough.lean).
  held_k14 · held_onGu · held_onGomega   **AT EVERY BLOCK**; and through shiftBook lo at the file's seat lo + z.
Limits. At the test on G_u: at a seat whose message is not the mask handed in. At the chain's own record St. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.BookThrough
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.Sound.SamplesAtK14
import Johnson.Desc.Sound.HeldShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)
open VerifiableInference.Desc.Sound (recvBook recvBook_place_old recvBook_place_new PlacesInBook
  placesIn_recv shiftBook smpHeld_shift partsLaid_count treesSent_count)

/-- Every place names a tree of the book; the book behind has no fewer trees; at every seat whose tree lies in the book in front the same message sits. -/
structure PlacesGrow (B B' : TreeBook) : Prop where
  inB : PlacesInBook B → PlacesInBook B'
  more : B.trees.size ≤ B'.trees.size
  same : PlacesInBook B → ∀ z t, z < B.trees.size → oracleNo B' z t = oracleNo B z t

theorem PlacesGrow.refl (B : TreeBook) : PlacesGrow B B := ⟨id, Nat.le_refl _, fun _ _ _ _ => rfl⟩

theorem PlacesGrow.trans {A B C : TreeBook} (h : PlacesGrow A B) (k : PlacesGrow B C) :
    PlacesGrow A C :=
  ⟨fun x => k.inB (h.inB x), h.more.trans k.more, fun x z t hz =>
    (k.same (h.inB x) z t (Nat.lt_of_lt_of_le hz h.more)).trans (h.same x z t hz)⟩

/-- A reading: the places stand, the trees' count stands. -/
theorem placesGrow_same (B B' : TreeBook) (h : SameN B B') : PlacesGrow B B' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x o q hq => ?_, by rw [h1], fun _ z t _ => ?_⟩
  · rw [h1]
    rw [h2] at hq
    exact x o q hq
  · unfold oracleNo
    rw [h2]

/-- find? over a longer range whose new members all fail. -/
theorem find_range_more (p : ℕ → Bool) (n k : ℕ) (h : ∀ i, n ≤ i → i < n + k → p i = false) :
    (List.range (n + k)).find? p = (List.range n).find? p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.find?_append,
      ih fun i h1 h2 => h i h1 (by omega)]
    have e : [n + k].find? p = none := by
      rw [List.find?_cons, h (n + k) (by omega) (by omega)]
      rfl
    rw [e, Option.or_none]

theorem find_congr' (p q : ℕ → Bool) : ∀ l : List ℕ, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find_congr' p q l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **A receiving.** -/
theorem placesGrow_recv (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) (hl : ∀ i, i < sent.size → lay.tree.getD i 0 < lay.shapes.size) :
    PlacesGrow bk (recvBook ft bk sent lay n0 roots) := by
  have hsz : (recvBook ft bk sent lay n0 roots).trees.size = bk.trees.size + lay.shapes.size := by
    show (partsLaid sent lay n0 bk.trees.size
      (treesSent ft lay.shapes.toList roots bk.trees)).size = _
    rw [partsLaid_count, treesSent_count, Array.length_toList]
  have hps : (recvBook ft bk sent lay n0 roots).place.size = bk.place.size + sent.size := by
    show (bk.place ++ _).size = _
    simp
  refine ⟨fun x => placesIn_recv ft bk sent lay n0 roots x hl, by rw [hsz]; omega,
    fun _ z t hz => ?_⟩
  unfold oracleNo
  rw [hps, find_range_more _ _ _ fun i h1 h2 => ?_]
  · refine find_congr' _ _ _ fun o ho => ?_
    rw [recvBook_place_old ft bk sent lay n0 roots o (List.mem_range.1 ho)]
  · obtain ⟨j, rfl⟩ : ∃ j, i = bk.place.size + j := ⟨i - bk.place.size, by omega⟩
    rw [recvBook_place_new ft bk sent lay n0 roots j (by omega)]
    refine beq_eq_false_iff_ne.2 fun e => ?_
    have := congrArg Prod.fst (Option.some.inj e)
    have e' : bk.trees.size + lay.tree.getD j 0 = z := this
    omega

/-- **smpHeld rides.** -/
theorem smpHeld_rides (st st' : Statement) (B B' : TreeBook) (hg : PlacesGrow B B')
    (hin : PlacesInBook B) (hc : st'.codes = st.codes) (z t : ℕ) (hz : z < B.trees.size)
    (hs : ∀ o, oracleNo B z t = some o →
      (st'.oracles[o]?).map smpPart = (st.oracles[o]?).map smpPart) :
    smpHeld st' B' z t = smpHeld st B z t := by
  have eo := hg.same hin z t hz
  unfold smpHeld smpSeed smpRows
  rw [eo, hc]
  cases ho : oracleNo B z t with
  | none => rfl
  | some o =>
    have h1 := hs o ho
    simp only [Option.bind_some]
    cases hx : st.oracles[o]? with
    | none =>
      rw [hx] at h1
      cases hx' : st'.oracles[o]? with
      | none => rfl
      | some x' =>
        rw [hx'] at h1
        cases h1
    | some x =>
      rw [hx] at h1
      cases hx' : st'.oracles[o]? with
      | none =>
        rw [hx'] at h1
        cases h1
      | some x' =>
        rw [hx'] at h1
        have e : smpPart x' = smpPart x := Option.some.inj h1
        have e1 : x'.shape = x.shape := congrArg (fun q => q.1) e
        have e2 : x'.sampled = x.sampled := congrArg (fun q => q.2.1) e
        have e3 : x'.sampleRows = x.sampleRows := congrArg (fun q => q.2.2) e
        simp only [Option.bind_some]
        rw [e1, e2, e3]

/-! ## The proximity test's own block, part by part -/

theorem foldJ_places (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    PlacesGrow t.book t1.book := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact PlacesGrow.refl _
  · obtain ⟨lay, hl, _, _, rfl⟩ := recvP_ok hr
    exact placesGrow_recv p.nums.firstTree t.book _ lay t.st.oracles.size t.roots
      fun i hi => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hl hi

theorem switch_places (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    PlacesGrow t1.book t3.book := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, _⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    obtain ⟨i, left, _, hb, _, _, _, hread⟩ := hd.read
    have s1 := readOld_same i _ _ _ _ hread
    rw [hb] at s1
    exact (placesGrow_recv p.nums.firstTree t1.book _ D.lay t1.st.oracles.size t1.roots
      fun i hi => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hd.trees hi).trans (placesGrow_same _ _ s1)
  · cases h1'

theorem stages_places (X : Parts T12) (p : P12) (hX : Like X p)
    (hBs : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
      (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE → PlacesGrow t.book tE.book
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact placesGrow_same _ _ (hBs _ _ _ _ _ _ _ h).1
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k1 := foldJ_places p j cur _ t t1 _ _ (hX.fold _ _ _ _ _ _ _ f1)
    have k2 := switch_places p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    exact (k1.trans k2).trans (stages_places X p hX hBs he ha rest (j + 1) nxt _ t3 tE _ _ f5)

/-- **A yes of the test's decision.** -/
theorem k12_places (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    PlacesGrow t0.book tE.book := by
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  have k := stages_places guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_bk p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha rest 0 first _ _ tE _ _ hst
  exact k

theorem seat_places (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') : PlacesGrow d.book d'.book := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  exact k12_places p he ha _ t' rs gs ht'

/-! ## At every block -/

/-- What the riding asks of the record in front: every place names a tree of the book, and the book places no message that the statement has not. -/
def HeldFit (d : _root_.Desc.K14.St) : Prop :=
  PlacesInBook d.book ∧ d.book.place.size ≤ d.st.oracles.size

theorem oracleNo_lt (B : TreeBook) (z t o : ℕ) (h : oracleNo B z t = some o) : o < B.place.size := by
  unfold oracleNo at h
  exact List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- **The test on G_u**: at a seat whose message is not the mask handed in. -/
theorem held_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hf : HeldFit d) (z t : ℕ)
    (hz : z < d.book.trees.size) (hm : ∀ o, oracleNo d.book z t = some o → d.loc.firstMask ≠ some o) :
    smpHeld d'.st d'.book z t = smpHeld d.st d.book z t := by
  obtain ⟨a, b, _⟩ := onGu_leaves p he ha d d' rs gs h
  exact smpHeld_rides d.st d'.st d.book d'.book (seat_places _ _ p he ha d d' rs gs h) hf.1 a z t hz
    fun o ho => b o (Nat.lt_of_lt_of_le (oracleNo_lt _ _ _ _ ho) hf.2) (hm o ho)

/-- **The test on G_omega.** -/
theorem held_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hf : HeldFit d) (z t : ℕ)
    (hz : z < d.book.trees.size) :
    smpHeld d'.st d'.book z t = smpHeld d.st d.book z t := by
  obtain ⟨a, b, _⟩ := onGomega_leaves p he ha d d' rs gs h
  exact smpHeld_rides d.st d'.st d.book d'.book (seat_places _ _ p he ha d d' rs gs h) hf.1 a z t hz
    fun o ho => b o (Nat.lt_of_lt_of_le (oracleNo_lt _ _ _ _ ho) hf.2)

open _root_.Desc.K14.Law.Fence in
/-- **K14's eight blocks.** -/
theorem held_k14 (P : _root_.Desc.K14.P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
    (hbl : _root_.Desc.K14.blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (b : Block _root_.Desc.K14.St Unit) (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8])
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs) (h : b.decide d rs gs = .ok d')
    (hf : HeldFit d) (z t : ℕ) (hz : z < d.book.trees.size) :
    smpHeld d'.st d'.book z t = smpHeld d.st d.book z t := by
  have ks := keepsSmp_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d d' rs gs h
  have hg : PlacesGrow d.book d'.book := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) →
        PlacesGrow d.book d'.book := fun hq => by
      have e := (own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h).1
      rw [e]
      exact PlacesGrow.refl d.book
    have snd : (b = b2 ∨ b = b5) → PlacesGrow d.book d'.book := fun hq => by
      obtain ⟨sent, lay, hl, _, _, rb, _⟩ := send_first P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
      rw [rb]
      exact placesGrow_recv _ d.book sent lay _ _ fun i hi => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hl hi
    rcases hb with e | e | e | e | e | e | e | e
    · exact own (.inl e)
    · exact snd (.inl e)
    · exact own (.inr (.inl e))
    · exact own (.inr (.inr (.inl e)))
    · exact snd (.inr e)
    · exact own (.inr (.inr (.inr (.inl e))))
    · exact own (.inr (.inr (.inr (.inr (.inl e)))))
    · exact own (.inr (.inr (.inr (.inr (.inr e)))))
  exact smpHeld_rides d.st d'.st d.book d'.book hg hf.1 ks.1 z t hz
    fun o ho => ks.2.2 o (Nat.lt_of_lt_of_le (oracleNo_lt _ _ _ _ ho) hf.2)

/-- Through the reader that the table's seats want: at the file's seat lo + z. -/
theorem held_shift (lo : ℕ) (st st' : Statement) (B B' : TreeBook) (z t : ℕ)
    (h : smpHeld st' B' z t = smpHeld st B z t) :
    smpHeld st' (shiftBook lo B') (lo + z) t = smpHeld st (shiftBook lo B) (lo + z) t := by
  rw [smpHeld_shift, smpHeld_shift]
  exact h

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.placesGrow_recv
#print axioms VerifiableInference.Desc.K12.Coin.smpHeld_rides
#print axioms VerifiableInference.Desc.K12.Coin.k12_places
#print axioms VerifiableInference.Desc.K12.Coin.held_onGu
#print axioms VerifiableInference.Desc.K12.Coin.held_onGomega
#print axioms VerifiableInference.Desc.K12.Coin.held_k14
#print axioms VerifiableInference.Desc.K12.Coin.held_shift
