-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BookThrough.lean: **THE PROXIMITY TEST's OWN BLOCK KEEPS "THE BOOK IS IN ORDER".** Statements and proofs, on the text of the block: no premise on the
view, and of the place only p.early = true and p.answers = 1.

BookStep first B roots (Johnson/Desc/Sound/BookInOrder.lean): the record counts as many roots as the book has trees, and the tree at the place z bears the number
first + z. A chain with two tests (the shared chain: the test on G_u, then the test on G_omega) must hand it through the first to the second.
The kind's files have the counts (Law/OutK3.lean: the roots rise as the trees do) and "what lay in the book stays" (Law/OutK.lean); by OutK3's own head the NUMBERS of
the trees that come are evaluated, not proved. Here they are proved, as far as this promise reads them: part by part after those files' own closed forms.
  bookOrd_of_keeps   a book with as many trees that keeps each tree's number is in order if the first was: so A READING KEEPS IT.
  foldJ_step         the fold's part: the mask has come (the book stands) or enters by the ground's receiving at p.nums.firstTree (bookStep_recv).
  switch_step        the switch's part and the batching behind it: a receiving, then a reading.
  base_step          the base case: a reading.
  stages_step        by recursion along the stages (after stages_book).
  **k12_bookStep_of · k12_bookStep**   a yes of the decision of proximityTestKind guardedProximityTestParts p from t0 to tE carries BookStep p.nums.firstTree from (t0.book, t0.roots) to (tE.book, tE.roots).
  seat_bookStep · onGu_bookStep · onGomega_bookStep   so at the shared chain's two seats (Johnson/Desc/K12/Seat.lean): the door in hands the chain's book and count of roots,
                     the door out lays them back; the chain's small record stands.
Limits. first IS THE PLACE's OWN firstTree. Nothing on how many trees come, nor on their shapes. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.SwTies
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)
open VerifiableInference.Desc.Sound (BookOrd BookStep bookStep_recv recvBook)

/-- A book with as many trees that keeps each tree's number. -/
theorem bookOrd_of_keeps (first : ℕ) (B B' : TreeBook) (hs : B'.trees.size = B.trees.size)
    (hk : BookKeeps B B') (h : BookOrd first B) : BookOrd first B' := by
  intro z T' hT'
  have hz : z < B.trees.size := hs ▸ (Array.getElem?_eq_some_iff.1 hT').1
  obtain ⟨T'', h1, _, hn, _⟩ := hk.tree z B.trees[z] (Array.getElem?_eq_getElem hz)
  rw [hT'] at h1
  obtain rfl := Option.some.inj h1
  rw [hn]
  exact h z _ (Array.getElem?_eq_getElem hz)

theorem bookStep_of_keeps (first : ℕ) (B B' : TreeBook) (r r' : ℕ)
    (hs : B'.trees.size = B.trees.size) (hk : BookKeeps B B') (hr : r' = r)
    (h : BookStep first B r) : BookStep first B' r' :=
  ⟨by rw [hr, hs]; exact h.1, bookOrd_of_keeps first B B' hs hk h.2⟩

/-- The kind's files' book behind a prover's message is the fence's. -/
theorem bookSentP_eq (ft roots : ℕ) (S : Statement) (Bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) : bookSentP ft roots S Bk sent lay = recvBook ft Bk sent lay S.oracles.size roots :=
  rfl

/-- The fold's part. -/
theorem foldJ_step (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (hB : BookStep p.nums.firstTree t.book t.roots) :
    BookStep p.nums.firstTree t1.book t1.roots := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact hB
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    exact bookStep_recv p.nums.firstTree t.book _ lay t.st.oracles.size t.roots hB

/-- The switch's part and the batching behind it. -/
theorem switch_step (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3)
    (hB : BookStep p.nums.firstTree t1.book t1.roots) :
    BookStep p.nums.firstTree t3.book t3.roots := by
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
    obtain ⟨nx', lay, e2', hl, hroots⟩ := switch_roots p he ha j cur nxt last cut t1 t2 _ gs h1
    obtain rfl : nx = nx' := Option.some.inj (e2.symm.trans e2')
    obtain rfl : D.lay = lay := Option.some.inj (hd.trees.symm.trans hl)
    have h3 := behindJ_roots p (j + 1) nxt cut t2 t3 h2
    obtain ⟨i, left, _, hb, _, _, _, hread⟩ := hd.read
    obtain ⟨s1, _⟩ := readOld_same i _ _ _ _ hread
    have k := readOld_keeps i _ _ _ _ hread
    rw [hb] at s1 k
    exact bookStep_of_keeps p.nums.firstTree _ _ _ _ s1 k (h3.trans hroots)
      (bookStep_recv p.nums.firstTree t1.book _ D.lay t1.st.oracles.size t1.roots hB)
  · cases h1'

/-- The base case. -/
theorem base_step (first : ℕ) (t tE : T12) (hk : KeepsK t tE) (hb : BaseBk t tE)
    (hB : BookStep first t.book t.roots) : BookStep first tE.book tE.roots :=
  bookStep_of_keeps first _ _ _ _ hb.1.1 hk.book hb.2 hB

/-- By recursion along the stages. -/
theorem stages_step (X : Parts T12) (p : P12) (hX : Like X p)
    (hBs : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
      (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE →
      BookStep p.nums.firstTree t.book t.roots → BookStep p.nums.firstTree tE.book tE.roots
  | [], j, cur, l, t, tE, rs, gs, h, hB => by
    rw [stagesFrom_last] at h
    exact base_step _ t tE (hX.base _ _ _ _ _ _ _ h).1 (hBs _ _ _ _ _ _ _ h) hB
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h, hB => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k1 := foldJ_step p j cur _ t t1 _ _ (hX.fold _ _ _ _ _ _ _ f1) hB
    have k2 := switch_step p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3) k1
    exact stages_step X p hX hBs he ha rest (j + 1) nxt _ t3 tE _ _ f5 k2

/-- **A yes of the test's decision keeps the book in order.** -/
theorem k12_bookStep_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hBs : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE)
    (hB : BookStep p.nums.firstTree t0.book t0.roots) :
    BookStep p.nums.firstTree tE.book tE.roots := by
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  exact stages_step X p hX hBs he ha rest 0 first _ _ tE _ _ hst hB

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_bookStep (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE)
    (hB : BookStep p.nums.firstTree t0.book t0.roots) :
    BookStep p.nums.firstTree tE.book tE.roots :=
  k12_bookStep_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_bk p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha t0 tE rs gs h hB

/-- **AT THE SHARED CHAIN's TWO SEATS**: a yes of the block seated by Seat.enter g mask and Seat.leave (Seat.onGu | Seat.onGomega are such) keeps the book in order and
leaves the chain's small record. -/
theorem seat_bookStep (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs = .ok d')
    (hB : BookStep p.nums.firstTree d.book d.roots) :
    BookStep p.nums.firstTree d'.book d'.roots ∧ d'.loc = d.loc := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  exact ⟨k12_bookStep p he ha _ t' rs gs ht' hB, rfl⟩

theorem onGu_bookStep (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hB : BookStep p.nums.firstTree d.book d.roots) :
    BookStep p.nums.firstTree d'.book d'.roots ∧ d'.loc = d.loc :=
  seat_bookStep _ _ p he ha d d' rs gs h hB

theorem onGomega_bookStep (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hB : BookStep p.nums.firstTree d.book d.roots) :
    BookStep p.nums.firstTree d'.book d'.roots ∧ d'.loc = d.loc :=
  seat_bookStep _ _ p he ha d d' rs gs h hB

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.bookOrd_of_keeps
#print axioms VerifiableInference.Desc.K12.Coin.foldJ_step
#print axioms VerifiableInference.Desc.K12.Coin.switch_step
#print axioms VerifiableInference.Desc.K12.Coin.k12_bookStep
#print axioms VerifiableInference.Desc.K12.Coin.onGu_bookStep
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_bookStep
