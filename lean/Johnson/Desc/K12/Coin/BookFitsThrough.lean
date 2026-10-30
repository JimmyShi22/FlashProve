-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BookFitsThrough.lean: **A YES OF THE PROXIMITY TEST's DECISION KEEPS "EVERY ORACLE MESSAGE STANDS IN ITS TREE's LIST OF PARTS AT ITS OWN PART NUMBER".** Statements and proofs.

The invariant is BookFits (Johnson/Desc/Book/BookFits.lean), with its law where a prover's message is entered (bookFits_entered) and its law on layTrees (layTrees_fits). Its head says: "that a chain's book
has BookFits wants that chain's walk, which is not read here". Here is the walk through the kind K12, along the road of BookThrough.lean (the same cuts of the decision; another sentence on the book).
  treesSent_blank     the trees that a receiving's first loop lays behind the old ones have no parts yet.
  bookFits_recvBook   the fence's book behind a receiving (recvBook, Johnson/Desc/Sound/FenceSend.lean) has it, where the layout is layTrees' and statement and book are in step.
  bookFits_of_keeps   a book with the same places that keeps each tree's parts (BookKeeps) has it.
  foldJ_bookFits · switch_bookFits · base_bookFits · stages_bookFits · k12_bookFits_of · k12_bookFits     the walk. In step: at the fold's own mask by the receiving's own clause (recvP_ok); at a switch by the field "places" of what a yes of the switch holds.
  seat_bookFits · onGu_bookFits · onGomega_bookFits     at the shared chain's two seats.
Nearest kin: recvP_fits (Johnson/Desc/Book/BookFitsGround.lean): the same call of bookFits_entered, at the plain ground's routine; here at the fence's closed form, which K12's files' unfoldings hand out.
Limits. On plain data. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.BookThrough
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)
open VerifiableInference.Desc.Sound (recvBook treesSent_count)
open VerifiableInference.Desc.Book (BookFits bookFits_entered layTrees_fits enterStep)

/-- The trees that the first loop lays behind the old ones have no parts yet. -/
theorem treesSent_blank (first : ℕ) : ∀ (l : List TreeShape) (r : ℕ) (A : Array Tree) (j : ℕ)
    (t : Tree), A.size ≤ j → (treesSent first l r A)[j]? = some t → t.parts = #[]
  | [], _, A, j, t, hj, h => by
    have h' : A[j]? = some t := h
    exact absurd (Array.getElem?_eq_some_iff.1 h').1 (by omega)
  | s :: l, r, A, j, t, hj, h => by
    have h' : (treesSent first l (r + 1) (A.push _))[j]? = some t := h
    by_cases e : j = A.size
    · subst e
      rw [treesSent_old first l (r + 1) _ A.size (by rw [Array.size_push]; omega),
        Array.getElem?_push, if_pos rfl] at h'
      rw [← Option.some.inj h']
    · exact treesSent_blank first l (r + 1) _ j t (by rw [Array.size_push]; omega) h'

/-- **The fence's book behind a receiving.** -/
theorem bookFits_recvBook (ft : ℕ) (B : TreeBook) (codes : Codes) (sent : Array OracleNotice)
    (lay : TreeLay) (n0 roots : ℕ) (hl : layTrees codes sent = some lay) (h0 : n0 = B.place.size)
    (hB : BookFits B) : BookFits (recvBook ft B sent lay n0 roots) :=
  bookFits_entered B hB sent.size n0 h0 lay (layTrees_fits hl)
    (treesSent ft lay.shapes.toList roots B.trees)
    (by rw [treesSent_count, Array.length_toList])
    (fun j hj => treesSent_old ft _ _ _ j hj)
    (fun j t hj ht => treesSent_blank ft _ _ _ j t hj ht)
    (fun x i => { x with
      parts := x.parts.push (n0 + i)
      oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) (fun _ _ => rfl)

/-- A book with the same places that keeps each tree's parts. -/
theorem bookFits_of_keeps (B B' : TreeBook) (hp : B'.place = B.place) (hk : BookKeeps B B')
    (h : BookFits B) : BookFits B' := by
  intro i q hq
  rw [hp] at hq
  obtain ⟨t, a, b⟩ := h i q hq
  obtain ⟨T', k, _, _, e⟩ := hk.tree q.1 t a
  exact ⟨T', k, by rw [e]; exact b⟩

/-- The fold's part. -/
theorem foldJ_bookFits (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (hB : BookFits t.book) : BookFits t1.book := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact hB
  · obtain ⟨lay, hl, hs, _, rfl⟩ := recvP_ok hr
    exact bookFits_recvBook p.nums.firstTree t.book _ _ lay t.st.oracles.size t.roots hl hs hB

/-- The switch's part and the batching behind it. -/
theorem switch_bookFits (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3)
    (hB : BookFits t1.book) : BookFits t3.book := by
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
    obtain ⟨_, s2⟩ := readOld_same i _ _ _ _ hread
    have k := readOld_keeps i _ _ _ _ hread
    rw [hb] at s2 k
    exact bookFits_of_keeps _ _ s2 k
      (bookFits_recvBook p.nums.firstTree t1.book _ _ D.lay t1.st.oracles.size t1.roots hd.trees
        hd.places hB)
  · cases h1'

/-- The base case. -/
theorem base_bookFits (t tE : T12) (hk : KeepsK t tE) (hb : BaseBk t tE) (hB : BookFits t.book) :
    BookFits tE.book := bookFits_of_keeps _ _ hb.1.2 hk.book hB

/-- By recursion along the stages. -/
theorem stages_bookFits (X : Parts T12) (p : P12) (hX : Like X p)
    (hBs : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
      (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE →
      BookFits t.book → BookFits tE.book
  | [], j, cur, l, t, tE, rs, gs, h, hB => by
    rw [stagesFrom_last] at h
    exact base_bookFits t tE (hX.base _ _ _ _ _ _ _ h).1 (hBs _ _ _ _ _ _ _ h) hB
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h, hB => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k1 := foldJ_bookFits p j cur _ t t1 _ _ (hX.fold _ _ _ _ _ _ _ f1) hB
    have k2 := switch_bookFits p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3) k1
    exact stages_bookFits X p hX hBs he ha rest (j + 1) nxt _ t3 tE _ _ f5 k2

/-- **A yes of the test's decision keeps it.** -/
theorem k12_bookFits_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hBs : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseBk t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) (hB : BookFits t0.book) :
    BookFits tE.book := by
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
  exact stages_bookFits X p hX hBs he ha rest 0 first _ _ tE _ _ hst hB

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_bookFits (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE)
    (hB : BookFits t0.book) : BookFits tE.book :=
  k12_bookFits_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_bk p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha t0 tE rs gs h hB

/-- **AT THE SHARED CHAIN's TWO SEATS.** -/
theorem seat_bookFits (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs = .ok d')
    (hB : BookFits d.book) : BookFits d'.book := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  exact k12_bookFits p he ha _ t' rs gs ht' hB

theorem onGu_bookFits (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hB : BookFits d.book) :
    BookFits d'.book := seat_bookFits _ _ p he ha d d' rs gs h hB

theorem onGomega_bookFits (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hB : BookFits d.book) :
    BookFits d'.book := seat_bookFits _ _ p he ha d d' rs gs h hB

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.bookFits_recvBook
#print axioms VerifiableInference.Desc.K12.Coin.bookFits_of_keeps
#print axioms VerifiableInference.Desc.K12.Coin.k12_bookFits
#print axioms VerifiableInference.Desc.K12.Coin.onGu_bookFits
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_bookFits
