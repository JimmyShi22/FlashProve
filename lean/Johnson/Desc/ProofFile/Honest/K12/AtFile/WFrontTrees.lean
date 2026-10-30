-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontTrees.lean: the trees of W's sending and of Omega have
not been opened when the last chain's own test begins.

  treesSent_old, treesSent_lists, laid_back   a tree that a sending lays has been opened at no list
  sendAtS_freshLists   behind W's sending every new tree is so
  newTrees_at_end      the messages of W's sending have a tree, not yet opened, at the first chain's end

Limits.
- Nothing on the index masks' tree.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOwn
import Johnson.Desc.Third.Law.Laid
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (sendAtS)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem treesSent_old (first : ℕ) : ∀ (l : List TreeShape) (roots : ℕ) (trees : Array OnBytes.Tree) (j : ℕ),
    j < trees.size → (treesSent first l roots trees)[j]? = trees[j]?
  | [], _, _, _, _ => rfl
  | s :: l, roots, trees, j, hj => by
    have e : treesSent first (s :: l) roots trees = treesSent first l (roots + 1)
        (trees.push { shape := s, number := first + roots, src := .own roots }) := rfl
    rw [e, treesSent_old first l _ _ j (by simp; omega), Array.getElem?_push_lt hj]
    exact (Array.getElem?_eq_getElem hj).symm

/-- **A tree that the sending lays has been opened at no list.** -/
theorem treesSent_lists (first : ℕ) : ∀ (l : List TreeShape) (roots : ℕ) (trees : Array OnBytes.Tree)
    (j : ℕ) (T : OnBytes.Tree), trees.size ≤ j → (treesSent first l roots trees)[j]? = some T → T.lists = 0
  | [], _, trees, j, T, hj, h => by
    have h' : trees[j]? = some T := h
    rw [Array.getElem?_eq_none hj] at h'
    cases h'
  | s :: l, roots, trees, j, T, hj, h => by
    have e : treesSent first (s :: l) roots trees = treesSent first l (roots + 1)
        (trees.push { shape := s, number := first + roots, src := .own roots }) := rfl
    rw [e] at h
    by_cases c : j = trees.size
    · subst c
      rw [treesSent_old first l _ _ _ (by simp), Array.getElem?_push_eq] at h
      obtain rfl := Option.some.inj h
      rfl
    · exact treesSent_lists first l _ _ j T (by simp; omega) h

/-- A fold of turns of single trees that keep the count of lists. -/
theorem laid_back (f : ℕ → OnBytes.Tree → OnBytes.Tree) (idx : ℕ → ℕ) (hf : ∀ i x, (f i x).lists = x.lists) :
    ∀ (l : List ℕ) (trees : Array OnBytes.Tree) (j : ℕ) (T : OnBytes.Tree),
      (l.foldl (fun trees i => trees.modify (idx i) (f i)) trees)[j]? = some T →
      ∃ x : OnBytes.Tree, trees[j]? = some x ∧ x.lists = T.lists
  | [], _, _, T, h => ⟨T, h, rfl⟩
  | i :: l, trees, j, T, h => by
    obtain ⟨y, hy, e⟩ := laid_back f idx hf l _ j T h
    rw [Array.getElem?_modify] at hy
    by_cases c : idx i = j
    · subst c
      rw [if_pos rfl] at hy
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
      exact ⟨x, hx, (hf i x).symm.trans e⟩
    · rw [if_neg c] at hy
      exact ⟨y, hy, e⟩

theorem partsLaid_back (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ)
    (trees : Array OnBytes.Tree) (j : ℕ) (T : OnBytes.Tree)
    (h : (partsLaid sent lay n0 base trees)[j]? = some T) :
    ∃ x : OnBytes.Tree, trees[j]? = some x ∧ x.lists = T.lists := by
  unfold partsLaid at h
  exact laid_back (fun i x => { x with
      parts := x.parts.push (n0 + i)
      oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
    (fun i => base + lay.tree.getD i 0) (fun _ _ => rfl) _ _ j T h

/-- **Behind a sending every new tree has been opened at no list**, at the sending's own record. -/
theorem behind_lists {L : Type} (P : VerifiableInference.Desc.K1.Par) (d : _root_.Desc.Plain.DState L)
    (seeds : List (List E × E)) (ys : List E) (j : ℕ) (T : OnBytes.Tree)
    (hj : d.book.trees.size ≤ j)
    (hT : (VerifiableInference.Desc.K1.behind P d seeds ys).book.trees[j]? = some T) :
    T.lists = 0 := by
  have e : (VerifiableInference.Desc.K1.behind P d seeds ys).book.trees =
      partsLaid P.sent _ d.st.oracles.size d.book.trees.size
        (treesSent P.gp.firstTree _ d.roots d.book.trees) := rfl
  rw [e] at hT
  obtain ⟨z, hz, ez⟩ := partsLaid_back _ _ _ _ _ j T hT
  rw [← ez]
  exact treesSent_lists _ _ _ _ j z hj hz

/-- **Behind W's sending every new tree has been opened at no list.** -/
theorem sendAtS_freshLists {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') (j : ℕ) (T : OnBytes.Tree)
    (hj : s.book.trees.size ≤ j) (hT : s'.book.trees[j]? = some T) : T.lists = 0 := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 hy
      obtain ⟨_, _, e⟩ := (VerifiableInference.Desc.K1.decideSend_iff P _ _ x.2 r₁ r₂ x.1).1 hx
      have hT' : x.2.book.trees[j]? = some T := hT
      rw [e] at hT'
      exact behind_lists P _ _ _ j T hj hT'
    · cases h
  · cases h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The messages of W's sending have trees that have been opened at no list**, at the first chain's
end. hm: no mark. hstep: statement and book are in step there. -/
theorem newTrees_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) (hstep : e₁.st.oracles.size = e₁.book.place.size) {l : LinFirst}
    (hl : linAt e₁ = some l) (o : ℕ) (ho₁ : l.w ≤ o) (ho₂ : o < e₁.st.oracles.size) :
    ∃ (q : ℕ × ℕ) (T : OnBytes.Tree), e₁.book.place[o]? = some q ∧ e₁.book.trees[q.1]? = some T ∧
      T.lists = 0 := by
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf
  have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
    (by rw [hlen]) _ _ _ _ _ hfold
  have h' := h.toAtMg
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h'
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ e => e) (P5J.laid_at_head h') (P5J.startB_at_head h')
    (P5J.sendsB_of_madeRow h' (P5J.madeRow_at_head h'))
  have hfit : VerifiableInference.Desc.Sound.bookFitsB e₁.book = true :=
    F.bookFits 358 (pI, e₁) hreach hm
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
  have hr : ∃ a b, R₁ = [a, b] := by
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  have B := VerifiableInference.Desc.K1.sendAtS_booked _ t mid a b G₁ h1
  obtain ⟨m, hm₁, hsz, hI⟩ := VerifiableInference.Desc.K13.Law.sendAtS_idsLast _ t mid a b G₁ h1
  obtain ⟨m₀, l₀, hm₀, hl₀, hmask⟩ := VerifiableInference.Desc.K13.Law.rowsB_mask h2
  rw [hm₁] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  obtain ⟨ew, -, -⟩ := hmask hI
  obtain ⟨m₁, l₁, o', owed, hs₀, -, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have est : e₁.st = o'.2.st := by rw [es]
  have ebook : e₁.book = mid.book := by rw [es]
  have hcnt : e₁.st.oracles.size = mid.st.oracles.size := by
    rw [est]
    exact (VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows).count
  have hmsgs := B.msgs
  have hw : l₀.w = t.st.oracles.size := by
    rw [ew, hsz, hcnt, hmsgs]
    omega
  have hplace : mid.book.place.size = t.book.place.size +
      (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent.size := by
    rw [B.place]
    simp
  have hn : t.book.place.size = t.st.oracles.size := by
    have := hstep
    rw [ebook, hplace, hcnt, hmsgs] at this
    omega
  obtain ⟨k, rfl⟩ : ∃ k, o = t.st.oracles.size + k := ⟨o - t.st.oracles.size, by omega⟩
  have hk : k < (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent.size := by
    rw [hcnt, hmsgs] at ho₂
    omega
  have hpl := B.newer hn hk
  rw [← ebook] at hpl
  have hi : t.st.oracles.size + k < e₁.book.place.size := by
    rw [← hstep]
    exact ho₂
  have hall := List.all_eq_true.1 hfit (t.st.oracles.size + k) (List.mem_range.2 hi)
  rw [hpl] at hall
  dsimp only at hall
  split at hall
  · rename_i T hT
    refine ⟨_, T, hpl, hT, ?_⟩
    rw [ebook] at hT
    exact sendAtS_freshLists _ t mid a b G₁ h1 _ T (Nat.le_add_right _ _) hT
  · cases hall

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.newTrees_at_end
#print axioms ProofFile.Honest.K12.AtFile.treesSent_lists
#print axioms ProofFile.Honest.K12.AtFile.sendAtS_freshLists
