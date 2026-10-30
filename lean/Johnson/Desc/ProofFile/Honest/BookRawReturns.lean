-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRawReturns.lean: WHERE EACH STEP OF THE MAKER OF THE BOOK OF COINS
IN FRONT OF THE BOOK's OWN TESTS (bookRaw, Honest/BookWhole.lean) RETURNS, AND ITS FOUR VERDICTS ARE
GOOD (mainRoomFault finds no switch at fault; Omega's sending and W's are there; no fold outside the
shared chain sends its own fresh table), THE MAKER RETURNS A BOOK. Written by the authors of the
honest side of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's
authors; the makers are theirs. Six statements with their proofs; no definition. General in the
description, the sendings and the merges: no description is named.

  mapM_ok_of_all  a function into Except that returns at each member of a list returns at the list
                  (kin: see below)
  linksWants_returns   **the segments' stretches are laid where each link's mask row is found**:
                  whatever the merges and the index-mask message are
  segmentCarries_returns   **the chain of segments' carrying entries are laid where behind each
                  link's fresh table a fold stands with a sending behind it**
  shared_steps_return   what a return of the short list (sharedAhead, Honest/BookShared.lean) gives:
                  eight steps' returns, each with the term that the short list binds
  spendingBook_returns   the book as far as its spending entries go (Honest/BookAll.lean): each
                  premise is one step of that text
  bookRaw_returns **the top**: each premise but hsh is one step of bookRaw's text; hsh, the short
                  list's return, gives seven

Why. The two long lists of a book (the segments' stretches; the chain of segments' carrying entries)
need not be made to know that they are there. Where a step's answer is short, an equation to that
answer gives the premise here.
Limits. NO RETURN IS SHOWN BY IT, AT ANY DESCRIPTION: each statement is an implication, and its
premises are shown nowhere in this file. THE BOOK IS NOT NAMED: nothing can be evaluated at it.
Nothing on the book's own tests (ProverCoinCounts.checked). The verdict of wantsFree is a premise of
spendingBook_returns (hw): a fifth verdict for whoever joins the two laws. Bookkeeping: no new
mathematics. Kin of mapM_ok_of_all in the library, none of them beneath this file: for errors that
are strings: ProofFile.Sk.mapM_returns (Johnson/Desc/ProofFile/Law/Skel/SkelEnd.lean),
LPFPol.SkR.mapM_returns (Johnson/LPFPol/SkR/SkelEnd.lean), and, with a property and the length,
mapM_of_each (Johnson/AtFull/Public/AttAtW.lean), and, in the form of the test isOk,
Johnson.Unfolds.mapM_isOk (Johnson/Unfolds/SentLaw.lean); for Option: mapM_returns
(OnBytes/Maker/TablesReturn.lean), mapM_some (OnBytes/Maker/ReadWalks.lean). Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.BookShared
import Johnson.Desc.ProofFile.Honest.BookSharedKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)
open ProofFile.Honest.BookShared (ex_bind bind_of_ok)

/-- A function into Except that returns at each member of a list returns at the list. The like of
the library's ProofFile.Sk.mapM_returns (Johnson/Desc/ProofFile/Law/Skel/SkelEnd.lean), which has it at
errors that are strings, here at any type of errors; not called: that file does not lie beneath this
one. -/
theorem mapM_ok_of_all {ε α β : Type} {f : α → Except ε β} :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ r, l.mapM f = .ok r
  | [], _ => ⟨[], by rw [List.mapM_nil]; rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨r, hr⟩ := mapM_ok_of_all l fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: r, by rw [List.mapM_cons, hb, hr]; rfl⟩

variable {S Cl Xi : Type}

/-- **The segments' stretches are laid where each link's mask row is found.** CONDITIONAL: h. -/
theorem linksWants_returns {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} (idx : MsgAt) (merges : List Addr) (ls : List Nat)
    (h : ∀ n ∈ ls,
      (ownerOf maskRowRun bs c later s!"link {n}, moment 0" isMaskRowMsg).isSome = true)
    (t : Nat) : ∃ y, linksWants bs c later idx merges ls t = .ok y := by
  induction ls generalizing t with
  | nil => exact ⟨([], t), rfl⟩
  | cons n ls ih =>
    obtain ⟨row, hrow⟩ := Option.isSome_iff_exists.1 (h n List.mem_cons_self)
    obtain ⟨y, hy⟩ := ih (fun m hm => h m (List.mem_cons_of_mem _ hm))
      (segmentWants bs n row idx merges t).2
    refine ⟨((segmentWants bs n row idx merges t).1 ++ y.1, y.2), ?_⟩
    show (match ownerOf maskRowRun bs c later s!"link {n}, moment 0" isMaskRowMsg with
      | none =>
        (.error s!"segment {n}: its mask row is not found" : Except String (List Want × Nat))
      | some row => (linksWants bs c later idx merges ls (segmentWants bs n row idx merges t).2).map
          fun (y : List Want × Nat) => ((segmentWants bs n row idx merges t).1 ++ y.1, y.2)) = _
    rw [hrow]
    show (linksWants bs c later idx merges ls (segmentWants bs n row idx merges t).2).map _ = _
    rw [hy]
    rfl

/-- **The chain of segments' carrying entries are laid where behind each link's fresh table a fold
stands with a sending behind it.** CONDITIONAL: h. -/
theorem segmentCarries_returns {here : List PlanB} {ms : List SentMsg}
    (h : ∀ f ∈ ms, f.fresh = true → (linkOf f.label).isSome = true →
      (behindFold here f.round).isSome = true) : ∃ l, segmentCarries here ms = .ok l := by
  have key : ∀ (g : SentMsg → Except String (List Ahead)) (L : List SentMsg),
      (∀ a ∈ L, ∃ b, g a = .ok b) → ∃ l, (List.flatten <$> L.mapM g) = .ok l := fun g L hg => by
    obtain ⟨r, hr⟩ := mapM_ok_of_all L hg
    exact ⟨r.flatten, by rw [hr]; rfl⟩
  unfold segmentCarries
  refine key _ _ fun f hf => ?_
  have hm := List.mem_filter.1 hf
  have hb := hm.2
  rw [Bool.and_eq_true] at hb
  obtain ⟨⟨p, q⟩, hpq⟩ := Option.isSome_iff_exists.1 (h f hm.1 hb.1 hb.2)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hb.2
  rw [hpq, hn]
  exact ⟨_, rfl⟩

/-- **What a return of the short list gives**: eight steps' returns, each with the term that the
short list binds. CONDITIONAL: h. -/
theorem shared_steps_return {F : FileDescription Xi} {p1 : Johnson.G.ChainSends} {l : List Ahead}
    (h : sharedAhead F p1 = .ok l) :
    ∃ f1 m1 iF cF iO cO pq tail, foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f1 ∧
      sentIn F.shared.blocksInOrder p1 = .ok m1 ∧
      due? "the folded row's sending"
        ((m1.filter fun m => m.label == "the folded row").head?.map (·.round)) = .ok iF ∧
      groupCarries (planOf F.shared.blocksInOrder) iF
        ((m1.filter fun m => m.label == "the folded row").filter (!·.fresh) ++
          (m1.filter fun m => m.label == "Omega").filter (·.masks))
        ((m1.filter fun m => m.label == "the folded row").find? (·.fresh)) = .ok cF ∧
      due? "the folded row's test's last switch"
        ((((seedRounds F.shared.blocksInOrder).zip p1.sends).filter fun x =>
          testOf x.2.label == "the folded row's test").getLast?.map (·.1)) = .ok iO ∧
      groupCarries (planOf F.shared.blocksInOrder) iO (m1.filter fun m => m.label == "Omega") none =
        .ok cO ∧
      due? "the second chain's first fold, with a sending behind it"
        (behindFold (planOf F.second.blocksInOrder) 0) = .ok pq ∧
      due? "the shared chain's mask code" ((codesUnder p1 "Omega").map (·.2.r)) = .ok tail := by
  unfold sharedAhead at h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨m1, hm1, h⟩ := ex_bind h
  dsimp only at h
  obtain ⟨iF, hiF, h⟩ := ex_bind h
  obtain ⟨cF, hcF, h⟩ := ex_bind h
  obtain ⟨iO, hiO, h⟩ := ex_bind h
  obtain ⟨cO, hcO, h⟩ := ex_bind h
  obtain ⟨pq, hpq, h⟩ := ex_bind h
  obtain ⟨tail, htail, -⟩ := ex_bind h
  exact ⟨f1, m1, iF, cF, iO, cO, pq, tail, hf1, hm1, hiF, hcF, hiO, hcO, hpq, htail⟩

/-- **The book as far as its spending entries go returns**, where each step of its text does and
wantsFree accepts. CONDITIONAL: each premise is one step. -/
theorem spendingBook_returns {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {idx : MsgAt}
    (e0 : ∃ r, rowsIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok r)
    (e1 : ∃ r, rowsIn F.shared.blocksInOrder p1 = .ok r) (e2 : ∃ r, rowsIn F.second.blocksInOrder p2 = .ok r)
    (ei : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
      isIndexMaskMsg = some idx)
    (hl : ∀ n ∈ (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups,
      (ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {n}, moment 0" isMaskRowMsg).isSome = true)
    (hw : ∀ a, linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a →
      wantsFree (a.1 ++ (loneWants idx M.lone
        ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) = true)
    (g0 : ∃ f, foldEntries (planOf F.first.blocksInOrder) (planOf F.second.blocksInOrder) p0 = .ok f)
    (g1 : ∃ f, foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f)
    (g2 : ∃ f, foldEntries (planOf F.second.blocksInOrder) [] p2 = .ok f) :
    ∃ B, spendingBook F p0 p1 p2 M = .ok B := by
  obtain ⟨r0, hr0⟩ := e0
  obtain ⟨r1, hr1⟩ := e1
  obtain ⟨r2, hr2⟩ := e2
  obtain ⟨f0, hf0⟩ := g0
  obtain ⟨f1, hf1⟩ := g1
  obtain ⟨f2, hf2⟩ := g2
  obtain ⟨a, ha⟩ := linksWants_returns idx M.ends _ hl 0
  have hwa := hw a ha
  have step : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {a : α},
      x = .ok a → (∃ b, f a = .ok b) → ∃ b, (x >>= f) = .ok b :=
    fun hx ⟨b, hb⟩ => ⟨b, bind_of_ok hx hb⟩
  have ifn : ∀ {c : Prop} [Decidable c] {β : Type} {x y : Except String β},
      ¬c → (∃ b, y = .ok b) → ∃ b, (if c then x else y) = .ok b :=
    fun hc ⟨b, hb⟩ => ⟨b, (if_neg hc).trans hb⟩
  unfold spendingBook
  refine step hr0 (step hr1 (step hr2 ?_))
  rw [ei]
  refine step (a := idx) rfl (step ha (ifn ?_ ?_))
  · rw [hwa]
    decide
  · exact step rfl (step hf0 (step hf1 (step hf2 ⟨_, rfl⟩)))

/-- **THE TOP: bookRaw returns a book**, where each step of its text returns and its verdicts are
good. CONDITIONAL: each premise but hsh is one step; hsh gives seven. -/
theorem bookRaw_returns {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {m0 : List SentMsg} {l : List Ahead}
    (hS : ∃ B, spendingBook F p0 p1 p2 M = .ok B)
    (hm : sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0)
    (hsh : sharedAhead F p1 = .ok l)
    (s0 : ∃ r, switchRows F.first.blocksInOrder p0 (firstCodes p0 p1) = .ok r)
    (s1 : ∃ r, switchRows F.shared.blocksInOrder p1 (firstCodes p0 p1) = .ok r)
    (s2 : ∃ r, switchRows F.second.blocksInOrder p2 (firstCodes p0 p1) = .ok r)
    (hroom : ∀ c ∈ [p0, p1, p2], mainRoomFault c (firstCodes p0 p1) = .ok none)
    (hseg : ∀ f ∈ m0, f.fresh = true → (linkOf f.label).isSome = true →
      (behindFold (planOf F.first.blocksInOrder) f.round).isSome = true)
    (hom : ∀ m1, sentIn F.shared.blocksInOrder p1 = .ok m1 →
      (m1.filter fun m => m.label == "Omega").isEmpty = false)
    (hW : (m0.filter fun m => m.label == "W").isEmpty = false)
    (hown : (ownFreshIn F.first.blocksInOrder).isEmpty = true ∧ (ownFreshIn F.second.blocksInOrder).isEmpty = true) :
    ∃ W, bookRaw F p0 p1 p2 M = .ok W := by
  obtain ⟨B, hB⟩ := hS
  obtain ⟨r0, hs0⟩ := s0
  obtain ⟨r1, hs1⟩ := s1
  obtain ⟨r2, hs2⟩ := s2
  obtain ⟨f1, m1, iF, cF, iO, cO, pq, tail, -, hm1, hiF, hcF, hiO, hcO, hpq, htail⟩ :=
    shared_steps_return hsh
  obtain ⟨seg, hsg⟩ := segmentCarries_returns hseg
  have q0 := hroom p0 (by simp)
  have q1 := hroom p1 (by simp)
  have q2 := hroom p2 (by simp)
  have step : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {a : α},
      x = .ok a → (∃ b, f a = .ok b) → ∃ b, (x >>= f) = .ok b :=
    fun hx ⟨b, hb⟩ => ⟨b, bind_of_ok hx hb⟩
  have ifn : ∀ {c : Prop} [Decidable c] {β : Type} {x y : Except String β},
      ¬c → (∃ b, y = .ok b) → ∃ b, (if c then x else y) = .ok b :=
    fun hc ⟨b, hb⟩ => ⟨b, (if_neg hc).trans hb⟩
  unfold bookRaw
  refine step hB (step hm (step hm1 (step hs0 (step hs1 (step hs2
    (step (a := PUnit.unit) ?_ ?_))))))
  · simp only [List.forIn_cons, List.forIn_nil, q0, q1, q2]
    rfl
  refine step hsg (step hiF (step hcF (step hiO (ifn ?_ (step rfl (step hcO (ifn ?_
    (step rfl (step hpq (ifn ?_ (step rfl (step htail ⟨_, rfl⟩))))))))))))
  · show ¬ (m1.filter fun m => m.label == "Omega").isEmpty = true
    rw [hom m1 hm1]
    decide
  · show ¬ (m0.filter fun m => m.label == "W").isEmpty = true
    rw [hW]
    decide
  · show ¬ (!(ownFreshIn F.first.blocksInOrder).isEmpty || !(ownFreshIn F.second.blocksInOrder).isEmpty) = true
    rw [hown.1, hown.2]
    decide

end ProofFile.Honest

#print axioms ProofFile.Honest.mapM_ok_of_all
#print axioms ProofFile.Honest.linksWants_returns
#print axioms ProofFile.Honest.segmentCarries_returns
#print axioms ProofFile.Honest.shared_steps_return
#print axioms ProofFile.Honest.spendingBook_returns
#print axioms ProofFile.Honest.bookRaw_returns
