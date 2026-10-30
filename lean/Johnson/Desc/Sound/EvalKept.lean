-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/EvalKept.lean: **INSIDE THE PROMISE AT A BORDER OF THE SHARED CHAIN, THE SLOT's OWN ITEM (Eval) IS KEPT BY THE SUB-PROTOCOL's EXTRACTOR**: the sentence EvKept (Johnson/Desc/K14/Law/LedgerRidesApart.lean), written out, at every border k and at every filling of the shared table's
letters whose (Eval) is "the row (Eval) says its claim of the witness's words, read through the first chain's reader". Statements and proofs.
THE ARGUMENT. A row's value on words is a sum over the messages THAT THE STATEMENT HAS (value_below). At each of these the first chain's reader gives the witness's table at the seat where the first chain's last state places the message (hbook). The extractor of a sub-protocol of the shared chain
turns the witness at the numbers and the seats of the messages that this sub-protocol lays, and nowhere else (extS_msg_other | extS_pad_other). So, where no message of the first chain bears such a number or sits at such a seat (hfar), the words are the same, and so is what the row says of them.
NOTHING IS ASKED OF THE ROW: not which messages it names, not that it lies in a group.
  extS_msg_other | extS_pad_other   the extractor leaves the witness's message at a number, and its pad at a seat, that no laid message bears (these stand inside the proof of extSSame, Johnson/Desc/Sound/BordersSharedFillProofs.lean; here by name).
  tab_congr              the one accessor Wit.tab reads the message at its number and the pad at its seat alone.
  value_below | says_below   a row's value reads the words of the statement's own messages alone.
  wrow_kept              WRow is carried from one family of tables to another that agrees with it at the statement's messages.
  **evKept_of**          the sentence.
ITS PREMISES: hE | hU (what the filling's (Eval) and "no mark" are: rfl at the tied letters) · hcod · hsz (inside the slot's own condition, at a state without a mark: the codes; every message of the statement has a place in the book)
· hbook (in the fenced form of Johnson/Desc/Sound/PointFenced.lean) · hfar (no message of the first chain bears the number, or sits at the seat, of a message that sub-protocol k lays).
Limits. Every premise is a premise. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SharedJointCountRowH
import Johnson.Desc.Sound.BordersSharedFillProofs
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker OnBytes.Flat KObj Cb Johnson.Pack OnBytes.Slice
open OnBytes.Means (Words Says value onTable wordsOn)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (WRow)

section
variable (cs : OnBytes.Codes) {Xi S₂ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
  (N : NumbersS) (split : Bool)

/-- The extractor leaves the witness's message at a number that no laid message bears. -/
theorem extS_msg_other (k : ℕ) (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) (n : ℕ)
    (hn : ∀ m, Comp.msg m ∈ laysAtS split k → arr (N.tenant m).1 (N.tenant m).2 ≠ n) :
    (extS cs G arr smp₂ ms decT₂ c₀ N split k s y w).msg n = w.msg n := by
  refine extAt_other cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w n ?_
  intro hmem
  obtain ⟨x, hx, hxn⟩ := List.mem_map.1 hmem
  obtain ⟨m, hm, hs⟩ := mineS_sits N ms split k x hx
  refine hn m hm ?_
  rw [← hxn]
  show _ = arr (x.1.seat x.2).1 (x.1.seat x.2).2
  rw [hs]

/-- And its pad at a seat at which no laid message sits. -/
theorem extS_pad_other (k : ℕ) (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) (q : ℕ × ℕ)
    (hq : ∀ m, Comp.msg m ∈ laysAtS split k → N.tenant m ≠ q) :
    (extS cs G arr smp₂ ms decT₂ c₀ N split k s y w).pad q.1 q.2 = w.pad q.1 q.2 := by
  refine extAt_other_pad cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w q.1 q.2 ?_
  intro hmem
  obtain ⟨x, hx, hxq⟩ := List.mem_map.1 hmem
  rw [List.append_nil] at hx
  obtain ⟨m, hm, hs⟩ := mineS_sits N ms split k x hx
  refine hq m hm ?_
  rw [← hs]
  exact hxq

end

/-- The one accessor reads the message at its number and the pad at its seat alone. -/
theorem tab_congr {Cells Tok : Type} (w w' : Wit Cells Tok MsgT) (cs : OnBytes.Codes)
    (s : OnBytes.OracleShape) (n j t : ℕ) (h1 : w'.msg n = w.msg n) (h2 : w'.pad j t = w.pad j t) :
    w'.tab cs s n j t = w.tab cs s n j t := by
  unfold Wit.tab
  rw [h1, h2]

/-- A row's value reads the words of the statement's own messages alone. -/
theorem value_below {K : Type} [CommRing K] (ρ : Model.Reading K) (S : Statement) (r : OnBytes.Row)
    {m m' : Words K} (h : ∀ o, o < S.oracles.size → ∀ part i, m o part i = m' o part i) :
    value ρ S r m = value ρ S r m' := by
  unfold value onTable
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' := Finset.mem_range.1 ho
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [h o ho']

/-- So does what it says. -/
theorem says_below {K : Type} [CommRing K] (ρ : Model.Reading K) (S : Statement) (r : OnBytes.Row)
    {m m' : Words K} (h : ∀ o, o < S.oracles.size → ∀ part i, m o part i = m' o part i) :
    Says ρ S r m ↔ Says ρ S r m' := by
  unfold Says
  rw [value_below ρ S r h]

/-- (Eval) is carried from one family of tables to another that agrees with it at the statement's messages. -/
theorem wrow_kept (Pw : Where) (s : First.S) (st : Statement)
    (T T' : ℕ → MsgT) (hT : ∀ n, n < s.st.oracles.size → T' n = T n)
    (h : WRow Pw s (wordsOn st T)) : WRow Pw s (wordsOn st T') := by
  intro l r hl hr
  refine (says_below _ s.st r fun o ho part i => ?_).1 (h l r hl hr)
  unfold wordsOn
  rw [hT o ho]

/-- **(Eval) IS KEPT BY THE EXTRACTOR OF SUB-PROTOCOL k.** -/
theorem evKept_of {P₀ P₁ S₂ Cl Xi Cells Tok : Type} {C : CK} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
    (N : NumbersS) (Mg : MeaningS S₂ P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (get : P₁ → P₀ × First.S) (Pw : Where) (stOf₁ : P₀ × First.S → Statement)
    (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → ℕ → MsgT)
    (hE : ∀ q y w, Mg.ev q y w ↔ WRow Pw (get q).2 (wordsOn (stOf₁ (get q)) (tabP₁ (get q) w)))
    (hU : ∀ q, Mg.unmarked1 q → (get q).2.failed = none)
    (hcod : ∀ q y, Oc q y → (get q).2.failed = none → (get q).2.st.codes = cs)
    (hsz : ∀ q y, Oc q y → (get q).2.failed = none →
      (get q).2.st.oracles.size ≤ (get q).2.book.place.size)
    (hbook : ∀ q y, Oc q y → (get q).2.failed = none → (get q).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) (n j t : ℕ) (sh : OnBytes.OracleShape),
        (get q).2.book.place[n]? = some (j, t) →
        ((get q).2.st.oracles[n]?).map (·.shape) = some sh →
        tabP₁ (get q) w n = w.tab cs sh (arr j t) j t)
    (hfar : ∀ q y, Oc q y → (get q).2.failed = none → ∀ n j t : ℕ,
      (get q).2.book.place[n]? = some (j, t) → ∀ m, Comp.msg m ∈ laysAtS split k →
        arr (N.tenant m).1 (N.tenant m).2 ≠ arr j t ∧ N.tenant m ≠ (j, t)) :
    ∀ a w, onQ₂ N Pm Oc split p l k a → relOwn N Mg 2 a w →
      Mg.ev a.1.1 (strsOf Fr a.2)
        (e₀H cs G arr smp₂ ms decT₂ c₀ N split Fr k ((actQ N p l k).2 a) w) := by
  intro a w ha hw
  have hoc : Oc a.1.1 (strsOf Fr a.2) := ha.2
  have hun : (get a.1.1).2.failed = none := hU _ (hw .unmarked1 (by decide))
  have hev : Mg.ev a.1.1 (strsOf Fr a.2) w := hw .ev (by decide)
  have hc := hcod _ _ hoc hun
  refine (hE _ _ _).2 (wrow_kept Pw _ _ _ _ (fun n hn => ?_) ((hE _ _ _).1 hev))
  have hn' : n < (get a.1.1).2.book.place.size := Nat.lt_of_lt_of_le hn (hsz _ _ hoc hun)
  have hpl : (get a.1.1).2.book.place[n]? = some ((get a.1.1).2.book.place[n].1,
      (get a.1.1).2.book.place[n].2) := by
    rw [Array.getElem?_eq_getElem hn']
  have hsh : ((get a.1.1).2.st.oracles[n]?).map (·.shape) =
      some ((get a.1.1).2.st.oracles[n]).shape := by
    rw [Array.getElem?_eq_getElem hn]
    rfl
  rw [hbook _ _ hoc hun hc _ n _ _ _ hpl hsh, hbook _ _ hoc hun hc w n _ _ _ hpl hsh]
  refine tab_congr _ _ _ _ _ _ _ ?_ ?_
  · exact extS_msg_other cs G arr smp₂ ms decT₂ c₀ N split k _ _ w _
      fun m hm => (hfar _ _ hoc hun n _ _ hpl m hm).1
  · exact extS_pad_other cs G arr smp₂ ms decT₂ c₀ N split k _ _ w
      ((get a.1.1).2.book.place[n].1, (get a.1.1).2.book.place[n].2)
      fun m hm => (hfar _ _ hoc hun n _ _ hpl m hm).2

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extS_msg_other
#print axioms VerifiableInference.Desc.Sound.extS_pad_other
#print axioms VerifiableInference.Desc.Sound.tab_congr
#print axioms VerifiableInference.Desc.Sound.value_below
#print axioms VerifiableInference.Desc.Sound.says_below
#print axioms VerifiableInference.Desc.Sound.wrow_kept
#print axioms VerifiableInference.Desc.Sound.evKept_of
