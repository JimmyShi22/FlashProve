-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleOn.lean: the end of the law of the proximity test at words given by
tables: oracle message, mask or main, row, place. Statements and proofs.

There is no new mathematics.
Why: Johnson/Desc/K12/Law/TupleWords.lean ends at `wordsT D c`. Another form of words is "wordsOn S
T" with T : oracle message → mask or main → row → place → K (in Johnson/Desc/Means/ItemsTab.lean).
Here: `wordsT D c` is that form at T := the tuple's tables.
Main names:
  `wordsOnW S T`: that "wordsOn", its four lines copied by hand. A device: it falls for the
    original, by one line "example : @wordsOnW = @wordsOn := rfl", in a tree that holds both. Not
    held by a compile.
  `entP cs sh m`: a message of a shape by (mask or main, row, place); 0 outside.
  `tabT D c`: the tables of a tuple c: at the oracle message that the layout finds at the place n:
    `entP` of message number n; 0 at every other.
  `tabP_entP`: `tabP` at an index i is `entP` at (i modulo 2 ^ the row bits, i divided by it): by
    rfl.
  `wordsT_on`: wordsT D c = wordsOnW S (tabT D c): an equation of functions, at every oracle
    message, table and index; S: any statement that holds each member's message at the member's own
    shape.
  `tuple_on_or_few`: `tuple_words_or_few` with wordsOnW t.st (tabT D c) in the place of wordsT D c.
Limits: all of those of Johnson/Desc/K12/Law/TupleWords.lean. The lemmas that go with the original
"wordsOn" (padded_wordsOn, wordsOn_agree, wordsOn_extends, says_agree; not in this library) have no
twins here. `says_congr` and `allSay_congr` of Johnson/Desc/K12/Law/TupleWords.lean (no premise on
the row; agreement inside all the statement's tables) serve in the place of says_agree (a row that
meets `RowIn`; agreement at the members alone) where that one does not lie. No soundness is claimed,
and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `combineAt_gives`, `layout_eq`;
`tuple_words_or_few`, `find_spec`, `shapes_back`, `shapesKeep_made`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.TupleWords

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- "wordsOn" (of Johnson/Desc/Means/ItemsTab.lean), its four lines copied: words
out of tables that are read by (oracle message, mask or main, row, place). -/
def wordsOnW {K : Type} [Zero K] (S : Statement) (T : Nat → Bool → Nat → Nat → K) : Words K :=
  fun o part i =>
    if i % 2 ^ S.rowBits o part < realRows S o part then
      T o (part == .mask) (i % 2 ^ S.rowBits o part) (i / 2 ^ S.rowBits o part)
    else 0

/-- A message of a shape by (mask or main, row, place); 0 outside. -/
noncomputable def entP (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J →
    GE) :
    Bool → ℕ → ℕ → GE
  | false, r, c => if h : r < sh.mainRows ∧ c < (cMain cs sh).l then m (.inl (⟨r, h.1⟩, ⟨c, h.2⟩))
      else 0
  | true, r, c => if h : r < sh.maskRows ∧ c < (cMask cs sh).l then m (.inr (⟨r, h.1⟩, ⟨c, h.2⟩))
      else 0

/-- The tables of a tuple, one message a member, by (oracle message, mask or main, row, place). -/
noncomputable def tabT (D : Plain)
    (c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE) :
    Nat → Bool → Nat → Nat → GE :=
  fun o b r pl =>
    match D.L.find o with
    | none => 0
    | some n => if h : n < D.mems.length then entP D.st.codes (D.mems.get ⟨n, h⟩).sh (c ⟨n, h⟩) b r
        pl else 0

theorem tabP_entP (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J → GE)
    (i : ℕ) : tabP cs sh m .main i = entP cs sh m false (i % 2 ^ k1 sh) (i / 2 ^ k1 sh) ∧
      tabP cs sh m .mask i = entP cs sh m true (i % 2 ^ k2 sh) (i / 2 ^ k2 sh) := ⟨rfl, rfl⟩

/-- The words of a tuple are of the form wordsOn S T: at every oracle message, table and index. S:
any statement that holds each member's message at the member's own shape. -/
theorem wordsT_on {p : P12} {t : T12} {a : Fmt.M1.Stage} {L : GroupLayout} {D : Plain}
    (hm : Made p t a L D) (S : Statement)
    (hsh : ∀ j : Fin D.mems.length, ∃ x, S.oracles[(D.mems.get j).id]? = some x ∧
      x.shape = (D.mems.get j).sh)
    (c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE) :
    wordsT D c = wordsOnW S (tabT D c) := by
  funext o part i
  unfold wordsT wordsOnW tabT
  cases hf : D.L.find o with
  | none => simp
  | some n =>
    dsimp only
    by_cases hnl : n < D.mems.length
    · rw [dif_pos hnl, dif_pos hnl]
      have hLD := hm.lay
      have hid : (D.mems.get ⟨n, hnl⟩).id = o := by
        have h1 := find_spec hf
        have h2 := (hm.mem ⟨n, hnl⟩).1
        rw [← hLD, h1] at h2
        exact (Option.some.inj h2).symm
      obtain ⟨x, hx, ex⟩ := hsh ⟨n, hnl⟩
      rw [hid] at hx
      have hrb : S.rowBits o part = ceilLog2 ((D.mems.get ⟨n, hnl⟩).sh.rows part) := by
        unfold Statement.rowBits
        rw [hx]
        show ceilLog2 (x.shape.rows part) = _
        rw [ex]
      have hrr : realRows S o part = (D.mems.get ⟨n, hnl⟩).sh.rows part := by
        unfold realRows
        rw [hx]
        show x.shape.rows part = _
        rw [ex]
      rw [hrb, hrr]
      cases part with
      | main =>
        rw [(tabP_entP _ _ _ i).1]
        show entP _ _ _ false (i % 2 ^ k1 _) (i / 2 ^ k1 _) =
          if i % 2 ^ k1 _ < (D.mems.get ⟨n, hnl⟩).sh.mainRows then
            entP _ _ _ false (i % 2 ^ k1 _) (i / 2 ^ k1 _) else 0
        split
        · rfl
        · rename_i hr
          show (if h : _ ∧ _ then _ else 0) = (0 : GE)
          rw [dif_neg (fun q => hr q.1)]
      | mask =>
        rw [(tabP_entP _ _ _ i).2]
        show entP _ _ _ true (i % 2 ^ k2 _) (i / 2 ^ k2 _) =
          if i % 2 ^ k2 _ < (D.mems.get ⟨n, hnl⟩).sh.maskRows then
            entP _ _ _ true (i % 2 ^ k2 _) (i / 2 ^ k2 _) else 0
        split
        · rfl
        · rename_i hr
          show (if h : _ ∧ _ then _ else 0) = (0 : GE)
          rw [dif_neg (fun q => hr q.1)]
    · rw [dif_neg hnl, dif_neg hnl]
      simp

/-- tuple_words_or_few at words of the form wordsOn S T: either there is a tuple c, one message a
member, such that all the rows that the test takes in hold of wordsOnW t.st (tabT D c) and each c j
is a candidate of the member's word as sent; or few draws. -/
theorem tuple_on_or_few {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12}
    {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat)
    (G : Group) (hG : S.groups[g]? = some G) (hLf : S.layout g = some L)
    (hst : t.st = begun S g G) (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD)
    (os : ∀ i, (wRound (dM i)).Orc) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l)
    (e0s : Fin D.mems.length → ℕ)
    (hS : ∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true)
    (hQ : ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (hfit : ∀ j : Fin D.mems.length,
      e < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh)) :
    (∃ c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE,
      AllSay rdE t.st (runRows S G).toList (wordsOnW t.st (tabT D c)) ∧
      ∀ (j : Fin D.mems.length) (x : OnBytes.Oracle),
        D.st.oracles[(D.mems.get j).id]? = some x →
        ∀ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
        Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 →
        x.sampleRows.toList = [{ row0 with target := tt }] →
        bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length → (β : GE) = readE seed.beta →
        (portOmZ D.st.codes (D.mems.get j).sh (e0s j)).Cand
          (strOf D.st.codes (D.mems.get j).sh (e0s j) (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) (c j)) ∨
    cnt (BadDraws (sgOf a) e t.st g L (runRows S G)
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
      (sgOf a).lstJ e * ((runRows S G).size - 1) := by
  rcases tuple_words_or_few h hm S g G hG hLf hst rd dM dF os e hJ ht hk hh hl hz e0s hS hQ hfit
      with
    ⟨c, hall, hc⟩ | hfew
  · obtain ⟨G', hG', hL'', hOk, _⟩ := combineAt_gives ht
    have hLm' : L.members = G'.members := by
      have e' := layout_eq t.st g G' hG'
      rw [show t.st.layout g = some L from hL''] at e'
      rw [Option.some.inj e']
      rfl
    have hsh : ∀ j : Fin D.mems.length, ∃ x, t.st.oracles[(D.mems.get j).id]? = some x ∧
        x.shape = (D.mems.get j).sh :=
      fun j => shapes_back hm t.st (shapesKeep_made hm) (by rw [hLm']; exact hOk.there) j
    rw [wordsT_on hm t.st hsh c] at hall
    exact .inl ⟨c, hall, hc⟩
  · exact .inr hfew

end H2K.Pin

#print axioms H2K.Pin.wordsT_on
#print axioms H2K.Pin.tuple_on_or_few
