-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleWords.lean: the end of the law of the proximity test at words built from
the tuple of candidates alone. Statements and proofs.

There is no new mathematics.
Why: `tuple_or_few` (Johnson/Desc/K12/Law/TupleRoad.lean) ends, in its first arm, in "∃ one witness
w near the law's word, AllSay … (the words cut out of w's own group tables) ∧ each member's share of
w is a candidate". Whoever states what a row means wants words made of messages, one for each oracle
message, through a function that lays a message out as its two tables. The lemma that turns the one
into the other is here.
Main names:
  `tabP cs sh m`: a message m of the shape sh as its two tables: the entry (row r, place c) at the
    index r + 2 ^ (the row bits) · c; 0 on the rows beyond the real ones and on the places beyond
    the code's message length.
  `tabP_main`, `tabP_mask`, `tabP_at`: its two equations; at an entry's own table (partZ) and index
    (locZ) it is the entry.
  `says_congr`, `allSay_congr`: what a row says hangs on the words inside the statement's tables
    alone (i < tableSize S o part): no premise on the row.
  `words_tabP`: one member: under the premises of `words_share`, S.codes = cs, the two message
    lengths powers of two, and `Padded` of the witness's words: at every index inside the member's
    tables: wordsOf S L (tabOf s w) o part i = tabP cs sh (the member's share of w) part i. At the
    real rows: `words_share`; beyond them: `Padded`.
  `find_spec`: what the layout finds stands at that place among the members.
  `wordsT D c`: the words of a tuple c (one message a member): at the oracle message that the layout
    finds at the place n: `tabP` of message number n; 0 at every other.
  `words_tuple`: at the law's letters (`Good`, `Made`, `StageJ`, `combineAt`, two numbers, the yes
    of `siteL` and of `sampleL` at every member): for a witness w within e of the law's word, at
    every oracle message, table and index inside the statement's tables: the words cut out of w's
    own group tables = wordsT D (the shares of w). `Padded` comes of `blank_of_near` and
    `padded_wordsOf`: so "near" is spent.
  `tuple_words_or_few`: `tuple_or_few` with the witness gone from the first arm: either ∃ c, AllSay
    rdE t.st (runRows S G).toList (wordsT D c) ∧ each c j is a candidate of `strOf` (the member's
    word as sent) at ((the seed's point read, β), the answer read), for any seed at which
    `Send.form` gives the record's sample row; or cnt (BadDraws …) ≤ lstJ e · ((runRows S G).size −
    1).
Limits:
(1) All of those of Johnson/Desc/K12/Law/TupleRoad.lean: no game; the letters are this folder's own
(`strOf`, the seed, e0, `AllSay`); the members are the group's.
(2) The statement is t.st = begun S g G, behind the beginning of the test; a table of what rows mean
has its items at S, in front. The bridge wants `InOrder S` (Johnson/Desc/Means/Order.lean) from the
border.
(3) The yes of `siteL` and of `sampleL` are asked at every member (hS, hQ): they are held by runs
alone (`siteOk` and `sampleOk` have said true at every member of the two example proofs). A group
with a member that is not sampled pays hQ nowhere; the front's clause "every member is sampled" asks
the mark, not `sampleL`.
(4) c is dependently typed (each c j over its member's own shape); a reader that wants one type for
all messages needs a cast, which is not typed.
(5) e0s: one radius a member, with hfit as a premise on each.
(6) One direction: nothing says that a tuple with these properties comes of a near witness.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `le_two_pow_ceilLog2`
(OnBytes/Slice/ProgCodes.lean); `combineAt_gives`, `layout_eq`, `layFacts`; `tuple_or_few`,
`words_share`, `padded_wordsOf`, `blank_of_near`, `rowsBlank_law`, `codes_made`, `sample_of_L`,
`shapes_back`, `shapesKeep_made`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.TupleRoad

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays

/-- A message of a shape as its two tables: the entry (row r, place c) stands at the index r + 2 ^
(the row bits) · c; 0 on the rows beyond the real ones and on the places beyond the code's message
length. -/
noncomputable def tabP (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J →
    GE) :
    Part → ℕ → GE
  | .main, i =>
    if h : i % 2 ^ k1 sh < sh.mainRows ∧ i / 2 ^ k1 sh < (cMain cs sh).l then
      m (.inl (⟨i % 2 ^ k1 sh, h.1⟩, ⟨i / 2 ^ k1 sh, h.2⟩)) else 0
  | .mask, i =>
    if h : i % 2 ^ k2 sh < sh.maskRows ∧ i / 2 ^ k2 sh < (cMask cs sh).l then
      m (.inr (⟨i % 2 ^ k2 sh, h.1⟩, ⟨i / 2 ^ k2 sh, h.2⟩)) else 0

theorem tabP_main (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J → GE)
    (i : ℕ) : tabP cs sh m .main i =
      if h : i % 2 ^ k1 sh < sh.mainRows ∧ i / 2 ^ k1 sh < (cMain cs sh).l then
        m (.inl (⟨i % 2 ^ k1 sh, h.1⟩, ⟨i / 2 ^ k1 sh, h.2⟩)) else 0 := rfl

theorem tabP_mask (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J → GE)
    (i : ℕ) : tabP cs sh m .mask i =
      if h : i % 2 ^ k2 sh < sh.maskRows ∧ i / 2 ^ k2 sh < (cMask cs sh).l then
        m (.inr (⟨i % 2 ^ k2 sh, h.1⟩, ⟨i / 2 ^ k2 sh, h.2⟩)) else 0 := rfl

/-- tabP at an entry's own table and index is the entry. -/
theorem tabP_at (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (m : (portCode cs sh).J → GE)
    (j : (portCode cs sh).J) : tabP cs sh m (partZ cs sh j) (locZ cs sh j) = m j := by
  rcases j with y | y
  · have hr : y.1.val < 2 ^ k1 sh := lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _)
    have h1 : (y.1.val + 2 ^ k1 sh * y.2.val) % 2 ^ k1 sh = y.1.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have h2 : (y.1.val + 2 ^ k1 sh * y.2.val) / 2 ^ k1 sh = y.2.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
    show tabP cs sh m .main (y.1.val + 2 ^ k1 sh * y.2.val) = _
    rw [tabP_main, dif_pos ⟨by rw [h1]; exact y.1.isLt, by rw [h2]; exact y.2.isLt⟩]
    congr 2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · have hr : y.1.val < 2 ^ k2 sh := lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _)
    have h1 : (y.1.val + 2 ^ k2 sh * y.2.val) % 2 ^ k2 sh = y.1.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have h2 : (y.1.val + 2 ^ k2 sh * y.2.val) / 2 ^ k2 sh = y.2.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
    show tabP cs sh m .mask (y.1.val + 2 ^ k2 sh * y.2.val) = _
    rw [tabP_mask, dif_pos ⟨by rw [h1]; exact y.1.isLt, by rw [h2]; exact y.2.isLt⟩]
    congr 2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- What a row says hangs on the words inside the statement's tables alone. -/
theorem says_congr (S : Statement) (r : Row) (m m' : Words GE)
    (h : ∀ o part i, i < tableSize S o part → m o part i = m' o part i) :
    Says rdE S r m ↔ Says rdE S r m' := by
  have hv : value rdE S r m = value rdE S r m' := by
    unfold value onTable
    refine Finset.sum_congr rfl fun o _ => ?_
    congr 1 <;>
      exact Finset.sum_congr rfl fun i hi => by rw [h o _ i (Finset.mem_range.1 hi)]
  unfold Says
  rw [hv]

theorem allSay_congr (S : Statement) (l : List Row) (m m' : Words GE)
    (h : ∀ o part i, i < tableSize S o part → m o part i = m' o part i) :
    AllSay rdE S l m ↔ AllSay rdE S l m' :=
  ⟨fun a r hr => (says_congr S r m m' h).1 (a r hr), fun a r hr => (says_congr S r m m' h).2 (a r
      hr)⟩

/-- At a member, inside its tables, the words that a witness's own tables hold are the two tables
of the member's share: words_share at the real rows; Padded beyond them. -/
theorem words_tabP (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) {s : Sg}
    (σs : Site s (mbOfShape cs sh e0)) (oM oZ : ℕ)
    (hpM : ∀ r, σs.pM r = vtx _ (oM + r.val)) (hpZ : ∀ r, σs.pZ r = vtx _ (oZ + r.val))
    (hrM : oM + sh.mainRows ≤ 2 ^ (s.h + s.g)) (hrZ : oZ + sh.maskRows ≤ 2 ^ s.h)
    (S : Statement) (L : GroupLayout) (o n : ℕ) (x : Oracle) (hx : S.oracles[o]? = some x)
    (hsh : x.shape = sh) (hcs : S.codes = cs) (hf : L.find o = some n)
    (hk : L.kept.getD n false = false)
    (hm : 0 < sh.mainRows → L.mainFirst.getD n none = some oM)
    (hz : 0 < sh.maskRows → L.maskFirst.getD n none = some oZ)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (hlM : 0 < sh.mainRows → 2 ^ ceilLog2 (pMain cs sh).ell = (pMain cs sh).ell)
    (hlZ : 0 < sh.maskRows → 2 ^ ceilLog2 (pMask cs sh).ell = (pMask cs sh).ell)
    (w : s.cIn.J → GE) (hP : Padded S (H2K.ClaimSays.wordsOf S L (tabOf s w)))
    (part : Part) (i : ℕ) (hi : i < tableSize S o part) :
    H2K.ClaimSays.wordsOf S L (tabOf s w) o part i =
      tabP cs sh (fun j => w (σs.atJ j)) part i := by
  have hW := words_share cs sh e0 σs oM oZ hpM hpZ hrM hrZ S L o n x hx hsh hf hk hm hz hLk hLh w
  subst hsh
  subst hcs
  cases part with
  | main =>
    have hb : S.rowBits o .main = k1 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    by_cases hr : i % 2 ^ k1 x.shape < x.shape.mainRows
    · have h0 : 0 < x.shape.mainRows := lt_of_le_of_lt (Nat.zero_le _) hr
      have hc : i / 2 ^ k1 x.shape < (cMain S.codes x.shape).l := by
        have hts : tableSize S o .main =
            2 ^ (k1 x.shape + ceilLog2 (pMain S.codes x.shape).ell) := by
          have hne : (x.shape.rows .main == 0) = false := by
            show (x.shape.mainRows == 0) = false
            simp only [beq_eq_false_iff_ne]
            omega
          unfold tableSize Statement.has Statement.tableBits Statement.placeBits
          rw [hb, hx]
          simp only [hne]
          rw [if_pos (by simpa using h0)]
          rfl
        rw [hts, pow_add, hlM h0] at hi
        exact Nat.div_lt_of_lt_mul hi
      have e := hW (.inl (⟨_, hr⟩, ⟨_, hc⟩))
      have el : locZ S.codes x.shape (.inl (⟨i % 2 ^ k1 x.shape, hr⟩, ⟨i / 2 ^ k1 x.shape, hc⟩)) =
          i :=
        Nat.mod_add_div i _
      rw [el] at e
      rw [tabP_main, dif_pos ⟨hr, hc⟩]
      exact e
    · rw [tabP_main, dif_neg (fun q => hr q.1)]
      refine hP o .main i ?_
      rw [hb]
      unfold realRows
      rw [hx]
      exact Nat.le_of_not_lt hr
  | mask =>
    have hb : S.rowBits o .mask = k2 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    by_cases hr : i % 2 ^ k2 x.shape < x.shape.maskRows
    · have h0 : 0 < x.shape.maskRows := lt_of_le_of_lt (Nat.zero_le _) hr
      have hc : i / 2 ^ k2 x.shape < (cMask S.codes x.shape).l := by
        have hts : tableSize S o .mask =
            2 ^ (k2 x.shape + ceilLog2 (pMask S.codes x.shape).ell) := by
          have hne : (x.shape.rows .mask == 0) = false := by
            show (x.shape.maskRows == 0) = false
            simp only [beq_eq_false_iff_ne]
            omega
          unfold tableSize Statement.has Statement.tableBits Statement.placeBits
          rw [hb, hx]
          simp only [hne]
          rw [if_pos (by simpa using h0)]
          rfl
        rw [hts, pow_add, hlZ h0] at hi
        exact Nat.div_lt_of_lt_mul hi
      have e := hW (.inr (⟨_, hr⟩, ⟨_, hc⟩))
      have el : locZ S.codes x.shape (.inr (⟨i % 2 ^ k2 x.shape, hr⟩, ⟨i / 2 ^ k2 x.shape, hc⟩)) =
          i :=
        Nat.mod_add_div i _
      rw [el] at e
      rw [tabP_mask, dif_pos ⟨hr, hc⟩]
      exact e
    · rw [tabP_mask, dif_neg (fun q => hr q.1)]
      refine hP o .mask i ?_
      rw [hb]
      unfold realRows
      rw [hx]
      exact Nat.le_of_not_lt hr

/-! ## At the law's own letters -/

open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- What the layout finds stands at that place among the members. -/
theorem find_spec {L : GroupLayout} {o n : Nat} (h : L.find o = some n) : L.members[n]? = some o :=
    by
  unfold GroupLayout.find at h
  rcases hm : L.members with ⟨l⟩
  rw [hm, List.idxOf?_toArray, List.idxOf?_eq_some_iff] at h
  obtain ⟨hi, e, _⟩ := h
  simp only [List.getElem?_toArray]
  rw [List.getElem?_eq_getElem hi, e]

/-- The words that a tuple of messages holds, one message a member: at the member that the layout
finds at the place n: the two tables of message number n; 0 at every other oracle message. -/
noncomputable def wordsT (D : Plain)
    (c : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE) : Words GE :=
  fun o part i =>
    match D.L.find o with
    | none => 0
    | some n =>
      if h : n < D.mems.length then tabP D.st.codes (D.mems.get ⟨n, h⟩).sh (c ⟨n, h⟩) part i else 0

/-- For a witness near the law's word: inside the statement's tables the words cut out of the
witness's own group tables are the words of the tuple of its shares. -/
theorem words_tuple {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (g : Nat)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (e : ℕ) (hJ : (sgOf a).StageJ e) (rows : Array Row) (ht : combineAt t.st g ⟨L, rows⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (e0s : Fin D.mems.length → ℕ)
    (hS : ∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true)
    (hQ : ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (w : (sgOf a).cIn.N.Wit)
    (hn : offCnt (Ex := (sgOf a).cIn.ext)
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
      ((sgOf a).cIn.N.enc w.1 w.2) ≤ e)
    (o : Nat) (part : Part) (i : ℕ) (hi : i < tableSize t.st o part) :
    H2K.ClaimSays.wordsOf t.st L (tabOf (sgOf a) w.1) o part i =
      wordsT D (fun j q => w.1
        ((siteOf D.st.codes a (D.mems.get j) (e0s j) (oM D.L j.val) (oZ D.L j.val) (hS j)).atJ q))
        o part i := by
  obtain ⟨G', hG', hL'', hOk, _⟩ := combineAt_gives ht
  have hL' : t.st.layout g = some L := hL''
  have hLm' : L.members = G'.members := by
    have e' := layout_eq t.st g G' hG'
    rw [hL'] at e'
    rw [Option.some.inj e']
    rfl
  have hy := rowsBlank_law h hm rd g G' hG' hL' hOk hk hh
    (fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
  have hF := layFacts hG' hL' hOk
  have hcs := codes_made hm
  have hP : Padded t.st (H2K.ClaimSays.wordsOf t.st L (tabOf (sgOf a) w.1)) :=
    padded_wordsOf hF _ (blank_of_near (sgOf a) hJ.sized e hJ.joh.1 t.st L _ hy w hn)
  have hLD := hm.lay
  subst hLD
  unfold wordsT
  cases hf : D.L.find o with
  | none =>
    simp only [H2K.ClaimSays.wordsOf, hf]
  | some n =>
    have hmem := find_spec hf
    have hnl : n < D.mems.length := by
      rw [← hm.size]
      rcases Nat.lt_or_ge n D.L.members.size with q | q
      · exact q
      · rw [Array.getElem?_eq_none q] at hmem
        cases hmem
    have hid : (D.mems.get ⟨n, hnl⟩).id = o := by
      have := (hm.mem ⟨n, hnl⟩).1
      rw [hmem] at this
      exact (Option.some.inj this).symm
    dsimp only
    rw [dif_pos hnl]
    obtain ⟨x, hx, hq⟩ := hQ ⟨n, hnl⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hlM, hlZ⟩ := sample_of_L hq
    obtain ⟨x1, hx1, ex1⟩ := shapes_back hm t.st (shapesKeep_made hm)
      (by rw [hLm']; exact hOk.there) ⟨n, hnl⟩
    rw [hid] at hx1
    exact words_tabP (s := sgOf a) D.st.codes (D.mems.get ⟨n, hnl⟩).sh (e0s ⟨n, hnl⟩)
      (siteOf D.st.codes a (D.mems.get ⟨n, hnl⟩) (e0s ⟨n, hnl⟩) (oM D.L n) (oZ D.L n)
        (hS ⟨n, hnl⟩)) (oM D.L n) (oZ D.L n)
      (fun _ => rfl) (fun _ => rfl) (h.roomM ⟨n, hnl⟩) (h.roomZ ⟨n, hnl⟩) t.st D.L o n x1 hx1 ex1
          hcs
      hf (h.kept _)
      (fun h0 => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstM ⟨n, hnl⟩ h0)
        unfold oM
        rw [hv]
        rfl)
      (fun h0 => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstZ ⟨n, hnl⟩ h0)
        unfold oZ
        rw [hv]
        rfl)
      hk hh hlM hlZ w.1 hP part i hi

/-- One tuple of candidates of whose own words all the batched rows hold, or few draws:
tuple_or_few with the witness gone from the first arm: either there is a tuple c, one message a
member, such that all the rows that the test takes in hold of wordsT D c (words built from c alone)
and each c j is a candidate of the member's word as sent, at any seed at which Send.form gives the
record's sample row; or the values of the drawn element at which the batched claim has a witness
within e are at most lstJ e · (the number of rows − 1). -/
theorem tuple_words_or_few {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12}
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
      AllSay rdE t.st (runRows S G).toList (wordsT D c) ∧
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
  rcases tuple_or_few h hm S g G hG hLf hst rd dM dF os e hJ ht hk hh hl hz with
    ⟨w, hn, hall, hc⟩ | hfew
  · refine .inl ⟨fun j q => w.1
      ((siteOf D.st.codes a (D.mems.get j) (e0s j) (oM D.L j.val) (oZ D.L j.val) (hS j)).atJ q),
      ?_, fun j x hx seed row0 tt β hform hrows hzl hβ => ?_⟩
    · exact (allSay_congr t.st _ _ _ (words_tuple h hm g rd dM dF os e hJ _ ht hk hh e0s hS hQ w
        hn)).1 hall
    · obtain ⟨x', hx', hq⟩ := hQ j
      rw [hx] at hx'
      cases hx'
      exact hc j (e0s j) (hS j) x hx hq (hfit j) seed row0 tt β hform hrows hzl hβ
  · exact .inr hfew

end H2K.Pin

#print axioms H2K.Pin.tabP_at
#print axioms H2K.Pin.allSay_congr
#print axioms H2K.Pin.words_tabP
#print axioms H2K.Pin.words_tuple
#print axioms H2K.Pin.tuple_words_or_few
