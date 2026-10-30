-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeldAtYes.lean: code switching: BEHIND AN ACCEPT OF THE SWITCH's DECISION THE
VERIFIER's STATE HOLDS THE OOD SAMPLE OF EACH NEW SAMPLED TENANT, AND OF EACH TENANT WHOSE OOD
SAMPLE IT HELD IN FRONT: the test smpHeld (Johnson/Desc/SmpRows.lean) accepts there. For the
premise «the OOD samples are held behind» of the second tie. At the level of the state; general
in the numbers N. NO SUB-PROTOCOL IMPORTS THIS FILE.
TWO NUMBERINGS. smpHeld st book j t looks for a message that the BOOK places at (j, t): j is the
tree's PLACE IN THE BOOK. The table of joints' tenants (N.sent, N.index) are (the tree's number
through the file, the part). Every tenant in this file is a place of the book. The two are tied by
nothing here but the premise «sent» of held_behind, which is the field «sent» of what is owed on
the numbers (K2C/HandsCore.lean), with the book's number of trees in front.
  oracleNo_of_fits   in a book that fits, the message that is placed at (j, t) is the one that
                     oracleNo finds (places_inj, Johnson/Desc/Book/BookFits.lean)
  smpHeld_of · smpHeld_inv   the test, clause by clause, both ways
  admit_mark · loop_mark · sendP_mark   THE MARK «sampled»: behind the plain ground's sending each
                     new message whose notice counts an answer bears it. After the pattern of
                     admit_rows · loop_rows · sendP_rows (K2Hears/SentRows.lean), which say the
                     like of the stored rows and do not read the mark
  frontAt_of         the two ways of naming the front that a switch takes off a state are one
  yes_mark           behind an accept of the decision these messages bear the mark still (yes_front,
                     K2C/SendsOn.lean, at «a statement only grows»)
  SeedReads          A NAMED PREMISE: off a row that the program's Send.form made, with whatever
                     target, a seed can be read back, where the shape has a row and an answer
  held_new           the accept · the book in front fits · SeedReads · notice i counts an answer and
                     has a row: the test accepts behind at the place that the layout gives i
  held_old           the accept · the book in front fits · the test accepts in front at (j, t): it
                     accepts behind at (j, t)
  held_behind        both, at every member of N.index :: N.sent m 0
  smpHeld_carry      for a way out: the book's places as they were · the statement has only grown ·
                     each message's stored rows as they were: the test rides
LIMITS. SeedReads is a premise here: Johnson/ToldDescR/SeedOfForm.lean has it as a theorem (seedOf_form), which is not imported here.
That what is read back IS the seed is said by nobody.
«The book in front fits», «sent», «each of the first n notices counts an answer and has a row» and
the test in front at N.index are premises. No way out is treated but by smpHeld_carry's rule. No
soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.NewAtYes
import Johnson.Top.H0.Tw.K2C.FitsRide
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.K2Hears.SentRows
import Johnson.Top.H0.K2Hears.SampleGood
import Johnson.Desc.SmpRows
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain VerifiableInference.Desc.Ground
open _root_.Tw.K2 (switchNotices sendByL8)
open VerifiableInference.Desc.Book (BookFits places_inj)

/-! ## The test, clause by clause -/

/-- In a book that fits, the message placed at (j, t) is the one that oracleNo finds. -/
theorem oracleNo_of_fits {B : TreeBook} (h : BookFits B) {o j t : Nat}
    (ho : B.place[o]? = some (j, t)) : oracleNo B j t = some o := by
  unfold oracleNo
  cases hf : (List.range B.place.size).find? (fun o' => B.place[o']? == some (j, t)) with
  | none =>
    have hlt : o < B.place.size := (Array.getElem?_eq_some_iff.1 ho).1
    have c := List.find?_eq_none.1 hf o (List.mem_range.2 hlt)
    rw [ho] at c
    simp at c
  | some o' =>
    have e : B.place[o']? = some (j, t) := by simpa using List.find?_some hf
    rw [places_inj h e ho]

/-- What oracleNo finds is placed there. -/
theorem place_of_no {B : TreeBook} {o j t : Nat} (h : oracleNo B j t = some o) :
    B.place[o]? = some (j, t) := by
  unfold oracleNo at h
  simpa using List.find?_some h

theorem smpHeld_of {st : Statement} {bk : TreeBook} {j t o : Nat} {x : OnBytes.Oracle}
    {r : OnBytes.Row} (ho : oracleNo bk j t = some o) (hx : st.oracles[o]? = some x)
    (hm : x.sampled = true) (ha : 0 < x.shape.answers)
    (hz : x.sampleRows.size = x.shape.answers) (hr : x.sampleRows[0]? = some r)
    (hs : (seedOf st.codes x.shape r).isSome = true) : smpHeld st bk j t = true := by
  have e : smpRows st bk j t = some x.sampleRows := by
    unfold smpRows
    simp [ho, hx, hm, ha, hz]
  unfold smpHeld smpSeed
  simp only [ho, hx, e, hr, Option.bind_some, Option.isSome_map]
  exact hs

theorem smpHeld_inv {st : Statement} {bk : TreeBook} {j t : Nat} (h : smpHeld st bk j t = true) :
    ∃ (o : Nat) (x : OnBytes.Oracle) (r : OnBytes.Row), oracleNo bk j t = some o ∧
      st.oracles[o]? = some x ∧ x.sampled = true ∧ 0 < x.shape.answers ∧
      x.sampleRows.size = x.shape.answers ∧ x.sampleRows[0]? = some r ∧
      (seedOf st.codes x.shape r).isSome = true := by
  unfold smpHeld smpSeed at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨o, ho, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨rows, hrows, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨r, hr, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨sd, hsd, -⟩ := Option.map_eq_some_iff.1 hv
  unfold smpRows at hrows
  simp only [ho, hx, Option.bind_some] at hrows
  split at hrows
  · rename_i c
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
    obtain rfl := Option.some.inj hrows
    exact ⟨o, x, r, ho, hx, c.1.1, c.1.2, c.2, hr, by rw [hsd]; rfl⟩
  · cases hrows

/-! ## The mark -/

/-- What admitting lays, of the mark. -/
theorem admit_mark {L : Type} {o : Nat} {d d' : DState L} {rows : Array OnBytes.Row}
    (h : admitP d o rows = some d') : (d'.st.oracles[o]?).map (·.sampled) = some true := by
  unfold admitP at h
  split at h
  · obtain ⟨x, hx, h⟩ := optBind h
    obtain ⟨places, -, h⟩ := optBind h
    cases h
    exact congrArg (Option.map (·.sampled)) (OnBytes.Slice.admitted_same _ _ _ _ _ x hx)
  · cases h

/-- Behind the loop each message that it samples bears the mark. -/
theorem loop_mark {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      Fmt.increasing (l.map (·.1)) = true →
      sampleLoop groundG p codes seeds l ys d = some (d', left) →
      ∀ x ∈ l, (d'.st.oracles[x.1]?).map (·.sampled) = some true
  | [], ys, d, d', left, _, h => fun x hx => (by cases hx)
  | (o, s) :: l, ys, d, d', left, hi, h => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' hr
      split at h
      · cases h
      · rename_i d1 h1
        have hi' : Fmt.increasing (o :: l.map (·.1)) = true := hi
        have ha := admit_mark (show admitP d o rows = some d1 from h1)
        have hd := (loop_rows p codes seeds l ys' d1 d' left (incr_tail _ _ hi') h).2
        have hc := loop_mark p codes seeds l ys' d1 d' left (incr_tail _ _ hi') h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [hd o fun z hz => Nat.ne_of_gt (incr_lt _ _ hi' z.1 (List.mem_map_of_mem hz))]
          exact ha
        · exact hc x hx

/-- **Behind the plain ground's sending each new message whose notice counts an answer bears the
mark.** -/
theorem sendP_mark {L : Type} {p : GPar} {own : Bool} {d : DState L} {sent : Array OracleNotice}
    {r₁ r₂ : Fmt.RoundView} {x : Array Nat × List E × List E × Nat × DState L}
    (h : sendP groundG p own d sent r₁ r₂ = some x) (i : Nat) (n : OracleNotice)
    (hn : sent[i]? = some n) (ha : n.shape.answers ≠ 0) :
    (x.2.2.2.2.st.oracles[d.st.oracles.size + i]?).map (·.sampled) = some true := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := optBind h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := optBind h
  obtain ⟨seeds, -, h⟩ := optBind h
  obtain ⟨an, -, h⟩ := optBind h
  split at h
  · rename_i hc
    obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBind h
    dsimp only at h
    split at h
    · cases h
      have hr : recvP p.firstTree d sent = some (ids, d₁) := h1
      unfold recvP at hr
      split at hr
      · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 hr
        cases e
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hlen, -⟩ := mapM_zip _ _ _ hsh
        have hinc := hc.1.1.1.1.1.1.1.1.2
        rw [← VerifiableInference.Desc.Own.rising_agrees] at hinc
        have hmark := loop_mark p _ seeds _ an _ d₂ left
          (by rw [List.map_fst_zip (by omega)]; exact hinc) h2
        have hnew := OnBytes.Slice.stSent_new d.st sent i
        rw [hn] at hnew
        have hi : i < sent.size := by
          by_contra hcon
          rw [Array.getElem?_eq_none (by omega)] at hn
          cases hn
        obtain ⟨s, hs⟩ := mem_zip_of _ shapes hlen (d.st.oracles.size + i) (by
          refine List.mem_filter.2 ⟨?_, ?_⟩
          · simp only [Array.toList_map, List.mem_map]
            exact ⟨i, by simpa using hi, Nat.add_comm _ _⟩
          · rw [hnew]
            simpa using ha)
        exact hmark _ hs
      · cases hr
    · cases h
  · cases h

/-- The two ways of naming the front are one. -/
theorem frontAt_of {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : FrontOf p s x) :
    frontAt p s = some x := by
  rcases h with ⟨hp, hx⟩ | ⟨hp, a, G, ha, hG, rfl⟩ | ⟨hp, a, G, ha, hG, rfl⟩
  · simp [frontAt, hp, hx, Except.toOption]
  · simp [frontAt, hp, ha, hG]
  · simp [frontAt, hp, ha, hG]

/-- **Behind an accept of the decision the new messages that count an answer bear the mark.** -/
theorem yes_mark {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') {x : _root_.Tw.K2.Front}
    (hx : frontAt p s = some x) (i : Nat) (n : OracleNotice)
    (hn : (switchNotices x.T x.others)[i]? = some n) (ha : n.shape.answers ≠ 0) :
    ∃ xo, s'.st.oracles[x.st.oracles.size + i]? = some xo ∧ xo.sampled = true := by
  obtain ⟨r₁, r₂, x1, ids, sd, an, took, d', _, f1, hs, hg⟩ := yes_front groundKeeps_grows h
  obtain rfl : x1 = x := Option.some.inj ((frontAt_of f1).symm.trans hx)
  obtain ⟨y, h1, e1⟩ := Option.map_eq_some_iff.1 (sendP_mark hs i n hn ha)
  obtain ⟨xo, h2, g⟩ := hg.2.2 _ y h1
  exact ⟨xo, h2, g.2.1 e1⟩

/-! ## The test behind an accept -/

/-- **A named premise**: off a row that the program's Send.form made, with whatever target, a seed
can be read back, where the shape has a row and an answer. -/
def SeedReads : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (i : Nat) (row : OnBytes.Row)
    (y : E), Send.form codes s o seed i = some row → 0 < s.mainRows + s.maskRows →
    0 < s.answers → (seedOf codes s { row with target := y }).isSome = true

/-- **At a new sampled tenant.** -/
theorem held_new {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') (hB : BookFits s.book) (hS : SeedReads)
    {x : _root_.Tw.K2.Front} (hx : frontAt p s = some x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {i : Nat}
    {n : OracleNotice} (hn : (switchNotices x.T x.others)[i]? = some n)
    (ha : n.shape.answers ≠ 0) (hr : 0 < n.shape.mainRows + n.shape.maskRows) :
    smpHeld s'.st s'.book (s.book.trees.size + lay.tree.getD i 0) (lay.part.getD i 0) = true := by
  obtain ⟨x1, lay1, f1, l1, _, St⟩ := yes_seated h
  obtain rfl : x1 = x := Option.some.inj ((frontAt_of f1).symm.trans hx)
  obtain rfl : lay1 = lay := Option.some.inj (l1.symm.trans hl)
  have ho := oracleNo_of_fits (yes_fits h hB) (St.new i (Array.getElem?_eq_some_iff.1 hn).1)
  obtain ⟨xo, hxo, hmk⟩ := yes_mark h hx i n hn ha
  obtain ⟨x3, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  obtain rfl : x3 = x1 := Option.some.inj (A.front.symm.trans hx)
  have T := A.same.trans A.tables
  have hsh := T.shape (x3.st.oracles.size + i)
  have hsm := T.samples (x3.st.oracles.size + i)
  obtain ⟨bits, answers, seeds, -, -, hall, -⟩ := sent_rows A.sentBy
  obtain ⟨-, rws, hrw, hR⟩ := hall i n hn ha
  rw [hxo, A.sent.shape i, hn] at hsh
  rw [hxo, hrw] at hsm
  have e1 : xo.shape = n.shape := Option.some.inj hsh
  have e2 : xo.sampleRows = rws := Option.some.inj hsm
  have ha0 : 0 < n.shape.answers := Nat.pos_of_ne_zero ha
  obtain ⟨seed, row, yy, -, hform, hrow⟩ := hR.2 0 ha0
  refine smpHeld_of ho hxo hmk (by rw [e1]; exact ha0) (by rw [e1, e2]; exact hR.1)
    (by rw [e2]; exact hrow) ?_
  rw [e1, T.codes, A.sent.codes]
  exact hS _ _ _ _ _ _ yy hform hr ha0

/-- **At a tenant whose OOD sample was held in front.** -/
theorem held_old {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') (hB : BookFits s.book) {j t : Nat}
    (h0 : smpHeld s.st s.book j t = true) : smpHeld s'.st s'.book j t = true := by
  obtain ⟨o, x0, r, ho, hx0, hm, ha, hz, hr, hs⟩ := smpHeld_inv h0
  have hp := place_of_no ho
  obtain ⟨x1, lay1, _, _, _, St⟩ := yes_seated h
  have hp' : s'.book.place[o]? = some (j, t) := by
    rw [St.places o (Array.getElem?_eq_some_iff.1 hp).1]
    exact hp
  have ho' := oracleNo_of_fits (yes_fits h hB) hp'
  obtain ⟨x', hx', g⟩ := (yes_grows h).2.2 o x0 hx0
  obtain ⟨x3, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  have hsm := (A.same.trans A.tables).samples o
  have hlo : o < x3.st.oracles.size := by
    rw [(front_tables A.front).2]
    exact (Array.getElem?_eq_some_iff.1 hx0).1
  rw [hx', A.sent.old o hlo, (front_tables A.front).2, hx0] at hsm
  have e2 : x'.sampleRows = x0.sampleRows := Option.some.inj hsm
  refine smpHeld_of ho' hx' (g.2.1 hm) (by rw [g.1]; exact ha) (by rw [e2, g.1]; exact hz)
    (by rw [e2]; exact hr) ?_
  rw [g.1, yes_codes h]
  exact hs

/-- **At every member of N.index :: N.sent m 0.** n: how many of the sending's messages join the
group (all but the fold's mask, which is the last notice). -/
theorem held_behind {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') (hB : BookFits s.book) (hS : SeedReads)
    {x : _root_.Tw.K2.Front} (hx : frontAt p s = some x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {N : Numbers} {m n : Nat}
    (sent : sameMembers ((List.range n).map fun i =>
      (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true)
    (hall : ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
      nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows)
    (hI : smpHeld s.st s.book N.index.1 N.index.2 = true) :
    ∀ q ∈ N.index :: N.sent m 0, smpHeld s'.st s'.book q.1 q.2 = true := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact held_old h hB hI
  · unfold sameMembers at sent
    rw [Bool.and_eq_true] at sent
    have c := List.all_eq_true.1 sent.2 q hq
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < n ∧
        (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) = q := by simpa using c
    obtain ⟨nt, h1, h2, h3⟩ := hall i hi
    exact held_new h hB hS hx hl h1 h2 h3

/-- **For a way out.** -/
theorem smpHeld_carry {A B : Statement} {bk bk' : TreeBook} (hp : bk'.place = bk.place)
    (hG : Desc.Grows A B)
    (hR : ∀ i : Nat, (B.oracles[i]?).map (·.sampleRows) = (A.oracles[i]?).map (·.sampleRows))
    {j t : Nat} (h0 : smpHeld A bk j t = true) : smpHeld B bk' j t = true := by
  obtain ⟨o, x0, r, ho, hx0, hm, ha, hz, hr, hs⟩ := smpHeld_inv h0
  have ho' : oracleNo bk' j t = some o := by
    unfold oracleNo at ho ⊢
    rw [hp]
    exact ho
  obtain ⟨x', hx', g⟩ := hG.2.2 o x0 hx0
  have e := hR o
  rw [hx', hx0] at e
  have e2 : x'.sampleRows = x0.sampleRows := Option.some.inj e
  exact smpHeld_of ho' hx' (g.2.1 hm) (by rw [g.1]; exact ha) (by rw [e2, g.1]; exact hz)
    (by rw [e2]; exact hr) (by rw [g.1, hG.1]; exact hs)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sendP_mark
#print axioms VerifiableInference.Desc.First.K2.yes_mark
#print axioms VerifiableInference.Desc.First.K2.held_new
#print axioms VerifiableInference.Desc.First.K2.held_old
#print axioms VerifiableInference.Desc.First.K2.held_behind
#print axioms VerifiableInference.Desc.First.K2.smpHeld_carry
