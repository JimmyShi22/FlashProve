-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WordsNames.lean: the code switch (the kind K2): the arithmetic between the
words that tables give at a statement (`OnBytes.Means.wordsOn`, Johnson/Desc/Means/ItemsTab.lean)
and the typed entries of a new sending (`entAt`, `coordAt`, `idxOf`:
Johnson/Top/H/SwitchNames.lean). It serves the premises hF and h0, and one step of hm, of
`rowsHoldT_of_says` (Johnson/Top/H0/K2Caller/RowsSay.lean). Definitions, and theorems with proofs.

Main names:
  `wordsOn_idxOf`: where the statement has the shape sh at the message o, the word at the index
    row + 2 ^ ceilLog2 rows * place of a table is the table's entry at that row and place.
    `wordsOn_coordAt`: the same at `coordAt` of a coordinate of the shape's message.
    `idxReads`: the same, worded as the body of `IdxReads cs`
    (Johnson/Top/H0/Tw/K2C/WordsAtNew.lean).
  `ShapesAt cs l n0 st`: the statement st has the codes cs, and at the number n0 + i the shape of
    the sending's i-th message.
  `wordsOn_entAt`: the same at the three numbers of a typed entry of the sending.
  `name_in_tables` (hF): under `ShapesAt` each typed entry's name lies in `tabAll st`.
  `CodesFit cs l on`: every message length of cs is a power of two, and at the members i with
    "on i" the code of each table that has a row is in its list. `Taken`: the member is g or takes
    a kept member: h0 asks `CodesFit` of these alone.
  `entry_of_word`: under `ShapesAt` and `CodesFit`, a place of a new message's table at which the
    words are not 0 has the three numbers of a typed entry.
  `NewNumbers`: g and the messages that take the kept members are messages of the new sending.
  `words_zero_outside` (h0): outside `Inside` (Johnson/Top/H0/K2Hands/HandsOn.lean) the words
    are 0.
  `outside_at_rows`: where h0 has something to do: a kept member whose rows are no power of two.
  `words_zero_first`: h0 at the words `wordsFirst` (Johnson/Desc/Sound/WordsAt.lean).
  `Try.shapes`, `Try.no_entry`: a try at made-up numbers: at a code whose message length, 3, is no
    power of two, `ShapesAt` holds, a word inside the table is not 0, and its three numbers are no
    typed entry's: so `entry_of_word` fails without `CodesFit.lengths`.
  The two premises in the binders of `rowsHoldT_of_says`: WordsNamesAt.lean.
Limits. `ShapesAt`, `CodesFit`, `NewNumbers`, `Names`, `NamesK`, `SlotsAll` and `Slots` are
premises: nobody shows them here. The theorems hold of the words of ANY tables T: nothing is said of
a witness. Whether h0 needs `CodesFit.lengths` is not settled here: this proof spends it. (That test
is asked of the first chain's codes by `pubBy`, Johnson/Desc/ProofFile/Pub.lean, and by `startOk`,
Johnson/Desc/First/State.lean; that a later state still has these codes is not shown here.) Tools:
they would stay proved if the protocol were another. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SaysText
import Johnson.Top.H.SwitchMaps
import Johnson.Desc.Means.ItemsLen
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open OnBytes.Means (Words wordsOn tableSize realRows CodeThere place_lt_ell)
open VerifiableInference.Desc.First.K2Hands (nameOf Inside InBits InClaim Names NamesK SlotsAll
  Slots)

/-! ## 1 The word at the index of a row and a place -/

section
variable {K : Type} [CommRing K]

/-- **The word at the index row + 2 ^ ceilLog2 rows * place is the table's entry at that row
and place**, where the statement has the shape sh at the message o. -/
theorem wordsOn_idxOf (st : Statement) (T : ℕ → Bool → ℕ → ℕ → K) (o : ℕ) (sh : OracleShape)
    (hs : (st.oracles[o]?).map (·.shape) = some sh) (part : Part) (ell : ℕ)
    (x : Fin (sh.rows part) × Fin ell) :
    wordsOn st T o part (idxOf (sh.rows part) ell x) = T o (part == .mask) x.1.val x.2.val := by
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hs
  have rb : st.rowBits o part = ceilLog2 (sh.rows part) := by
    unfold Statement.rowBits
    rw [hy, ← e]
  have rr : realRows st o part = sh.rows part := by
    unfold realRows
    rw [hy, ← e]
  unfold wordsOn
  rw [rb, rr, idxOf_mod, idxOf_div, if_pos x.1.isLt]

/-- The same at the table and the index of a coordinate of the shape's message. -/
theorem wordsOn_coordAt (cs : Codes) (st : Statement) (T : ℕ → Bool → ℕ → ℕ → K) (o : ℕ)
    (sh : OracleShape) (hs : (st.oracles[o]?).map (·.shape) = some sh) (j : (portCode cs sh).J) :
    wordsOn st T o (coordAt cs sh j).1 (coordAt cs sh j).2 =
      Sum.elim (fun x => T o false x.1.val x.2.val) (fun x => T o true x.1.val x.2.val)
        (j : (Fin sh.mainRows × Fin (pMain cs sh).ell) ⊕ (Fin sh.maskRows × Fin (pMask cs sh).ell))
        := by
  change (Fin sh.mainRows × Fin (pMain cs sh).ell) ⊕ (Fin sh.maskRows × Fin (pMask cs sh).ell) at j
  rcases j with x | x
  · exact wordsOn_idxOf st T o sh hs .main _ x
  · exact wordsOn_idxOf st T o sh hs .mask _ x

end

/-- The same, worded as the body of `IdxReads cs` (Johnson/Top/H0/Tw/K2C/WordsAtNew.lean), to the
letter. -/
theorem idxReads (cs : Codes) : ∀ (S : Statement) (T : Nat → Bool → Nat → Nat → GE) (o : Nat)
    (s : OracleShape), (S.oracles[o]?).map (·.shape) = some s →
    ∀ j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell),
      wordsOn S T o (coordAt cs s j).1 (coordAt cs s j).2 =
        Sum.elim (fun q => T o false q.1.val q.2.val) (fun q => T o true q.1.val q.2.val) j :=
  fun S T o s hs j => wordsOn_coordAt cs S T o s hs j

/-! ## 2 The new sending's shapes in the statement -/

section
variable (cs : Codes) (l : List (OracleShape × ℕ)) (n0 : ℕ)

/-- **The statement has the codes cs, and at the number n0 + i the shape of the sending's i-th
message.** -/
structure ShapesAt (st : Statement) : Prop where
  codes : st.codes = cs
  shape : ∀ i : Fin l.length, (st.oracles[n0 + i.val]?).map (·.shape) = some (l.get i).1

variable {cs l n0} {st : Statement}

/-- The word at the three numbers of a typed entry of the sending. -/
theorem wordsOn_entAt {K : Type} [CommRing K] (N : ShapesAt cs l n0 st)
    (T : ℕ → Bool → ℕ → ℕ → K) (n : (sigOf cs l).Ent) :
    wordsOn st T (n0 + (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
      Sum.elim (fun x => T (n0 + n.1.val) false x.1.val x.2.val)
        (fun x => T (n0 + n.1.val) true x.1.val x.2.val)
        (n.2 : (Fin (l.get n.1).1.mainRows × Fin (pMain cs (l.get n.1).1).ell) ⊕
          (Fin (l.get n.1).1.maskRows × Fin (pMask cs (l.get n.1).1).ell)) :=
  wordsOn_coordAt cs st T (n0 + n.1.val) (l.get n.1).1 (N.shape n.1) n.2

theorem ShapesAt.there (N : ShapesAt cs l n0 st) (i : Fin l.length) :
    n0 + i.val < st.oracles.size := by
  obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 (N.shape i)
  exact (Array.getElem?_eq_some_iff.1 hy).1

/-- The size of a new message's table that has a row. -/
theorem ShapesAt.size (N : ShapesAt cs l n0 st) (i : Fin l.length) (part : Part)
    (h : 0 < (l.get i).1.rows part) :
    tableSize st (n0 + i.val) part =
      2 ^ (ceilLog2 ((l.get i).1.rows part) + ceilLog2 (ellOf cs (l.get i).1 part)) := by
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 (N.shape i)
  have hne : ((l.get i).1.rows part == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have hh : st.has (n0 + i.val) part = true := by
    unfold Statement.has
    rw [hy]
    show decide (0 < y.shape.rows part) = true
    rw [e]
    exact decide_eq_true h
  have rb : st.rowBits (n0 + i.val) part = ceilLog2 ((l.get i).1.rows part) := by
    unfold Statement.rowBits
    rw [hy, ← e]
  have pb : st.placeBits (n0 + i.val) part = ceilLog2 (ellOf cs (l.get i).1 part) := by
    unfold Statement.placeBits
    rw [hy]
    show (if (y.shape.rows part == 0) = true then 0 else _) = _
    rw [e, hne, if_neg Bool.false_ne_true, N.codes]
    cases part <;> rfl
  unfold tableSize Statement.tableBits
  rw [if_pos hh, rb, pb]

/-- **(hF) Each typed entry's name lies in the tables of the statement.** -/
theorem name_in_tables (N : ShapesAt cs l n0 st) (n : (sigOf cs l).Ent) :
    nameOf cs l (fun i => n0 + i) n ∈ tabAll st := by
  rw [mem_tabAll]
  refine ⟨N.there n.1, ?_⟩
  obtain ⟨hl, h1, h2⟩ := inTab_entAt cs l n
  show (entAt cs l n).2.2 < tableSize st (n0 + n.1.val) (entAt cs l n).2.1
  have h1' : (entAt cs l n).2.2 % 2 ^ ceilLog2 ((l.get n.1).1.rows (entAt cs l n).2.1) <
      (l.get n.1).1.rows (entAt cs l n).2.1 := h1
  have h2' : (entAt cs l n).2.2 / 2 ^ ceilLog2 ((l.get n.1).1.rows (entAt cs l n).2.1) <
      ellOf cs (l.get n.1).1 (entAt cs l n).2.1 := h2
  rw [N.size n.1 _ (Nat.lt_of_le_of_lt (Nat.zero_le _) h1'), pow_add]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1
    (lt_of_lt_of_le h2' (le_two_pow_ceilLog2 _)) |>.trans_eq (Nat.mul_comm _ _)

/-! ## 3 Outside `Inside` the words are 0 -/

/-- **The codes fit**, at the members i of the sending with "on i": the programs' test on the codes'
message lengths passes, and the number of the code of each such member's table THAT HAS A ROW is
in its list. (A shape without main rows names "no
code", `noId`: of such a table nothing can be asked.) -/
structure CodesFit (cs : Codes) (l : List (OracleShape × ℕ)) (on : Fin l.length → Prop) : Prop where
  lengths : cs.lengthsOk = true
  main : ∀ i : Fin l.length, on i → 0 < (l.get i).1.mainRows → (l.get i).1.code < cs.base.size
  mask : ∀ i : Fin l.length, on i → 0 < (l.get i).1.maskRows →
    (l.get i).1.maskCode < cs.mask.size

theorem CodesFit.mono {cs : Codes} {l : List (OracleShape × ℕ)} {on on' : Fin l.length → Prop}
    (C : CodesFit cs l on) (h : ∀ i, on' i → on i) : CodesFit cs l on' :=
  ⟨C.lengths, fun i hi => C.main i (h i hi), fun i hi => C.mask i (h i hi)⟩

/-- **A place of a new message's table at which the words are not 0 has the three numbers of a typed
entry.** -/
theorem entry_of_word {K : Type} [CommRing K] (N : ShapesAt cs l n0 st)
    {on : Fin l.length → Prop} (C : CodesFit cs l on)
    (T : ℕ → Bool → ℕ → ℕ → K) (i : Fin l.length) (hi : on i) (part : Part) (J : ℕ)
    (hJ : J < tableSize st (n0 + i.val) part) (hne : wordsOn st T (n0 + i.val) part J ≠ 0) :
    ∃ n : (sigOf cs l).Ent, entAt cs l n = (i.val, part, J) := by
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 (N.shape i)
  have rb : st.rowBits (n0 + i.val) part = ceilLog2 ((l.get i).1.rows part) := by
    unfold Statement.rowBits
    rw [hy, ← e]
  have rr : realRows st (n0 + i.val) part = (l.get i).1.rows part := by
    unfold realRows
    rw [hy, ← e]
  have hr : J % 2 ^ ceilLog2 ((l.get i).1.rows part) < (l.get i).1.rows part := by
    by_contra hr
    apply hne
    unfold wordsOn
    rw [rb, rr, if_neg hr]
  have hpos : 0 < (l.get i).1.rows part := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  have hT : CodeThere st (n0 + i.val) part := by
    intro z hz
    rw [hy] at hz
    rw [← Option.some.inj hz, e, N.codes]
    cases part
    · exact C.main i hi hpos
    · exact C.mask i hi hpos
  have hp := place_lt_ell (by rw [N.codes]; exact C.lengths) hT hJ
  have he : OnBytes.Means.ellOf st (n0 + i.val) part = ellOf cs (l.get i).1 part := by
    unfold OnBytes.Means.ellOf
    rw [hy]
    dsimp only
    rw [e, N.codes]
    cases part <;> rfl
  rw [rb, he] at hp
  exact ent_of_inTab cs l (i.val, part, J) ⟨i.isLt, hr, hp⟩

/-- **g and the messages that take the kept members are messages of the new sending.** -/
structure NewNumbers (l : List (OracleShape × ℕ)) (n0 : ℕ) (W : SwitchFrame) : Prop where
  g : ∃ i : Fin l.length, W.g = n0 + i.val
  kept : ∀ k ∈ W.kept, ∃ i : Fin l.length, k.anew = n0 + i.val

/-- The member i of the sending is g, or takes a kept member. -/
def Taken (l : List (OracleShape × ℕ)) (n0 : ℕ) (W : SwitchFrame) (i : Fin l.length) : Prop :=
  n0 + i.val = W.g ∨ ∃ k ∈ W.kept, n0 + i.val = k.anew

section
variable {s : Sg} {Kp : Type} [Fintype Kp] [DecidableEq Kp]
  {iJ : (s.cKept Kp).J → (sigOf cs l).Ent} {iQ : (s.cKept Kp).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : Kp → ℕ} {pl : Kp → KeptPlace}
  {aKept : Kp → ℕ}

/-- **(h0) OUTSIDE `Inside` THE WORDS ARE 0**: at every place of the statement's tables, for the
words of any tables T. -/
theorem words_zero_outside {K : Type} [CommRing K] (N : ShapesAt cs l n0 st)
    (C : CodesFit cs l (Taken l n0 W)) (U : NewNumbers l n0 W)
    (D : Names s Kp cs l iJ iQ W (fun i => n0 + i) aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s Kp cs l iJ iQ W (fun i => n0 + i) mem row pl aKept)
    (A : SlotsAll Kp W mem row pl)
    (Sl : ∀ a k, W.kept[a]? = some k → Slots s Kp cs l W (fun i => n0 + i) mem row a k)
    (T : ℕ → Bool → ℕ → ℕ → K) :
    ∀ x ∈ tabAll st, ¬ Inside s W pl x.1 x.2.1 x.2.2 → wordsOn st T x.1 x.2.1 x.2.2 = 0 := by
  rintro ⟨o, part, J⟩ hx hin
  by_contra hne
  have hJ : J < tableSize st o part := ((mem_tabAll st _).1 hx).2
  -- at a message of the new sending the three numbers are a typed entry's
  have key : ∀ i : Fin l.length, o = n0 + i.val → Taken l n0 W i →
      ∃ n : (sigOf cs l).Ent, entAt cs l n = (i.val, part, J) := by
    rintro i rfl hi
    exact entry_of_word N C T i hi part J hJ hne
  have atG : o = W.g → ∃ n : (sigOf cs l).Ent, (entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = part ∧
      (entAt cs l n).2.2 = J := by
    intro hg
    obtain ⟨i, hi⟩ := U.g
    obtain ⟨n, hn⟩ := key i (hg.trans hi) (Or.inl hi.symm)
    refine ⟨n, (D.gIs n).1 ?_, by rw [hn], by rw [hn]⟩
    rw [hn]
    exact hi.symm
  apply hin
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro hg hp
    obtain ⟨n, h1, h2, h3⟩ := atG hg
    rw [← h3]
    exact D.mainIn n h1 (h2.trans hp)
  · intro hg hp
    obtain ⟨n, h1, h2, h3⟩ := atG hg
    rw [← h3]
    exact D.restIn n h1 (h2.trans hp)
  · intro κ ho hp
    obtain ⟨i, hi⟩ := U.kept (pl κ) (List.mem_of_getElem? (A.member κ))
    obtain ⟨n, hn⟩ := key i (ho.trans hi)
      (Or.inr ⟨pl κ, List.mem_of_getElem? (A.member κ), hi.symm⟩)
    have h1 : (entAt cs l n).1 = 1 + mem κ := (DK.anewIs κ n).1 (by rw [hn]; exact hi.symm)
    have h := DK.keptIn κ n h1 (by rw [hn]; exact hp)
    rwa [hn] at h
  · intro hg hp
    obtain ⟨n, h1, h2, h3⟩ := atG hg
    rw [← h3]
    exact D.mainIn n h1 (h2.trans hp)
  · intro k hk ho hp
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hk
    obtain ⟨i, hi⟩ := U.kept k hk
    obtain ⟨n, hn⟩ := key i (ho.trans hi) (Or.inr ⟨k, hk, hi.symm⟩)
    have h1 : (entAt cs l n).1 = 1 + a := ((Sl a k ha).anewIs n).1 (by rw [hn]; exact hi.symm)
    have h := (Sl a k ha).entry n h1 (by rw [hn]; exact hp)
    rwa [hn] at h

/-- (h0) at the words that a witness gives through the first chain's statement and book. -/
theorem words_zero_first (N : ShapesAt cs l n0 st) (C : CodesFit cs l (Taken l n0 W))
    (U : NewNumbers l n0 W)
    (D : Names s Kp cs l iJ iQ W (fun i => n0 + i) aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s Kp cs l iJ iQ W (fun i => n0 + i) mem row pl aKept)
    (A : SlotsAll Kp W mem row pl)
    (Sl : ∀ a k, W.kept[a]? = some k → Slots s Kp cs l W (fun i => n0 + i) mem row a k)
    {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (book : TreeBook)
    (w : VerifiableInference.Desc.Wit Cells Tok VerifiableInference.Desc.Sound.MsgT) :
    ∀ x ∈ tabAll st, ¬ Inside s W pl x.1 x.2.1 x.2.2 →
      VerifiableInference.Desc.Sound.wordsFirst arr st book w x.1 x.2.1 x.2.2 = 0 :=
  words_zero_outside N C U D DK A Sl _

end

end

/-- **Where h0 has something to do**: where a kept member's rows are fewer than 2 ^ (its row bits),
the index "rows" of the main table of the message that takes it lies outside `Inside`. -/
theorem outside_at_rows {Kp : Type} (s : Sg) (W : SwitchFrame) (pl : Kp → KeptPlace) (k : KeptPlace)
    (hk : k ∈ W.kept) (h : k.rows < 2 ^ k.rowBits) : ¬ Inside s W pl k.anew .main k.rows := by
  intro hin
  have h1 := (hin.2.2 k hk rfl rfl).1
  rw [Nat.mod_eq_of_lt h] at h1
  exact Nat.lt_irrefl _ h1

/-! ## 4 A try, at made-up numbers -/

namespace Try

/-- One code of main rows, whose message length is no power of two. -/
def cs3 : Codes := { base := #[⟨2, 3, 0⟩] }
/-- One main row of that code. -/
def sh3 : OracleShape := { code := 0, mainRows := 1 }
def l3 : List (OracleShape × ℕ) := [(sh3, 0)]
def st3 : Statement := { codes := cs3, oracles := #[{ shape := sh3 }] }

theorem shapes : ShapesAt cs3 l3 0 st3 where
  codes := rfl
  shape := fun i => by
    have h : i.val < 1 := i.isLt
    obtain ⟨_ | i, hi⟩ := i
    · rfl
    · exact absurd h (by simp)

theorem lengths_no : cs3.lengthsOk = false := by decide +kernel

theorem size3 : tableSize st3 0 .main = 4 := by decide

theorem word3 : wordsOn st3 (fun _ _ _ _ => (1 : GE)) 0 .main 3 = 1 := by
  have h : 3 % 2 ^ st3.rowBits 0 .main < realRows st3 0 .main := by decide
  unfold wordsOn
  rw [if_pos h]

/-- **Without the test on the lengths `entry_of_word` fails**: the index 3 lies in the table, the
word there is not 0, and no typed entry has these three numbers. -/
theorem no_entry : ¬ ∃ n : (sigOf cs3 l3).Ent, entAt cs3 l3 n = (0, Part.main, 3) := by
  rintro ⟨n, hn⟩
  obtain ⟨hl, -, h2⟩ := (inTab_iff cs3 l3 (0, Part.main, 3)).2 ⟨n, hn⟩
  have h3 : 3 / 2 ^ ceilLog2 (sh3.rows Part.main) < ellOf cs3 sh3 Part.main := h2
  exact absurd h3 (by decide)

end Try

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.outside_at_rows
#print axioms VerifiableInference.Desc.First.K2Caller.words_zero_first
#print axioms VerifiableInference.Desc.First.K2Caller.Try.shapes
#print axioms VerifiableInference.Desc.First.K2Caller.Try.no_entry
#print axioms VerifiableInference.Desc.First.K2Caller.wordsOn_idxOf
#print axioms VerifiableInference.Desc.First.K2Caller.wordsOn_coordAt
#print axioms VerifiableInference.Desc.First.K2Caller.idxReads
#print axioms VerifiableInference.Desc.First.K2Caller.wordsOn_entAt
#print axioms VerifiableInference.Desc.First.K2Caller.name_in_tables
#print axioms VerifiableInference.Desc.First.K2Caller.entry_of_word
#print axioms VerifiableInference.Desc.First.K2Caller.words_zero_outside
