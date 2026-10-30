-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/WantsStated.lean: CONDITIONAL: NO KIND IS NAMED BUT IN TWO SMALL
LAWS ON THE MERGES: THE MAKER OF THE BOOK: OF ALL THE STRETCHES THAT IT LAYS FOR THE FIRST CHAIN,
THOSE THAT ONE PART OF A MEMBER IN A LINK SPENDS ARE, BY NAME AND COUNT, WHAT THE MAKER STATES FOR
THAT PART; and from there, under sentences on the book, the shorter test rowNamed (RowNamed.lean) at
that member's place. On public data alone. One definition with code; twelve statements with their
proofs.

  stated              what the maker lays for a part that is no merge, by name and count: A SECOND
                      TEXT of partWants (Honest/BookEntries.lean), HELD TO THE FIRST BY stated_is
  stated_is           CONDITIONAL (the row bears the mask row's name): by cases
  wants_stated        CONDITIONAL: of a list of parts' stretches those with one spender
  numbered_at · planParts_at · flat_parts_at   the parts at one address
  rowNamed_of_parts · partNamed_of   the row's test from each part's; a part's from five sentences
  ownerOf_name        an oracle message as an owner bears the name that the caller gave
  wants_at_plain      CONDITIONAL: **the stretches of linksWants and loneWants with the spender
                      ⟨b.place, i⟩, as entries, by name and count = stated ‹part i of planParts b›**
  ends_kind · no_merge_of_kind   mergesByName's field ends lists parts of the kinds K4 and K11 alone
  rowNamed_of_pick    CONDITIONAL: nine premises: **rowNamed B (B.rowsOf 0) b.place ps 0 = true**

THE NINE PREMISES OF rowNamed_of_pick. hn: no two members of the list stand at one place · hb: b is
a member · hl: b stands in a link · hm: none of b's addresses is among the merges · hPick: the
entries of B that part j of b spends are the stretches of linksWants and loneWants with that
spender: two of the conjuncts in which other authors' pick_whole ends (Honest/BookRowStretch.lean;
not imported) · h3: no row of the first chain's table stands at b's addresses · h4: every entry
whose spender stands at b's place is a spent one · hplain: the parts of ps take nothing and carry
nothing · hst: what the maker states for b's parts is what the parts of ps state that they spend.
NONE IS PROVED HERE.

Called, of other authors (Honest/BookRowKit.lean, namespace ProofFile.Honest.BookRow;
Honest/BookSharedKit.lean): partWants_spender · wants_all · wants_other · planParts_place ·
numbered_from · cut_at · loneWants_spender · linksWants_at · nodup_eraseDups · nodup_filter_map ·
opt_bind · opt_map. Two short names stand in ProofFile.Honest too with other types (partWants_spender,
pick): here the kit's are written with BookRow in front.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. A part that is a merge is not spoken of; nor a member outside a link. No module
of the kind K5 and none under the library's folder ThirdParty/ lies in the import closure; thirteen
of the kind K3's do, through RowNamed.lean. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.Small.RowNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.BookRow (wants_all wants_other planParts_place cut_at)
open ProofFile.Honest.BookShared (opt_bind opt_map)

/-- **What the book's maker lays for a part that is no merge, by name and count.** A second text of
`partWants` (Honest/BookEntries.lean), held to it by `stated_is`. -/
def stated (p : PartAt) : List (String × Due) :=
  if p.ownScalars == 0 then []
  else if !p.isSum then [(runName maskRowRun p.addr "scalars", ⟨0, p.ownScalars⟩)]
  else if p.endScalars == 0 then [(runName maskRowRun p.addr "sum", ⟨0, p.ownScalars⟩)]
  else [(runName maskRowRun p.addr "sum", ⟨0, p.ownScalars - p.endScalars⟩),
    (runName maskRowRun p.addr "ends", ⟨0, p.endScalars⟩)]

/-- It is the maker's own text, read by name and count. -/
theorem stated_is (row idx : MsgAt) (hr : row.name = maskRowRun) (p : PartAt) (j t : Nat) :
    ((partWants row idx false p j t).1.map Want.entry).map Ahead.named = stated p := by
  unfold partWants stated
  by_cases h1 : (p.ownScalars == 0) = true
  · simp [h1]
  · by_cases h2 : (!p.isSum) = true
    · simp [h1, h2, Want.entry, Ahead.named, hr]
    · by_cases h3 : (p.endScalars == 0) = true
      · simp [h1, h2, h3, Want.entry, Ahead.named, hr]
      · simp [h1, h2, h3, Want.entry, Ahead.named, hr]

variable {S Cl V W X : Type}

/-! ## 1 From the maker's stretches at one address to what it states there -/

/-- **Of a list of parts' stretches those with one spender, by name and count, are what the maker
states for the parts at that address.** -/
theorem wants_stated (row idx : MsgAt) (merges : List Addr) (hr : row.name = maskRowRun) (a : Addr)
    (hm : merges.contains a = false) : ∀ (qs : List PartAt) (j t : Nat),
    (((partsWants row idx merges qs j t).1.filter fun w => w.spender == a).map (·.entry)).map
      Ahead.named = (qs.filter fun q => q.addr == a).flatMap stated
  | [], _, _ => rfl
  | q :: qs, j, t => by
    have ih := wants_stated row idx merges hr a hm qs (j + q.ownScalars)
      (partWants row idx (merges.contains q.addr) q j t).2
    have e : (partsWants row idx merges (q :: qs) j t).1 =
        (partWants row idx (merges.contains q.addr) q j t).1 ++
          (partsWants row idx merges qs (j + q.ownScalars)
            (partWants row idx (merges.contains q.addr) q j t).2).1 := rfl
    rw [e, List.filter_append, List.map_append, List.map_append, ih]
    by_cases hq : q.addr = a
    · have hb : (q.addr == a) = true := by simp [hq]
      rw [wants_all (fun w hw => (BookRow.partWants_spender _ _ _ _ _ _ w hw).trans hq), hq, hm,
        stated_is row idx hr, List.filter_cons_of_pos (p := fun q : PartAt => q.addr == a) hb,
        List.flatMap_cons]
    · have hb : ¬ (q.addr == a) = true := by simp [hq]
      rw [wants_other
          (fun w hw e' => hq ((BookRow.partWants_spender _ _ _ _ _ _ w hw).symm.trans e')),
        List.filter_cons_of_neg (p := fun q : PartAt => q.addr == a) hb]
      rfl

/-! ## 2 The parts at one address -/

/-- Parts numbered from k on: the parts at the number i. -/
theorem numbered_at (p : Place) : ∀ (L : List (List (String × Nat))) (k i : Nat),
    (((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)).filter fun q => q.addr == ⟨p, k + i⟩) =
      ((((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))[i]?).toList)
  | [], _, _ => rfl
  | r :: L, k, 0 => by
    have hrest : (((L.zipIdx (k + 1)).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)).filter
        fun q => q.addr == ⟨p, k + 0⟩) = [] := by
      refine List.filter_eq_nil_iff.2 fun q hq => ?_
      obtain ⟨i, hi, e⟩ := ProofFile.Honest.BookRow.numbered_from p L (k + 1) q hq
      rw [e]
      have : ¬ i = k := by omega
      simp [this]
    rw [List.zipIdx_cons, List.map_cons, List.filter_cons_of_pos (by simp), hrest]
    rfl
  | r :: L, k, i + 1 => by
    have ih := numbered_at p L (k + 1) i
    have e : k + (i + 1) = k + 1 + i := by omega
    rw [List.zipIdx_cons, List.map_cons, List.filter_cons_of_neg (by simp), e, ih]
    rfl

/-- The parts of a sub-protocol at its own place and the number i. -/
theorem planParts_at (b : Block S Cl) (i : Nat) :
    ((planParts b).filter fun q => q.addr == ⟨b.place, i⟩) = ((planParts b)[i]?).toList := by
  have h := numbered_at b.place
    (stretchesBy (b.rounds.map fun r => (r.entry.name, scalarsIn r)) (partsCut b)) 0 i
  rw [Nat.zero_add] at h
  exact h

/-- Of the parts of a list of sub-protocols at places without a twin, those at one member's place
are that member's. -/
theorem flat_parts_at {b : Block S Cl} {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup)
    (hb : b ∈ bs) (i : Nat) :
    ((bs.flatMap planParts).filter fun q => q.addr == ⟨b.place, i⟩) =
      ((planParts b)[i]?).toList := by
  obtain ⟨t, e, h1, h2⟩ := cut_at bs hn hb
  have none_of : ∀ (l : List (Block S Cl)), (∀ x ∈ l, x.place ≠ b.place) →
      ((l.flatMap planParts).filter fun q => q.addr == ⟨b.place, i⟩) = [] := by
    intro l hl
    refine List.filter_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
    have h3 := planParts_place hq2
    have h4 : q.addr ≠ ⟨b.place, i⟩ := fun e' => hl x hx (by rw [← h3, e'])
    simp [h4]
  rw [e, List.flatMap_append, List.flatMap_cons, List.filter_append, List.filter_append,
    none_of _ h1, none_of _ h2, planParts_at, List.nil_append, List.append_nil]

/-! ## 3 From the parts' test to the row's -/

/-- The row's test from the test at each part. -/
theorem rowNamed_of_parts (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Place) :
    ∀ (ps : List (Part V W X)) (j : Nat),
      (∀ i p, ps[i]? = some p → partNamed B rows p ⟨a, j + i⟩ = true) →
      rowNamed B rows a ps j = true
  | [], _, _ => rfl
  | p :: ps, j, h => by
    have h0 := h 0 p rfl
    have ih := rowNamed_of_parts B rows a ps (j + 1) fun i q hq => by
      have := h (i + 1) q hq
      rwa [show j + (i + 1) = j + 1 + i by omega] at this
    show (partNamed B rows p ⟨a, j⟩ && rowNamed B rows a ps (j + 1)) = true
    rw [ih, Bool.and_true]
    exact h0

/-! ## 4 The first chain's stretches at one part of a member that stands in a link -/

/-- An oracle message as an owner bears the name that the caller gave. -/
theorem ownerOf_name {name : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {label : String} {pk : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pk = some m) : m.name = name := by
  unfold ownerOf at h
  obtain ⟨x, -, h⟩ := opt_bind h
  obtain ⟨a, -, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨fr, -, h⟩ := opt_map h
  rw [← h]

/-- **OF ALL THE STRETCHES OF THE FIRST CHAIN, THOSE THAT ONE PART OF A MEMBER IN A LINK SPENDS ARE,
BY NAME AND COUNT, WHAT THE MAKER STATES FOR THAT PART.** -/
theorem wants_at_plain {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {M : Merges} {a : List Want × Nat}
    (ha : linksWants bs c later idx M.ends (bs.filterMap (·.place.link)).eraseDups 0 = .ok a)
    (hn : (bs.map (·.place)).Nodup) {b : Block S Cl} (hb : b ∈ bs) {l : Nat}
    (hl : b.place.link = some l) (i : Nat) (hm : M.ends.contains ⟨b.place, i⟩ = false) :
    (((a.1 ++ (loneWants idx M.lone
        ((bs.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
          fun w => w.spender == ⟨b.place, i⟩).map (·.entry)).map Ahead.named =
      (((planParts b)[i]?).toList).flatMap stated := by
  have hlone : ((loneWants idx M.lone
      ((bs.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1.filter
        fun w => w.spender == ⟨b.place, i⟩) = [] := wants_other fun w hw e => by
    obtain ⟨q, hq, e2⟩ := BookRow.loneWants_spender idx M.lone _ a.2 w hw
    obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
    have h3 := planParts_place hq2
    have h4 := (List.mem_filter.1 hx).2
    have h5 : x.place = b.place := by rw [← h3, ← e2, e]
    rw [h5, hl] at h4
    cases h4
  have hmem : l ∈ (bs.filterMap (·.place.link)).eraseDups :=
    List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨b, hb, hl⟩)
  obtain ⟨row, t', hrow, hf⟩ := BookRow.linksWants_at _ 0 a
    (BookRow.nodup_eraseDups _ _ (Nat.le_refl _)) hmem ha
  rw [List.filter_append, hlone, List.append_nil, hf ⟨b.place, i⟩ hl]
  have hw := wants_stated row idx M.ends (ownerOf_name hrow) ⟨b.place, i⟩ hm
    ((bs.filter fun b => b.place.link == some l).flatMap planParts) 0 t'
  refine Eq.trans hw ?_
  rw [flat_parts_at (BookRow.nodup_filter_map _ _ _ hn)
    (List.mem_filter.2 ⟨hb, by simp [hl]⟩) i]

/-! ## 5 No merge outside two kinds -/

theorem ends_kind {bs : List (Block S Cl)} {a : Addr} (h : a ∈ (mergesByName bs).ends) :
    a.place.kind = .K4 ∨ a.place.kind = .K11 := by
  unfold mergesByName at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  have h2 := (List.mem_filter.1 hp).2
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h2
  exact h2.2

theorem no_merge_of_kind (bs : List (Block S Cl)) (a : Addr) (h4 : a.place.kind ≠ .K4)
    (h11 : a.place.kind ≠ .K11) : (mergesByName bs).ends.contains a = false := by
  cases hc : (mergesByName bs).ends.contains a with
  | false => rfl
  | true =>
    rcases ends_kind (List.contains_iff_mem.1 hc) with h | h
    · exact absurd h h4
    · exact absurd h h11

/-! ## 6 The test at one part -/

/-- The test at one part, from its five clauses said as sentences. -/
theorem partNamed_of (B : ProverCoinCounts) (rows : List (Addr × Due)) (p : Part V W X) (a : Addr)
    (h1 : p.takes = ⟨0, 0⟩) (h2 : p.carries = []) (h3 : dueAt rows a = ⟨0, 0⟩)
    (h4 : ∀ e ∈ B.ahead, e.spender = a → e.once = true)
    (h5 : (BookRow.pick a B.ahead).map Ahead.named = p.spends) : partNamed B rows p a = true := by
  have hall : ∀ e ∈ B.ahead.filter (fun e => e.spender == a), e.once = true := fun e he =>
    h4 e (List.mem_filter.1 he).1 (beq_iff_eq.1 (List.mem_filter.1 he).2)
  have hpk : BookRow.pick a B.ahead = B.ahead.filter fun e => e.spender == a :=
    List.filter_eq_self.2 hall
  rw [hpk] at h5
  unfold partNamed
  rw [h1, h2, h3, h5, List.all_eq_true.2 hall]
  simp

/-- **THE SHORTER TEST ON THE BOOK AT A MEMBER's PLACE, FROM SENTENCES ON THE BOOK AND THE MAKER.**
CONDITIONAL: the nine premises stand in the file's head. -/
theorem rowNamed_of_pick {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {M : Merges} {B : ProverCoinCounts}
    (hn : (bs.map (·.place)).Nodup) {b : Block S Cl} (hb : b ∈ bs) {l : Nat}
    (hl : b.place.link = some l) (hm : ∀ i, M.ends.contains ⟨b.place, i⟩ = false)
    (hPick : ∃ (idx : MsgAt) (a : List Want × Nat),
      linksWants bs c later idx M.ends (bs.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead =
        ((a.1 ++ (loneWants idx M.lone
          ((bs.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
            fun w => w.spender == ⟨b.place, j⟩).map (·.entry))
    (h3 : ∀ i, dueAt B.first ⟨b.place, i⟩ = ⟨0, 0⟩)
    (h4 : ∀ e ∈ B.ahead, e.spender.place = b.place → e.once = true)
    (ps : List (Part V W X)) (hplain : ∀ p ∈ ps, p.takes = ⟨0, 0⟩ ∧ p.carries = [])
    (hst : (planParts b).map stated = ps.map (·.spends)) :
    rowNamed B (B.rowsOf 0) b.place ps 0 = true := by
  obtain ⟨idx, a, ha, hpk⟩ := hPick
  refine rowNamed_of_parts B (B.rowsOf 0) b.place ps 0 fun i p hp => ?_
  rw [Nat.zero_add]
  have hmem : p ∈ ps := List.mem_of_getElem? hp
  have e1 : ((planParts b).map stated)[i]? = some p.spends := by
    rw [hst, List.getElem?_map, hp]
    rfl
  rw [List.getElem?_map] at e1
  obtain ⟨q, hq, hqs⟩ := Option.map_eq_some_iff.1 e1
  refine partNamed_of B (B.rowsOf 0) p ⟨b.place, i⟩ (hplain p hmem).1 (hplain p hmem).2 (h3 i)
    (fun e he hs => h4 e he (by rw [hs])) ?_
  rw [hpk i, wants_at_plain ha hn hb hl i (hm i), hq]
  show stated q ++ [] = p.spends
  rw [List.append_nil, hqs]

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.stated_is
#print axioms ProofFile.Honest.Small.wants_stated
#print axioms ProofFile.Honest.Small.numbered_at
#print axioms ProofFile.Honest.Small.planParts_at
#print axioms ProofFile.Honest.Small.flat_parts_at
#print axioms ProofFile.Honest.Small.rowNamed_of_parts
#print axioms ProofFile.Honest.Small.ownerOf_name
#print axioms ProofFile.Honest.Small.wants_at_plain
#print axioms ProofFile.Honest.Small.ends_kind
#print axioms ProofFile.Honest.Small.no_merge_of_kind
#print axioms ProofFile.Honest.Small.partNamed_of
#print axioms ProofFile.Honest.Small.rowNamed_of_pick
