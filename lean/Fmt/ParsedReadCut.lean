-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedReadCut.lean: the parts of which this library's readers cut a chain, each against the
parsed record: what they accept fits the declared form and is written back to the bytes that were
read. Theorems, for Run/ParsedCutLaws.lean [not in this library].

The readers of this library that hash (`roundX`, Fmt/Rules8X.lean; `cutStepX`, Run/ParseLaxX.lean)
cut a round with four hash-free readers: `slice` with `whole (readItems …)` for the message,
`readNonce`, `readList`, and `rdOpening` for each opening, at lists of positions that they have
drawn. `RoundParsed.of` (Fmt/Parsed.lean) lays what they hold into a record. This file says of each
of the four what its part of the record is, that it has the form that `RoundParsed.fits` asks, and
that the writer gives the bytes back; then it joins the four. It also ties three of them to the
readers by the numbers (Fmt/ParsedRead.lean), which are the same cuts told their numbers. No
Mathlib, neither directly nor through the imports. No hash is called.

1. What the file contains. Theorems; four small definitions: `nonceOf`, `listedOf` (the nonce and
the listed positions of a record, from what a reader holds: the text of `RoundParsed.of`),
`listedOk` (the clause of `RoundParsed.fits` on the listed positions, by a name),
`RoundParsed.Form` (the form of a round, part by part, against an entry, a cut into items and a list
for the openings).

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   The ties. `OpenParsed.read_opening`: the reader of an opening at the two numbers of a list is
     `rdOpening` at that list, its value laid into the record (by definition).
     `rdNonceAt_readNonce`: the reader of a nonce is `readNonce`, its value turned by `nonceOf`.
     `rdMany_map`, `readList_many`: where `readList` accepts, the reader of as many low-byte words
     gives the listed positions.
   An opening: `open_fits`, `listOK_pos`, `opening_cut` (asked: the list is in order, `listOK`, and
     has at most "most" members); `zip_fst_snd`, `OpenParsed.of_cut`.
   A message: `message_cut`.
   A nonce: `cuts_nonce` (asked: at most eight bytes). The listed positions: `map_toNat_ofNat`,
     `list_cut` (asked: at most eight bytes).
   The draws: `times_len`, `times_all`, `drawRound_len`, `drawRound_lt`: a round draws as many
     positions as its entry says, each below 2 ^ logN. `increasing_of_pairwise`, `listedOk_listOf`:
     so the list of the draws has the form that `fits` asks of listed positions.
   A round: `RoundParsed.fits_iff_form`; `RoundParsed.bytes_eq`, `round_join`.

4. What is not claimed. Nothing on a whole cut: that is Run/ParsedCutLaws.lean
[not in this library]'s. Nothing on the hash, on the proof of work, on a Merkle path or a root.
`opening_cut` takes the list of positions as it comes: that it is the list of the draws is the
caller's. Some small facts stand a second time in this library, over Mathlib or in another
namespace: `times_len` and the length of a round's positions (Run/CostFmtProofs.lean:
`CostP.times_len`, `CostP.drawRound_poss`), `zip_fst_snd` (Run/WalkTieProofs.lean).

Terms: lean/GLOSSARY.md.

-/
import Fmt.ParsedReadLaws
import Fmt.Rules6Laws

namespace Fmt

/-! ## 1. The ties to the readers by the numbers -/

/-- The reader of an opening by the numbers, at the two numbers of a list xs of positions, is the
library's parser of an opening at xs, its value laid into the record. -/
theorem OpenParsed.read_opening (f : Fld) (salt : Nat) (sh : Shape) (xs : List Nat) :
    OpenParsed.read f sh.W salt (xs.length, (walkPlaces sh.a xs).length) =
      rdMap (fun x => ⟨x.1, x.2⟩) (rdOpening f salt sh xs) := rfl

/-- the nonce of a parsed round, from the number that a reader of this library holds -/
def nonceOf (work nonce : Nat) : Option UInt64 :=
  if work == 0 then none else some (UInt64.ofNat nonce)

/-- The reader of a nonce by the numbers is the library's, its value turned by `nonceOf`. -/
theorem rdNonceAt_readNonce (P : Plan) (work : Nat) :
    rdNonceAt P.nonce work = rdMap (nonceOf work) (readNonce P work) := by
  funext b i
  unfold rdNonceAt readNonce rdMap nonceOf
  by_cases hw : (work == 0) = true
  · simp only [if_pos hw]
    rfl
  · simp only [if_neg hw]
    show (Option.map _ (Option.map _ (readLE P.nonce b i))) = _
    cases readLE P.nonce b i <;> rfl

/-- n values by a turned reader are n values, each turned. -/
theorem rdMany_map {α β : Type} (f : α → β) (r : Rd α) : ∀ (n : Nat) (b : ByteArray) (i : Nat),
    rdMany (rdMap f r) n b i = (rdMany r n b i).map fun y => (y.1.map f, y.2)
  | 0, _, _ => rfl
  | n + 1, b, i => by
    rcases h1 : r b i with _ | ⟨x, k⟩
    · have h2 : rdMap f r b i = none := by
        unfold rdMap
        rw [h1]
        rfl
      unfold rdMany
      rw [h1, h2]
      rfl
    · have h2 : rdMap f r b i = some (f x, k) := by
        unfold rdMap
        rw [h1]
        rfl
      unfold rdMany
      rw [h1, h2]
      simp only
      rw [rdMany_map f r n b k]
      cases rdMany r n b k <;> rfl

/-- the listed positions of a parsed round, from the list that a reader of this library holds -/
def listedOf (posB poss : Nat) (l : List Nat) : List UInt64 :=
  if posB == 0 || poss == 0 then [] else l.map UInt64.ofNat

/-- Where the library's reader of the listed positions accepts, the reader by the numbers, told
their number, gives them. -/
theorem readList_many (P : Plan) (poss : Nat) (l : List Nat) (b : ByteArray) (i j : Nat)
    (h : readList P poss l b i = some ((), j)) :
    rdMany (rdLow P.posB) (listedOf P.posB poss l).length b i =
      some (listedOf P.posB poss l, j) := by
  unfold readList at h
  unfold listedOf
  by_cases hc : (P.posB == 0 || poss == 0) = true
  · rw [if_pos hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [if_pos hc]
    rfl
  · rw [if_neg hc] at h
    rcases h1 : rdMany (readLE P.posB) l.length b i with _ | ⟨l', k⟩
    · rw [h1] at h
      exact absurd h (by simp)
    · rw [h1] at h
      simp only at h
      by_cases he : (l' == l) = true
      · rw [if_pos he] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have he' : l' = l := beq_iff_eq.1 he
        subst he'
        simp only [if_neg hc, List.length_map]
        show rdMany (rdMap UInt64.ofNat (readLE P.posB)) l'.length b i = _
        rw [rdMany_map, h1]
        rfl
      · rw [if_neg he] at h
        exact absurd h (by simp)

/-! ## 2. An opening -/

/-- The form of an opening, from its parts'. -/
theorem open_fits (f : Fld) (W salt most : Nat) (o : OpenParsed) (h1 : 1 ≤ o.cols.length)
    (h2 : o.cols.length ≤ most)
    (h3 : ∀ c ∈ o.cols, (c.1.length = W ∧ ∀ w ∈ c.1, w.toNat < f.p) ∧ c.2.size = salt)
    (h4 : ∀ d ∈ o.given, d.size = 32) : o.fits f W salt most = true := by
  simp only [OpenParsed.fits, Fld.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  exact ⟨⟨⟨h1, h2⟩, fun c hc => ⟨⟨(h3 c hc).1.1, (h3 c hc).1.2⟩, (h3 c hc).2⟩⟩, h4⟩

/-- A list of positions that is in order has a member. -/
theorem listOK_pos (a : Nat) : ∀ xs : List Nat, listOK a xs = true → 1 ≤ xs.length
  | [], h => absurd h Bool.false_ne_true
  | _ :: _, _ => Nat.succ_le_succ (Nat.zero_le _)

/-- AN OPENING OF A CUT. What `rdOpening` reads at a list xs that is in order and has at most "most"
members fits, and its writing is the bytes that were read. -/
theorem opening_cut (f : Fld) (salt most : Nat) (sh : Shape) (xs : List Nat) (b : ByteArray)
    (i j : Nat) (cs : List (List UInt64 × ByteArray)) (gv : List ByteArray)
    (h : rdOpening f salt sh xs b i = some ((cs, gv), j)) (hx : listOK sh.a xs = true)
    (hm : xs.length ≤ most) :
    (⟨cs, gv⟩ : OpenParsed).fits f sh.W salt most = true ∧
      j = i + (OpenParsed.bytes ⟨cs, gv⟩).size ∧ b.extract i j = OpenParsed.bytes ⟨cs, gv⟩ := by
  have t : OpenParsed.read f sh.W salt (xs.length, (walkPlaces sh.a xs).length) b i =
      some (⟨cs, gv⟩, j) := by
    rw [OpenParsed.read_opening]
    show (rdOpening f salt sh xs b i).map _ = _
    rw [h]
    rfl
  obtain ⟨⟨a0, a2, a4⟩, c⟩ := cuts_open f sh.W salt _ b i ⟨cs, gv⟩ j t
  have a1' : cs.length = xs.length := congrArg Prod.fst a0
  have p := listOK_pos sh.a xs hx
  exact ⟨open_fits f sh.W salt most ⟨cs, gv⟩ (by show 1 ≤ cs.length; omega)
    (by show cs.length ≤ most; omega) a2 a4, c⟩

/-- A list of pairs is the zip of its two halves. -/
theorem zip_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | x :: l => congrArg (List.cons x) (zip_fst_snd l)

/-- The record of an opening as a lenient cut hands it on (Run/ParseLax.lean, Run/ParseLaxX.lean).
-/
theorem OpenParsed.of_cut (cs : List (List UInt64 × ByteArray)) (gv : List ByteArray)
    (r : ByteArray) (sn : List (Nat × Nat × ByteArray)) (j : Nat) :
    OpenParsed.of ⟨cs.map Prod.fst, cs.map Prod.snd, gv, r, sn, j⟩ = some ⟨cs, gv⟩ := by
  unfold OpenParsed.of
  simp only [List.length_map, beq_self_eq_true, if_true, zip_fst_snd]

/-! ## 3. A message -/

/-- A MESSAGE OF A CUT. n bytes are sliced off and read, whole, as the items ts. -/
theorem message_cut (f : Fld) (ts : List Item) (b msg : ByteArray) (i n : Nat) (vals : List ItemValue)
    (h1 : slice b i n = some msg) (h2 : whole (readItems f ts) msg = some vals) :
    (vals.length = ts.length ∧ ∀ y ∈ vals.zip ts, y.1.fitsItem f y.2 = true) ∧
      i + n = i + (cat (vals.map spellGot)).size ∧
      b.extract i (i + n) = cat (vals.map spellGot) := by
  obtain ⟨a1, a2⟩ := whole_cuts (cuts_items f ts) msg vals h2
  have a1' : msg = cat (vals.map spellGot) := a1
  unfold slice at h1
  by_cases hb : i + n ≤ b.size
  · rw [if_pos hb] at h1
    have e := Option.some.inj h1
    have s : (b.extract i (i + n)).size = n := by
      rw [ByteArray.size_extract]
      omega
    rw [← a1', ← e]
    exact ⟨a2, by rw [s], rfl⟩
  · rw [if_neg hb] at h1
    exact absurd h1 (by simp)

/-! ## 4. A nonce and the listed positions -/

/-- A NONCE OF A CUT. -/
theorem cuts_nonce (P : Plan) (work : Nat) (hn : P.nonce ≤ 8) :
    Cuts (readNonce P work) (fun v => spNonce P.nonce (nonceOf work v)) fun v =>
      okNonce P.nonce work (nonceOf work v) := by
  intro b i v j h
  have t : rdNonceAt P.nonce work b i = some (nonceOf work v, j) := by
    rw [rdNonceAt_readNonce]
    show (readNonce P work b i).map _ = _
    rw [h]
    rfl
  exact cuts_nonceAt P.nonce work hn b i _ j t

/-- Numbers below 2 ^ 64, as words and back. -/
theorem map_toNat_ofNat (l : List Nat) (h : ∀ v ∈ l, v < 2 ^ 64) :
    (l.map UInt64.ofNat).map (·.toNat) = l := by
  rw [List.map_map]
  have e : ∀ v ∈ l, ((·.toNat) ∘ UInt64.ofNat) v = id v := fun v hv => toNat_ofNat_lt v (h v hv)
  rw [List.map_congr_left e, List.map_id]

/-- THE LISTED POSITIONS OF A CUT. The library's reader compares them with the list l. Where
positions are listed, l's members are below 256 ^ posB. -/
theorem list_cut (P : Plan) (poss : Nat) (l : List Nat) (hn : P.posB ≤ 8) (b : ByteArray)
    (i j : Nat) (h : readList P poss l b i = some ((), j)) :
    ((P.posB == 0 || poss == 0) = false → ∀ v ∈ l, v < 256 ^ P.posB) ∧
      j = i + (cat ((listedOf P.posB poss l).map fun x => lowBytes P.posB x.toNat)).size ∧
      b.extract i j = cat ((listedOf P.posB poss l).map fun x => lowBytes P.posB x.toNat) := by
  unfold readList at h
  unfold listedOf
  by_cases hc : (P.posB == 0 || poss == 0) = true
  · rw [if_pos hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [if_pos hc]
    exact ⟨fun h0 => absurd hc (by rw [h0]; simp), rfl, extract_same b i⟩
  · rw [if_neg hc] at h
    rcases h1 : rdMany (readLE P.posB) l.length b i with _ | ⟨l', k⟩
    · rw [h1] at h
      exact absurd h (by simp)
    · rw [h1] at h
      simp only at h
      by_cases he : (l' == l) = true
      · rw [if_pos he] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have he' : l' = l := beq_iff_eq.1 he
        subst he'
        obtain ⟨⟨-, a1⟩, a2, a4⟩ := cuts_count (cuts_of_only (only_readLE P.posB hn)) _ b i l' k h1
        have e : (l'.map UInt64.ofNat).map (fun x => lowBytes P.posB x.toNat) =
            l'.map (lowBytes P.posB) := by
          rw [List.map_map]
          exact List.map_congr_left fun v hv => by
            show lowBytes P.posB (UInt64.ofNat v).toNat = _
            rw [toNat_ofNat_lt v (lt_word _ _ hn (a1 v hv))]
        simp only [if_neg hc]
        rw [e]
        exact ⟨fun _ => a1, a2, a4⟩
      · rw [if_neg he] at h
        exact absurd h (by simp)

/-! ## 5. The draws -/

/-- A draw, n times, gives n values. -/
theorem times_len {α : Type} (x : Dr α) :
    ∀ (n : Nat) (r : Row) (p : Nat), (x.times n r p).1.length = n
  | 0, _, _ => rfl
  | n + 1, r, _ => congrArg Nat.succ (times_len x n r _)

/-- What holds of every value of a draw holds of each of its n values. -/
theorem times_all {α : Type} (x : Dr α) (q : α → Prop) (hq : ∀ r c, q (x r c).1) :
    ∀ (n : Nat) (r : Row) (c : Nat), ∀ a ∈ (x.times n r c).1, q a
  | 0, _, _, _, ha => absurd ha (by show ¬ _ ∈ []; simp)
  | n + 1, r, c, a, ha => by
    have ha' : a ∈ (x r c).1 :: (x.times n r (x r c).2).1 := ha
    rcases List.mem_cons.1 ha' with rfl | h
    · exact hq r c
    · exact times_all x q hq n r _ a h

/-- A round draws as many positions as its entry says. -/
theorem drawRound_len (f : Fld) (e : Entry) (k : Kind) (row : Row) :
    (drawRound f e k row).poss.length = e.poss := times_len _ _ _ _

/-- Every position that a round draws is below 2 ^ logN. -/
theorem drawRound_lt (f : Fld) (e : Entry) (k : Kind) (row : Row) :
    ∀ p ∈ (drawRound f e k row).poss, p < 2 ^ e.logN :=
  times_all (drawPos e.logN) (fun p => p < 2 ^ e.logN)
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _)) _ _ _

/-- The library's two ways to say "increasing". -/
theorem increasing_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → increasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: c :: l, h => by
    have h' := List.pairwise_cons.1 h
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h'.1 c (by simp), increasing_of_pairwise (c :: l) h'.2⟩

/-- the clause of `RoundParsed.fits` on the listed positions -/
def listedOk (S : PlanSetting) (e : Entry) (L : List UInt64) : Bool :=
  if S.posB == 0 || e.poss == 0 then L.isEmpty
  else !L.isEmpty && decide (L.length ≤ e.poss) &&
    increasing (L.map (·.toNat)) &&
    L.all fun p =>
      decide (p.toNat < 2 ^ e.logN) && decide (p.toNat < 256 ^ S.posB)

/-- The list of a round's draws, as listed positions, has the form that `fits` asks. -/
theorem listedOk_listOf (S : PlanSetting) (e : Entry) (ps : List Nat) (h8 : S.posB ≤ 8)
    (hl : ps.length = e.poss) (hb : ∀ p ∈ ps, p < 2 ^ e.logN)
    (hw : (S.posB == 0 || e.poss == 0) = false → ∀ v ∈ listOf ps, v < 256 ^ S.posB) :
    listedOk S e (listedOf S.posB e.poss (listOf ps)) = true := by
  unfold listedOk listedOf
  by_cases hc : (S.posB == 0 || e.poss == 0) = true
  · simp only [if_pos hc]
    rfl
  · have hc' : (S.posB == 0 || e.poss == 0) = false := by simpa using hc
    have w := hw hc'
    have m := map_toNat_ofNat (listOf ps) fun v hv => lt_word _ _ h8 (w v hv)
    have hp : e.poss ≠ 0 := by
      intro h0
      rw [h0] at hc
      simp at hc
    obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
      cases ps with
      | nil => exact absurd hl.symm hp
      | cons p ps' => exact ⟨p, ps', rfl⟩
    have hne : listOf (p :: ps') ≠ [] := by
      intro h0
      have := (listOf_mem (p :: ps') p).2 (by simp)
      rw [h0] at this
      cases this
    simp only [if_neg hc, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      decide_eq_true_eq, List.all_eq_true, List.length_map]
    rw [m]
    refine ⟨⟨⟨?_, ?_⟩, increasing_of_pairwise _ (listOf_incr _)⟩, ?_⟩
    · intro h0
      exact hne (List.map_eq_nil_iff.1 h0)
    · rw [← hl]
      exact listOf_len _
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      rw [toNat_ofNat_lt v (lt_word _ _ h8 (w v hv))]
      exact ⟨hb v ((listOf_mem _ v).1 hv), w v hv⟩

/-! ## 6. A round -/

/-- A round's bytes, with the nonce's bytes by their own name. -/
theorem RoundParsed.bytes_eq (P : Plan) (x : RoundParsed) :
    x.bytes P = cat (x.vals.map spellGot) ++ spNonce P.nonce x.nonce ++
      cat (x.listed.map fun y => lowBytes P.posB y.toNat) ++
      cat (x.opens.map OpenParsed.bytes) := by
  obtain ⟨vals, nonce, listed, opens⟩ := x
  cases nonce <;> rfl

/-- The form of a round, part by part: against an entry e, a cut of the message into items, and the
list w of what the openings must look like. At a declared round's entry, cut and list it is what
`RoundParsed.fits` asks (`RoundParsed.fits_iff_form`). It is said apart so that it can be said of a
round of any description, whose cut need not be the one of a declared round. -/
def RoundParsed.Form (S : PlanSetting) (e : Entry) (items : List Item) (w : List (Nat × Nat × Nat))
    (x : RoundParsed) : Prop :=
  (x.vals.length = items.length ∧ ∀ y ∈ x.vals.zip items, y.1.fitsItem S.field y.2 = true) ∧
    okNonce S.nonce e.work x.nonce ∧ listedOk S e x.listed = true ∧ x.opens.length = w.length ∧
    ∀ y ∈ x.opens.zip w, y.1.fits S.field y.2.1 y.2.2.1 y.2.2.2 = true

/-- A round fits a declared round exactly where it has the form of that round's entry, items and
openings. -/
theorem RoundParsed.fits_iff_form (S : PlanSetting) (rd : DeclaredRound) (x : RoundParsed) :
    x.fits S rd = true ↔ x.Form S rd.entry rd.items (wantOpens S rd) := by
  obtain ⟨vals, nonce, listed, opens⟩ := x
  simp only [RoundParsed.fits, RoundParsed.Form, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩
    refine ⟨⟨beq_iff_eq.1 a1, List.all_eq_true.1 a2⟩, ?_, a4, beq_iff_eq.1 a5,
      List.all_eq_true.1 a6⟩
    cases nonce with
    | none => exact beq_iff_eq.1 a3
    | some v =>
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at a3
      exact a3
  · rintro ⟨v1, n1, l1, o1, o2⟩
    refine ⟨⟨⟨⟨⟨beq_iff_eq.2 v1.1, List.all_eq_true.2 v1.2⟩, ?_⟩, l1⟩, beq_iff_eq.2 o1⟩,
      List.all_eq_true.2 o2⟩
    cases nonce with
    | none => exact beq_iff_eq.2 n1
    | some v =>
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
      exact n1

/-- Four parts, each written to the bytes from its place to the next, make a round that is written
to the bytes from the first place to the last. -/
theorem round_join (P : Plan) (b : ByteArray) (i0 i1 i2 i3 i4 : Nat) (x : RoundParsed)
    (v3 : i1 = i0 + (cat (x.vals.map spellGot)).size)
    (v4 : b.extract i0 i1 = cat (x.vals.map spellGot))
    (n3 : i2 = i1 + (spNonce P.nonce x.nonce).size) (n4 : b.extract i1 i2 = spNonce P.nonce x.nonce)
    (l3 : i3 = i2 + (cat (x.listed.map fun y => lowBytes P.posB y.toNat)).size)
    (l4 : b.extract i2 i3 = cat (x.listed.map fun y => lowBytes P.posB y.toNat))
    (o3 : i4 = i3 + (cat (x.opens.map OpenParsed.bytes)).size)
    (o4 : b.extract i3 i4 = cat (x.opens.map OpenParsed.bytes)) :
    i4 = i0 + (x.bytes P).size ∧ b.extract i0 i4 = x.bytes P := by
  refine ⟨?_, ?_⟩
  · rw [RoundParsed.bytes_eq, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append]
    omega
  · rw [RoundParsed.bytes_eq, ← v4, ← n4, ← l4, ← o4,
      ← ByteArray.extract_eq_extract_append_extract i1 (by omega) (by omega),
      ← ByteArray.extract_eq_extract_append_extract i2 (by omega) (by omega),
      ← ByteArray.extract_eq_extract_append_extract i3 (by omega) (by omega)]

end Fmt
