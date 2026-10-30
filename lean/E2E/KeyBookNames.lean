-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookNames.lean: the name of an entry of the key file's book of coins fixes the data from
which the name is built: two keys with the same name are the same key (`name_inj`). A book (`ProverCoinCounts`,
in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is public data on the coins of a prover's
parts. An entry (`Ahead`) is a block of the coins of one part, its owner (`owner`), that one other
part, its spender (`spender`), is given too; it has a name, a string. A part is named by its address
(`Addr`): a place (`Place`, Johnson/Desc/Block.lean: chain, link, piece and kind) and the part's
number at that place. One of the frame's tests on a book fails where two entries have the same name
(`ProverCoinCounts.clauses`, "two entries bear one name"). The names are built by `runName` and `carriedName`
(Johnson/Desc/ProofFile/Honest/ForKinds.lean) from a string for the owner's message, a string for
the use, a message's number, and addresses written in decimal digits. With the theorems below that
test can be proved from the entries' keys, without evaluating the names and comparing them as
strings: E2E/KeyBookTile.lean and E2E/KeyBookPasses.lean do so. The theorems are on lists of
characters, at all numbers and at every string for the use; no protocol and no prover occurs.

  `name_inj`: two keys with the same name (`Key.name`) are equal
  `runName_key`, `carriedName_key`: the characters of the string `runName w.word d use` are the
    name of the key `.run w (quadOf d) use`; those of `carriedName o k d` are the name of the key
    `.carried k (quadOf o) (quadOf d)`
  `words_read`: take two quadruples written by `quadChars`, each followed by a character that is no
    digit and then by any characters. If the two lists are equal, so are the quadruples, the two
    characters and what follows them
  `read_off`: the same for two lists of digits in place of the written quadruples
  `link_read`: two links written by `linkChars`, each followed by '.' and then by any characters:
    if the two lists are equal, so are the links and what follows
  `digits_inj`: two numbers with the same decimal digits are equal
  `words_toList`: the characters of an address's string (`Addr.words`, ForKinds.lean) are
    `quadChars` of its quadruple
  `take_five`: the first five characters of a key's name are `Key.five` of the key
  `digitChar_toNat`, `digitChar_inj`: for n below 10 the digit of n has the code 48 + n; so two
    numbers below 10 with the same digit are equal
  `digits_step`, `digits_ne_nil`, `digits_isDigit`, `toString_digits`: `digits n` is one digit for
    n below 10, and otherwise `digits (n / 10)` followed by the digit of n % 10; it is not empty;
    each of its characters is a digit (`Char.isDigit`); it is the list of characters of `toString n`
  `Key`: a definition: what a name is built from. `.run w d use`, for an entry that the book marks
    as spent (`once` is true): which of the four owners' strings, the spender's quadruple, the use.
    `.carried k o d`, for an entry that it marks as carried (`once` is false): the message's number,
    the sender's quadruple, the spender's
  `Key.name`, `Key.five`: definitions: a key's name as a list of characters; five characters for
    each of the four owners' strings and five for a carried key
  `Who`, `Who.word`: definitions: the four owners' strings of the key file's book, as a type with
    four values, and the string of each: `countsMaskRun` (E2E/KeyBook.lean), `indexMaskRun`,
    `foldMaskRun`, `splitMaskRun` (ForKinds.lean)
  `Quad`, `quadOf`: definitions: a quadruple is chain, link, piece and part's number; the quadruple
    of an address. The place's kind is not in it
  `digits`, `linkChars`, `quadChars`: definitions: as lists of characters: a number's decimal
    digits; a link ('-' if there is none); a quadruple, with '.' between the four

By what. `name_inj` compares the first five characters (`take_five`), which decide between spent
and carried and among the four owners' strings; it then cancels the equal beginnings and reads the
numbers off by `read_off`, `words_read` and `digits_inj`; the use is what is left. `words_read`
calls `read_off` three times and `link_read` once, with `digits_inj`. `digits_inj` is by strong
induction along `digits_step`. Lemmas of the Lean libraries carry the facts on digits:
`Nat.toDigits_eq_if`, `Nat.length_toDigits_pos`, `Nat.isDigit_of_mem_toDigits`,
`Nat.toString_eq_ofList_toDigits`. Of other files of this library only definitions are used: those
named above.

Limits. A place's kind is not in a name: two addresses whose places differ only in the kind have the
same quadruple and give the same name. The places that E2E/KeyPlaces.lean defines for the key file
differ pairwise in chain, link or piece, as their definitions show; no theorem here states it. The
four owners' strings and the first word of a carried name, "message ", are told apart by their first
five characters: that is a fact on these five strings, proved by `decide` in `take_five`, and the
proof breaks if one of them gets another beginning. `maskRowRun` (ForKinds.lean) is not among the
four; it begins with the same five characters as `splitMaskRun`. Nothing is stated of a book: that
an entry's name is a key's name, and that the entries' names differ, is stated in
E2E/KeyBookTile.lean (`lay_keyed`, `lay_names`) and E2E/KeyBookPasses.lean (`looks_keyed`,
`others_keys`, `others_names`). No property of a protocol is stated: nothing on completeness,
soundness or hiding.
-/
import E2E.KeyBook

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open ProofFile.Honest (Addr runName carriedName indexMaskRun foldMaskRun splitMaskRun)

/-! ## 1 Digits -/

/-- The decimal digits of a number, as a list of characters. -/
def digits (n : Nat) : List Char := Nat.toDigits 10 n

theorem digitChar_toNat (n : Nat) (h : n < 10) : n.digitChar.toNat = 48 + n := by
  interval_cases n <;> rfl

theorem digitChar_inj {n m : Nat} (hn : n < 10) (hm : m < 10) (h : n.digitChar = m.digitChar) :
    n = m := by
  have := congrArg Char.toNat h
  rw [digitChar_toNat n hn, digitChar_toNat m hm] at this
  omega

theorem digits_step (n : Nat) :
    digits n = if n < 10 then [n.digitChar] else digits (n / 10) ++ [(n % 10).digitChar] :=
  Nat.toDigits_eq_if (by decide)

theorem digits_ne_nil (n : Nat) : digits n ≠ [] := by
  intro h
  have := Nat.length_toDigits_pos (b := 10) (n := n)
  unfold digits at h
  rw [h] at this
  exact absurd this (by decide)

/-- **Two numbers with the same decimal digits are equal.** -/
theorem digits_inj : ∀ n m : Nat, digits n = digits m → n = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m h
    rw [digits_step n, digits_step m] at h
    by_cases hn : n < 10 <;> by_cases hm : m < 10
    · simp only [hn, hm, if_true] at h
      exact digitChar_inj hn hm (List.cons.inj h).1
    · simp only [hn, hm, if_true, if_false] at h
      have hl := congrArg List.length h
      have hp : 0 < (digits (m / 10)).length := List.length_pos_iff.2 (digits_ne_nil _)
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega
    · simp only [hn, hm, if_true, if_false] at h
      have hl := congrArg List.length h
      have hp : 0 < (digits (n / 10)).length := List.length_pos_iff.2 (digits_ne_nil _)
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega
    · simp only [hn, hm, if_false] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      have e1 := ih (n / 10) (by omega) (m / 10) h1
      have e2 := digitChar_inj (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (List.cons.inj h2).1
      omega

theorem digits_isDigit (n : Nat) : ∀ c ∈ digits n, c.isDigit = true := fun _ hc =>
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem toString_digits (n : Nat) : (toString n).toList = digits n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  rfl

/-- **A list of digits before a character that is no digit can be read off.** If x and x' hold
digits only, s and s' are no digits, and x, s, r in a row are the same list as x', s', r', then
x = x', s = s' and r = r'. -/
theorem read_off : ∀ {x x' : List Char} {s s' : Char} {r r' : List Char},
    (∀ c ∈ x, c.isDigit = true) → (∀ c ∈ x', c.isDigit = true) → s.isDigit = false →
    s'.isDigit = false → x ++ s :: r = x' ++ s' :: r' → x = x' ∧ s = s' ∧ r = r'
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
  | [], c :: t, s, _, _, _, _, hx', hs, _, h => by
    have e : s = c := (List.cons.inj h).1
    have := hx' c List.mem_cons_self
    rw [← e, hs] at this
    cases this
  | a :: t, [], _, s', _, _, hx, _, _, hs', h => by
    have e : a = s' := (List.cons.inj h).1
    have := hx a List.mem_cons_self
    rw [e, hs'] at this
    cases this
  | a :: t, c :: t', _, _, _, _, hx, hx', hs, hs', h => by
    obtain ⟨e, h'⟩ := List.cons.inj h
    obtain ⟨h1, h2, h3⟩ := read_off (fun d hd => hx d (List.mem_cons_of_mem _ hd))
      (fun d hd => hx' d (List.mem_cons_of_mem _ hd)) hs hs' h'
    exact ⟨by rw [e, h1], h2, h3⟩

/-! ## 2 The string of an address -/

/-- A quadruple: chain, link, piece and the part's number. -/
abbrev Quad : Type := Nat × Option Nat × Nat × Nat

/-- The quadruple of an address: what `Addr.words` writes. It leaves out the place's kind. -/
def quadOf (a : Addr) : Quad := (a.place.chain, a.place.link, a.place.piece, a.part)

/-- A link as characters: '-' if there is none, otherwise its decimal digits. -/
def linkChars : Option Nat → List Char
  | none => ['-']
  | some n => digits n

/-- A quadruple as characters: the four in order, with '.' between them. -/
def quadChars (q : Quad) : List Char :=
  digits q.1 ++ '.' :: (linkChars q.2.1 ++ '.' :: (digits q.2.2.1 ++ '.' :: digits q.2.2.2))

theorem words_toList (a : Addr) : a.words.toList = quadChars (quadOf a) := by
  unfold Addr.words quadChars quadOf
  have hl : (toString ((Option.map toString a.place.link).getD "-")).toList =
      linkChars a.place.link := by
    cases a.place.link with
    | none => rfl
    | some n => exact toString_digits n
  have hd : (toString ".").toList = ['.'] := rfl
  simp only [String.toList_append, toString_digits, hl, hd, List.cons_append, List.append_assoc,
    List.nil_append]

theorem link_read {l l' : Option Nat} {r r' : List Char}
    (h : linkChars l ++ '.' :: r = linkChars l' ++ '.' :: r') : l = l' ∧ r = r' := by
  cases l with
  | none =>
    cases l' with
    | none => exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
    | some m =>
      have := read_off (x := []) (x' := digits m) (s := '-') (s' := '.') (fun _ hc => by cases hc)
        (digits_isDigit m) rfl rfl h
      exact absurd this.2.1 (by decide)
  | some n =>
    cases l' with
    | none =>
      have := read_off (x := digits n) (x' := []) (s := '.') (s' := '-') (digits_isDigit n)
        (fun _ hc => by cases hc) rfl rfl h
      exact absurd this.2.1 (by decide)
    | some m =>
      obtain ⟨h1, -, h3⟩ := read_off (digits_isDigit n) (digits_isDigit m) rfl rfl h
      exact ⟨by rw [digits_inj n m h1], h3⟩

/-- **A written quadruple before a character that is no digit fixes chain, link, piece and part,**
and also that character and what follows it. -/
theorem words_read {q q' : Quad} {s s' : Char} {r r' : List Char} (hs : s.isDigit = false)
    (hs' : s'.isDigit = false) (h : quadChars q ++ s :: r = quadChars q' ++ s' :: r') :
    q = q' ∧ s = s' ∧ r = r' := by
  obtain ⟨c, l, pc, pt⟩ := q
  obtain ⟨c', l', pc', pt'⟩ := q'
  simp only [quadChars, List.append_assoc, List.cons_append] at h
  obtain ⟨h1, -, h⟩ := read_off (digits_isDigit c) (digits_isDigit c') rfl rfl h
  obtain ⟨h2, h⟩ := link_read h
  obtain ⟨h3, -, h⟩ := read_off (digits_isDigit pc) (digits_isDigit pc') rfl rfl h
  obtain ⟨h4, h5, h6⟩ := read_off (digits_isDigit pt) (digits_isDigit pt') hs hs' h
  rw [digits_inj c c' h1, h2, digits_inj pc pc' h3, digits_inj pt pt' h4]
  exact ⟨rfl, h5, h6⟩

/-! ## 3 Keys and names -/

/-- The four strings for an owner's message in the names of the key file's book. -/
inductive Who where
  | counts | index | fold | split
  deriving DecidableEq, Repr

/-- The string of each of the four. -/
def Who.word : Who → String
  | .counts => countsMaskRun
  | .index => indexMaskRun
  | .fold => foldMaskRun
  | .split => splitMaskRun

/-- **An entry's key:** what its name is built from. -/
inductive Key where
  /-- coins that are spent: the owner's string; the spender's quadruple; the use -/
  | run (w : Who) (d : Quad) (use : String)
  /-- coins that are carried: the message's number; the sender's quadruple; the spender's -/
  | carried (k : Nat) (o d : Quad)
  deriving DecidableEq

/-- A key's name, as a list of characters. -/
def Key.name : Key → List Char
  | .run w d use => w.word.toList ++ " to ".toList ++ quadChars d ++ ": ".toList ++ use.toList
  | .carried k o d =>
    "message ".toList ++ digits k ++ " of ".toList ++ quadChars o ++ " to ".toList ++ quadChars d ++
      ": carried".toList

theorem runName_key (w : Who) (d : Addr) (use : String) :
    (runName w.word d use).toList = (Key.run w (quadOf d) use).name := by
  simp only [runName, Key.name, String.toList_append, words_toList]

theorem carriedName_key (o : Addr) (k : Nat) (d : Addr) :
    (carriedName o k d).toList = (Key.carried k (quadOf o) (quadOf d)).name := by
  have h1 : (toString "message ").toList = "message ".toList := rfl
  have h2 : (toString " of ").toList = " of ".toList := rfl
  simp only [carriedName, Key.name, String.toList_append, words_toList, toString_digits, h1, h2]

/-- The first five characters of a key's name (`take_five`). -/
def Key.five : Key → List Char
  | .run .counts _ _ => ['t', 'h', 'e', ' ', 'm']
  | .run .index _ _ => ['t', 'h', 'e', ' ', 'i']
  | .run .fold _ _ => ['t', 'h', 'e', ' ', 'f']
  | .run .split _ _ => ['t', 'h', 'e', ' ', 's']
  | .carried _ _ _ => ['m', 'e', 's', 's', 'a']

theorem take_five (k : Key) : k.name.take 5 = k.five := by
  have ht : ∀ (a five rest : List Char), a = five ++ rest → five.length = 5 →
      ∀ X : List Char, (a ++ X).take 5 = five := by
    intro a five rest e hl X
    rw [e, List.append_assoc, List.take_left' hl]
  have c1 : countsMaskRun.toList = ['t', 'h', 'e', ' ', 'm'] ++ countsMaskRun.toList.drop 5 := by
    decide
  have c2 : indexMaskRun.toList = ['t', 'h', 'e', ' ', 'i'] ++ indexMaskRun.toList.drop 5 := by
    decide
  have c3 : foldMaskRun.toList = ['t', 'h', 'e', ' ', 'f'] ++ foldMaskRun.toList.drop 5 := by
    decide
  have c4 : splitMaskRun.toList = ['t', 'h', 'e', ' ', 's'] ++ splitMaskRun.toList.drop 5 := by
    decide
  have c5 : "message ".toList = ['m', 'e', 's', 's', 'a'] ++ "message ".toList.drop 5 := by decide
  cases k with
  | run w d use =>
    simp only [Key.name, List.append_assoc]
    cases w
    · exact ht _ _ _ c1 rfl _
    · exact ht _ _ _ c2 rfl _
    · exact ht _ _ _ c3 rfl _
    · exact ht _ _ _ c4 rfl _
  | carried k o d =>
    simp only [Key.name, List.append_assoc]
    exact ht _ _ _ c5 rfl _

/-- **Two keys with the same name are equal.** -/
theorem name_inj {k k' : Key} (h : k.name = k'.name) : k = k' := by
  have h5 : k.five = k'.five := by rw [← take_five, ← take_five, h]
  cases k with
  | run w d use =>
    cases k' with
    | run w' d' use' =>
      have hw : w = w' := by
        cases w <;> cases w' <;> first | rfl | simp [Key.five] at h5
      subst hw
      simp only [Key.name, List.append_assoc] at h
      have h := List.append_cancel_left (List.append_cancel_left h)
      have e : ": ".toList = ':' :: [' '] := rfl
      rw [e, List.cons_append, List.cons_append] at h
      obtain ⟨h1, -, h3⟩ := words_read rfl rfl h
      have hu : use = use' := String.ext (List.append_cancel_left (as := [' ']) h3)
      rw [h1, hu]
    | carried k o d' => cases w <;> simp [Key.five] at h5
  | carried k o d =>
    cases k' with
    | run w' d' use' => cases w' <;> simp [Key.five] at h5
    | carried k' o' d' =>
      simp only [Key.name, List.append_assoc] at h
      have h := List.append_cancel_left h
      have e1 : " of ".toList = ' ' :: ['o', 'f', ' '] := rfl
      have e2 : " to ".toList = ' ' :: ['t', 'o', ' '] := rfl
      have e3 : ": carried".toList = ':' :: " carried".toList := rfl
      rw [e1, e2, e3] at h
      simp only [List.cons_append, List.nil_append] at h
      obtain ⟨h1, -, h⟩ := read_off (digits_isDigit k) (digits_isDigit k') rfl rfl h
      have h := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2
      obtain ⟨h2, -, h⟩ := words_read rfl rfl h
      have h := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2
      obtain ⟨h3, -, -⟩ := words_read rfl rfl h
      rw [digits_inj k k' h1, h2, h3]

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.digits_inj
#print axioms AtPublicFiles.KeyBook.read_off
#print axioms AtPublicFiles.KeyBook.words_read
#print axioms AtPublicFiles.KeyBook.runName_key
#print axioms AtPublicFiles.KeyBook.carriedName_key
#print axioms AtPublicFiles.KeyBook.name_inj
#print axioms AtPublicFiles.KeyBook.digits
#print axioms AtPublicFiles.KeyBook.digitChar_toNat
#print axioms AtPublicFiles.KeyBook.digitChar_inj
#print axioms AtPublicFiles.KeyBook.digits_step
#print axioms AtPublicFiles.KeyBook.digits_ne_nil
#print axioms AtPublicFiles.KeyBook.digits_isDigit
#print axioms AtPublicFiles.KeyBook.toString_digits
#print axioms AtPublicFiles.KeyBook.Quad
#print axioms AtPublicFiles.KeyBook.quadOf
#print axioms AtPublicFiles.KeyBook.linkChars
#print axioms AtPublicFiles.KeyBook.quadChars
#print axioms AtPublicFiles.KeyBook.words_toList
#print axioms AtPublicFiles.KeyBook.link_read
#print axioms AtPublicFiles.KeyBook.Who
#print axioms AtPublicFiles.KeyBook.Who.word
#print axioms AtPublicFiles.KeyBook.Key
#print axioms AtPublicFiles.KeyBook.Key.name
#print axioms AtPublicFiles.KeyBook.Key.five
#print axioms AtPublicFiles.KeyBook.take_five
