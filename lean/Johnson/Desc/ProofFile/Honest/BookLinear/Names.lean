-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Names.lean: THE MAKERS OF THE NAMES OF THE BOOK's ENTRIES,
runName AND carriedName (Honest/ForKinds.lean), ARE ONE-TO-ONE, UP TO THE KIND OF A PLACE, WHERE A
USE HOLDS NO COLON; AND NO SPENT RUN's NAME IS A CARRIED RUN's, WHERE THE USE IS NOT "carried".
General laws on strings: no book, no description, no evaluation of a list. Statements with their
proofs; four definitions with code. Written by the authors of the honest side of the linear claim's
shared rounds (K14), in the frame's folder, not by the frame's authors; runName, carriedName,
Addr.words and Addr are theirs.

  words_inj       Addr.words a = Addr.words b → a.spot = b.spot
  runName_inj     **runName o d u = runName o' d' u' → o = o' ∧ d.spot = d'.spot ∧ u = u'**, where
                  neither use holds a colon. GENERAL IN THE OWNER's STRING: it may hold blanks,
                  colons, " to ", whole printed addresses
  carriedName_inj   **carriedName s m d = carriedName s' m' d' → s.spot = s'.spot ∧ m = m' ∧ d.spot
                  = d'.spot**
  runName_ne_carried   **runName o d u ≠ carriedName s m d'**, where u holds no colon and is not
                  "carried"
  Addr.spot       what Addr.words prints of an address: chain, link, piece and part. THE PLACE's
                  KIND IS NOT PRINTED: two addresses that differ in the kind alone have one spot,
                  and bear the same names (seen by unfolding; stated at one pair: kind_not_read)

What they are for. The eleventh test of ProverCoinCounts.clauses (Honest/Frame.lean) asks that no two entries
bear one name. With these laws "the names differ" follows from "what the names are made of differs":
two strings, two spots, a number. (NameKeys.lean of this folder spends them so, with the strings by
their places in two short tables.)

How it goes. All at lists of characters (String.toList_append; toString n = String.ofList
(Nat.toDigits 10 n)).
  firstSign       THE ONE LEMMA ON LISTS: xs ++ c :: r = ys ++ c' :: r', every member of xs and of
                  ys has p, c and c' have it not: then xs = ys, c = c', r = r'
  lastSign        the same from the right, by reversing
  decChars, decValue   a number's decimal print as characters; what characters spell
  decChars_digits, decChars_ne_nil, decChars_inj   the print holds digits alone (the core library's
                  Nat.isDigit_of_mem_toDigits), is not empty, and is one-to-one (decValue_chars: it
                  spells the number)
  words_chars, runName_chars, linkChars   what is printed, sign by sign
  words_cut       the words are read off the front of a list, where a sign that is no digit stands
                  behind them: firstSign four times; at the link, "-" against a print: the print
                  would be empty
  words_class     the words hold no blank and no colon
  carried_is_run  carriedName s m d = runName (s!"message {m} of " ++ s.words) d "carried"
runName_inj READS FROM THE RIGHT: behind the last colon stands a blank and the use (lastSign, at "is
no colon"); in front of it the words, behind the last blank (lastSign, at "is no blank"); what is
left, less " to", is the owner's string.

Kin. VerifierAndGoals.Lines.spelled (Johnson/Goal/Meaning/ScopeScan.lean): "A number's decimal spelling is
made of digits, is not empty, and spells the number", AT BYTES. It is not called: its file would
bring some hundreds of modules beneath this folder; decValue_chars is proved here anew, at
characters, in its manner. Lk6.AtPlan.decimal_char (OnBytes/Tie/Pv/KeyLookup/ScanText.lean): a
print's characters lie in 48..57. OnBytes.Shell.oneLine_nat (OnBytes/Shell/AtLine.lean): a print
holds no line feed. OnBytes.Model.ConfigReaders.append_cons_inj (OnBytes/Model/ConfigReaders.lean):
"If x is in neither a nor b, and a ++ x :: c is b ++ x :: d, then a is b": firstSign at one sign x,
at p := "is not x", its first clause alone. It is not called: here the two signs may differ, p is
"is a digit" at the calls in words_cut and carriedName_inj, and the rest behind the sign is wanted
too.

Eight closed facts on short literals (lit_dot to lit_carried: seven; carried_no_colon) are
evaluations in Lean's kernel (decide +kernel): the longest literal has nine signs.

Three closed facts show that runName_inj's premise, runName_ne_carried's second premise and the
limit are needed (evaluations in Lean's kernel too; runName_ne_carried's first premise, "no colon",
is taken because runName_inj is called: nothing shows that it is needed): colon_needed: WITH A COLON
IN A USE runName IS NOT ONE-TO-ONE (it states the equation; that the two owners' strings, addresses
and uses differ is seen by the eye) · carried_needed: at the use "carried" a spent run's name can be
a carried run's · kind_not_read: two addresses that differ in the kind alone bear one name.

Limits. That the makers of a book pass uses without a colon, and never "carried", is not shown here
(the five uses that a docstring of Honest/ForKinds.lean lists are such: by the eye). That two places
of a description differ in more than the kind is not shown here. Nothing on any book; nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **The first sign that has not p**: two lists that agree, each a stretch of members with p, then
a member without, then a rest: the three pieces agree. -/
theorem firstSign {α : Type} (p : α → Prop) : ∀ {xs ys : List α} {c c' : α} {r r' : List α},
    (∀ x ∈ xs, p x) → (∀ y ∈ ys, p y) → ¬ p c → ¬ p c' → xs ++ c :: r = ys ++ c' :: r' →
    xs = ys ∧ c = c' ∧ r = r'
  | [], [], _, _, _, _, _, _, _, _, h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact ⟨rfl, h1, h2⟩
  | [], y :: ys, c, _, _, _, _, hy, hc, _, h => by
    obtain ⟨h1, -⟩ := List.cons.inj h
    exact absurd (h1 ▸ hy y (List.mem_cons_self ..)) hc
  | x :: xs, [], _, c', _, _, hx, _, _, hc', h => by
    obtain ⟨h1, -⟩ := List.cons.inj h
    exact absurd (h1 ▸ hx x (List.mem_cons_self ..)) hc'
  | x :: xs, y :: ys, _, _, _, _, hx, hy, hc, hc', h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨e1, e2, e3⟩ := firstSign p (fun a ha => hx a (List.mem_cons_of_mem _ ha))
      (fun a ha => hy a (List.mem_cons_of_mem _ ha)) hc hc' h2
    exact ⟨by rw [h1, e1], e2, e3⟩

/-- A number's decimal print, as characters. -/
def decChars (n : Nat) : List Char := Nat.toDigits 10 n

/-- toString of a number, as characters. -/
theorem toString_chars (n : Nat) : (toString n).toList = decChars n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  rfl

/-- The print holds digits alone. -/
theorem decChars_digits (n : Nat) : ∀ c ∈ decChars n, c.isDigit = true := fun _ h =>
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- Below ten: one digit. -/
theorem decChars_small {n : Nat} (h : n < 10) : decChars n = [Nat.digitChar n] :=
  Nat.toDigits_of_lt_base h
/-- From ten on: the print of the tenth part, and the last digit. -/
theorem decChars_step {n : Nat} (h : 10 ≤ n) : decChars n = decChars (n / 10) ++ [Nat.digitChar (n %
  10)] :=
  Nat.toDigits_of_base_le (by decide) h

/-- The print is not empty. -/
theorem decChars_ne_nil (n : Nat) : decChars n ≠ [] := by
  by_cases h : n < 10
  · rw [decChars_small h]
    exact List.cons_ne_nil _ _
  · rw [decChars_step (Nat.le_of_not_lt h)]
    exact fun e => absurd (List.append_eq_nil_iff.1 e).2 (List.cons_ne_nil _ _)

/-- What characters spell, read as decimal digits. A sign that is no digit is not refused: it counts
as its number less 48, or as 0 below that: meant at prints alone. -/
def decValue (l : List Char) : Nat := l.foldl (fun v c => 10 * v + (c.toNat - 48)) 0

/-- A digit's character spells the digit. -/
theorem digit_value : ∀ d, d < 10 → (Nat.digitChar d).toNat - 48 = d := by decide

/-- **The print spells the number.** -/
theorem decValue_chars (n : Nat) : decValue (decChars n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decChars_small h]
      show 10 * 0 + ((Nat.digitChar n).toNat - 48) = n
      rw [digit_value n h]
      omega
    · have h10 : 10 ≤ n := Nat.le_of_not_lt h
      have c := ih (n / 10) (by omega)
      rw [decChars_step h10]
      unfold decValue at c ⊢
      rw [List.foldl_append, c]
      show 10 * (n / 10) + ((Nat.digitChar (n % 10)).toNat - 48) = n
      rw [digit_value _ (Nat.mod_lt _ (by decide))]
      omega

/-- **The print is one-to-one.** -/
theorem decChars_inj {n m : Nat} (h : decChars n = decChars m) : n = m := by
  rw [← decValue_chars n, ← decValue_chars m, h]


/-- **The last sign that has not p**: the same from the right. -/
theorem lastSign {α : Type} (p : α → Prop) {xs ys : List α} {c c' : α} {r r' : List α}
    (hx : ∀ x ∈ xs, p x) (hy : ∀ y ∈ ys, p y) (hc : ¬ p c) (hc' : ¬ p c')
    (h : r ++ c :: xs = r' ++ c' :: ys) : r = r' ∧ c = c' ∧ xs = ys := by
  have h' : xs.reverse ++ c :: r.reverse = ys.reverse ++ c' :: r'.reverse := by
    have := congrArg List.reverse h
    simpa only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
      using this
  obtain ⟨e1, e2, e3⟩ := firstSign p (fun x hx' => hx x (List.mem_reverse.1 hx'))
    (fun y hy' => hy y (List.mem_reverse.1 hy')) hc hc' h'
  exact ⟨List.reverse_inj.1 e3, e2, List.reverse_inj.1 e1⟩

/-- What `Addr.words` prints of an address: chain, link, piece, part. NOT THE KIND. -/
def Addr.spot (a : Addr) : Nat × Option Nat × Nat × Nat :=
  (a.place.chain, a.place.link, a.place.piece, a.part)

/-- What is printed for the link. -/
def linkChars : Option Nat → List Char
  | none => ['-']
  | some n => decChars n

/-- Seven short literals, as characters. -/
theorem lit_dot : (".").toList = ['.'] := by decide +kernel
/-- See lit_dot. -/
theorem lit_dash : ("-").toList = ['-'] := by decide +kernel
/-- See lit_dot. -/
theorem lit_to : (" to ").toList = [' ', 't', 'o', ' '] := by decide +kernel
/-- See lit_dot. -/
theorem lit_colon : (": ").toList = [':', ' '] := by decide +kernel
/-- See lit_dot. -/
theorem lit_message : ("message ").toList = ['m', 'e', 's', 's', 'a', 'g', 'e', ' '] := by
  decide +kernel
/-- See lit_dot. -/
theorem lit_of : (" of ").toList = [' ', 'o', 'f', ' '] := by decide +kernel
/-- See lit_dot. -/
theorem lit_carried : (": carried").toList = ':' :: ' ' :: ("carried").toList := by decide +kernel

/-- The link's print, as characters. -/
theorem link_chars (l : Option Nat) : ((l.map toString).getD "-").toList = linkChars l := by
  cases l with
  | none => exact lit_dash
  | some n => exact toString_chars n

/-- toString of a string is the string. -/
theorem toString_str (s : String) : toString s = s := rfl

/-- **What Addr.words prints.** -/
theorem words_chars (a : Addr) : a.words.toList =
    decChars a.place.chain ++ '.' :: (linkChars a.place.link ++ '.' :: (decChars a.place.piece ++
      '.' :: decChars a.part)) := by
  unfold Addr.words
  simp only [String.toList_append, toString_chars, toString_str, lit_dot, link_chars,
    List.append_assoc, List.cons_append, List.nil_append]

/-- "." is no digit. -/
theorem dot_no : ¬ ('.' : Char).isDigit = true := by decide
/-- "-" is no digit. -/
theorem dash_no : ¬ ('-' : Char).isDigit = true := by decide

/-- **The words are read off the front of a list**, where a sign that is no digit stands behind
them. -/
theorem words_cut {a b : Addr} {c c' : Char} {r r' : List Char} (hc : ¬ c.isDigit = true)
    (hc' : ¬ c'.isDigit = true) (h : a.words.toList ++ c :: r = b.words.toList ++ c' :: r') :
    a.spot = b.spot ∧ c = c' ∧ r = r' := by
  rw [words_chars, words_chars] at h
  simp only [List.append_assoc, List.cons_append] at h
  obtain ⟨e1, -, h⟩ := firstSign (fun x : Char => x.isDigit = true) (decChars_digits _)
    (decChars_digits _)
    dot_no dot_no h
  have e2 : a.place.link = b.place.link ∧
      decChars a.place.piece ++ '.' :: (decChars a.part ++ c :: r) =
        decChars b.place.piece ++ '.' :: (decChars b.part ++ c' :: r') := by
    cases ha : a.place.link with
    | none =>
      cases hb : b.place.link with
      | none =>
        rw [ha, hb] at h
        exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
      | some m =>
        rw [ha, hb] at h
        exact absurd (firstSign (fun x : Char => x.isDigit = true) (xs := []) (fun _ hx => nomatch
          hx)
          (decChars_digits m) dash_no dot_no h).1.symm (decChars_ne_nil m)
    | some n =>
      cases hb : b.place.link with
      | none =>
        rw [ha, hb] at h
        exact absurd (firstSign (fun x : Char => x.isDigit = true) (ys := []) (decChars_digits n)
          (fun _ hx => nomatch hx) dot_no dash_no h).1 (decChars_ne_nil n)
      | some m =>
        rw [ha, hb] at h
        obtain ⟨e, -, h'⟩ := firstSign (fun x : Char => x.isDigit = true) (decChars_digits n)
          (decChars_digits m)
          dot_no dot_no h
        exact ⟨by rw [decChars_inj e], h'⟩
  obtain ⟨e2, h⟩ := e2
  obtain ⟨e3, -, h⟩ := firstSign (fun x : Char => x.isDigit = true) (decChars_digits _)
    (decChars_digits _)
    dot_no dot_no h
  obtain ⟨e4, e5, e6⟩ := firstSign (fun x : Char => x.isDigit = true) (decChars_digits _)
    (decChars_digits _)
    hc hc' h
  refine ⟨?_, e5, e6⟩
  unfold Addr.spot
  rw [decChars_inj e1, e2, decChars_inj e3, decChars_inj e4]

/-- **The words are one-to-one on spots.** -/
theorem words_inj {a b : Addr} (h : a.words = b.words) : a.spot = b.spot :=
  (words_cut (c := ':') (c' := ':') (r := []) (r' := []) (by decide) (by decide) (by rw [h])).1

/-- The words hold no blank and no colon. (They hold digits, "." and "-" alone: not stated.) -/
theorem words_class (a : Addr) : ∀ x ∈ a.words.toList, x ≠ ' ' ∧ x ≠ ':' := by
  have hd : ∀ n, ∀ x ∈ decChars n, x ≠ ' ' ∧ x ≠ ':' := fun n x hx =>
    ⟨fun e => absurd (e ▸ decChars_digits n x hx) (by decide),
      fun e => absurd (e ▸ decChars_digits n x hx) (by decide)⟩
  have hl : ∀ l, ∀ x ∈ linkChars l, x ≠ ' ' ∧ x ≠ ':' := by
    intro l x hx
    cases l with
    | none =>
      obtain rfl : x = '-' := List.mem_singleton.1 hx
      exact ⟨by decide, by decide⟩
    | some n => exact hd n x hx
  intro x hx
  rw [words_chars] at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h | rfl | h | rfl | h
  · exact hd _ x h
  · exact ⟨by decide, by decide⟩
  · exact hl _ x h
  · exact ⟨by decide, by decide⟩
  · exact hd _ x h
  · exact ⟨by decide, by decide⟩
  · exact hd _ x h

/-- **What runName prints**, bracketed for the reading from the right. -/
theorem runName_chars (o : String) (d : Addr) (u : String) : (runName o d u).toList =
    (o.toList ++ [' ', 't', 'o']) ++ ' ' :: d.words.toList ++ ':' :: (' ' :: u.toList) := by
  unfold runName
  simp only [String.toList_append, lit_to, lit_colon, List.append_assoc, List.cons_append,
    List.nil_append]

/-- **runName IS ONE-TO-ONE, UP TO THE PLACE's KIND, AT EVERY OWNER's STRING**, where the uses hold
no colon. Read from the right. -/
theorem runName_inj {o o' u u' : String} {d d' : Addr} (hu : ':' ∉ u.toList) (hu' : ':' ∉ u'.toList)
    (h : runName o d u = runName o' d' u') : o = o' ∧ d.spot = d'.spot ∧ u = u' := by
  have h := congrArg String.toList h
  rw [runName_chars, runName_chars] at h
  have nc : ∀ {w : String}, ':' ∉ w.toList → ∀ x ∈ ' ' :: w.toList, x ≠ ':' := by
    intro w hw x hx e
    rcases List.mem_cons.1 hx with rfl | hx
    · exact absurd e (by decide)
    · exact hw (e ▸ hx)
  obtain ⟨h, -, e3⟩ := lastSign (fun x : Char => x ≠ ':') (nc hu) (nc hu') (fun q => q rfl)
    (fun q => q rfl) h
  obtain ⟨e1, -, e2⟩ := lastSign (fun x : Char => x ≠ ' ') (fun x hx => (words_class d x hx).1)
    (fun x hx => (words_class d' x hx).1) (fun q => q rfl) (fun q => q rfl) h
  exact ⟨String.toList_injective (List.append_cancel_right e1),
    words_inj (String.toList_injective e2), String.toList_injective (List.cons.inj e3).2⟩

/-- A carried run's name is a spent run's, at an owner's string of its own and the use "carried". -/
theorem carried_is_run (s : Addr) (m : Nat) (d : Addr) :
    carriedName s m d = runName (s!"message {m} of " ++ s.words) d "carried" := by
  apply String.toList_injective
  rw [runName_chars]
  unfold carriedName
  simp only [String.toList_append, lit_to, lit_carried, List.append_assoc, List.cons_append,
    List.nil_append]

/-- "carried" holds no colon. -/
theorem carried_no_colon : ':' ∉ ("carried").toList := by decide +kernel

/-- **carriedName IS ONE-TO-ONE, UP TO THE PLACES' KINDS.** -/
theorem carriedName_inj {s s' d d' : Addr} {m m' : Nat}
    (h : carriedName s m d = carriedName s' m' d') : s.spot = s'.spot ∧ m = m' ∧ d.spot = d'.spot :=
      by
  rw [carried_is_run, carried_is_run] at h
  obtain ⟨e1, e2, -⟩ := runName_inj carried_no_colon carried_no_colon h
  have e1 := congrArg String.toList e1
  simp only [String.toList_append, toString_chars, toString_str, lit_message, lit_of,
    List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq, true_and] at e1
  obtain ⟨a1, -, a2⟩ := firstSign (fun x : Char => x.isDigit = true) (decChars_digits m)
    (decChars_digits m')
    (by decide) (by decide) e1
  exact ⟨words_inj (String.toList_injective (List.cons.inj (List.cons.inj (List.cons.inj
    a2).2).2).2),
    decChars_inj a1, e2⟩

/-- **No spent run's name is a carried run's**, where the use holds no colon and is not "carried".
  -/
theorem runName_ne_carried {o u : String} {d s d' : Addr} {m : Nat} (hu : ':' ∉ u.toList)
    (hc : u ≠ "carried") : runName o d u ≠ carriedName s m d' := by
  intro h
  rw [carried_is_run] at h
  exact hc (runName_inj hu carried_no_colon h).2.2

/-- **The premise "no colon in a use" is needed**: two owners' strings, two addresses, two uses: one
  name. -/
theorem colon_needed : runName "a" ⟨⟨0, none, 0, .K1⟩, 0⟩ "b to 1.1.1.1: y" =
    runName "a to 0.-.0.0: b" ⟨⟨1, some 1, 1, .K1⟩, 1⟩ "y" := by decide +kernel

/-- **The premise "the use is not carried" is needed.** -/
theorem carried_needed : runName "message 1 of 0.-.0.0" ⟨⟨1, some 1, 1, .K1⟩, 1⟩ "carried" =
    carriedName ⟨⟨0, none, 0, .K1⟩, 0⟩ 1 ⟨⟨1, some 1, 1, .K1⟩, 1⟩ := by decide +kernel

/-- **The kind is not read**: the conclusions speak of spots, and cannot speak of addresses. -/
theorem kind_not_read : runName "a" ⟨⟨0, none, 0, .K1⟩, 0⟩ "y" = runName "a" ⟨⟨0, none, 0, .K2⟩, 0⟩
  "y" ∧
    (⟨⟨0, none, 0, .K1⟩, 0⟩ : Addr) ≠ ⟨⟨0, none, 0, .K2⟩, 0⟩ := by decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.firstSign
#print axioms ProofFile.Honest.toString_chars
#print axioms ProofFile.Honest.decChars_digits
#print axioms ProofFile.Honest.decChars_small
#print axioms ProofFile.Honest.decChars_step
#print axioms ProofFile.Honest.decChars_ne_nil
#print axioms ProofFile.Honest.digit_value
#print axioms ProofFile.Honest.decValue_chars
#print axioms ProofFile.Honest.decChars_inj
#print axioms ProofFile.Honest.lastSign
#print axioms ProofFile.Honest.lit_dot
#print axioms ProofFile.Honest.lit_dash
#print axioms ProofFile.Honest.lit_to
#print axioms ProofFile.Honest.lit_colon
#print axioms ProofFile.Honest.lit_message
#print axioms ProofFile.Honest.lit_of
#print axioms ProofFile.Honest.lit_carried
#print axioms ProofFile.Honest.link_chars
#print axioms ProofFile.Honest.toString_str
#print axioms ProofFile.Honest.words_chars
#print axioms ProofFile.Honest.dot_no
#print axioms ProofFile.Honest.dash_no
#print axioms ProofFile.Honest.words_cut
#print axioms ProofFile.Honest.words_inj
#print axioms ProofFile.Honest.words_class
#print axioms ProofFile.Honest.runName_chars
#print axioms ProofFile.Honest.runName_inj
#print axioms ProofFile.Honest.carried_is_run
#print axioms ProofFile.Honest.carried_no_colon
#print axioms ProofFile.Honest.carriedName_inj
#print axioms ProofFile.Honest.runName_ne_carried
#print axioms ProofFile.Honest.colon_needed
#print axioms ProofFile.Honest.carried_needed
#print axioms ProofFile.Honest.kind_not_read
