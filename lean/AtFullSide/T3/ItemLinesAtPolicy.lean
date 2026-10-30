-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/ItemLinesAtPolicy.lean: THE TWO READERS OF THE PARAMETER FILE AGREE AT EVERY PARAMETER
FILE OF THE GOALS' SCOPE. The item "request" is formed from the parameter file by one reader
(Proof.ParamLines, OnBytes/Proof/RequestItem.lean); the public part holds what the strict scan
(polScan, OnBytes/Model/Config.lean) reads of the same file. Johnson/AtFull/Item/PartsAtFull.lean
has the test numbersB on the two readers at the stored example's file, by an evaluation. Here it is
shown at VerifierAndGoals.policyFile v for all values v of the eight free numbers at which the scan returns.

How. The file's lines are the stored example's but for eleven free lines (read_policyFile). A line
is found by its first piece. So at a name that is none of the eleven, the item's reader finds what
it finds in the stored example's lines (named_fixed), and the scan's value is the stored example's
(value_fixed). At one of the eleven names the item's reader finds the one free line of that name
(named_free), whose numeral spells the number that was written (number32_spelled); the scan's value
is that number (value_free), and it is below 2^32 because the scan refuses a larger one (value_lt).

Main names.
  polStep_lt, fold_lt, value_lt   every value of a scan that returns is below 2^32
  lead_ne, number_spelled, number32_spelled   a number's decimal spelling is read back
  splitAt_none, split_fl          a free line, cut at its blank
  Lat, lines_Lat                  the lines at v, in eight blocks
  named_fixed, named_free         the lines of one name
  numbers_at_policy               MAIN: the test numbersB passes
  text_at_policy                  the text of the call lines is the stored example's

Limits. A public sentence on one file and two readers: no run, no coin, no hash. That the scan
returns is a premise. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Item.PartsAtFull
import Johnson.LPFPol.PublicInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Config
open OnBytes.Params (exc_bind exc_either)
open OnBytes.Model.ConfigReaders (refuseIf_ok bytesOf_inj digit_ne digit_toNat)
open VerifierAndGoals (FreeLines policyFile storedLines)
open VerifierAndGoals.Lines
open Johnson.AtFull.Item
open OnBytes.Road.K4.Trial.Values (PW scan_zFull)

/-! ## 1 Every value of a scan that returns is below 2^32 -/

/-- While a name is due, a step of the scan that passes adds one value below 2^32. -/
theorem polStep_lt {frame : Params.Lines} {prof : Nat} {names : Array String} {s s' : PolState}
    {line : List UInt8} {due : String} (hd : names[s.vals.size]? = some due)
    (h : polStep frame prof names s line = .ok s') :
    ∃ val, s'.vals = s.vals.push val ∧ val < 2 ^ 32 := by
  unfold polStep at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  dsimp only at h
  rw [hd] at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  cases x with
  | none => cases h
  | some y =>
    obtain ⟨name, val⟩ := y
    dsimp only at h
    obtain ⟨_, hlt, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, h⟩ := exc_either h
    cases h
    refine ⟨val, rfl, ?_⟩
    have := refuseIf_ok hlt
    exact Nat.lt_of_not_le (of_decide_eq_false this)

/-- The scan's steps keep all values below 2^32. -/
theorem fold_lt {frame : Params.Lines} {prof : Nat} {names : Array String} :
    ∀ {lines : List (List UInt8)} {s s' : PolState}, (∀ x ∈ s.vals.toList, x < 2 ^ 32) →
      lines.foldlM (polStep frame prof names) s = .ok s' → ∀ x ∈ s'.vals.toList, x < 2 ^ 32
  | [], s, s', hs, h => by
    cases h
    exact hs
  | line :: lines, s, s', hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := exc_bind h
    refine fold_lt ?_ h
    cases hd : names[s.vals.size]? with
    | none =>
      rw [polStep_after hd h1]
      exact hs
    | some due =>
      obtain ⟨val, e, hv⟩ := polStep_lt hd h1
      rw [e]
      intro x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hs x hx
      · exact hv

/-- A look-up in pairs whose numbers are below a bound. -/
theorem lookup_lt {B : Nat} (hB : 0 < B) (n : String) : ∀ l : List (String × Nat),
    (∀ p ∈ l, p.2 < B) → (l.lookup n).getD 0 < B
  | [], _ => hB
  | p :: l, h => by
    obtain ⟨a, b⟩ := p
    rw [List.lookup_cons]
    cases hn : n == a with
    | true => exact h (a, b) (List.mem_cons_self ..)
    | false => exact lookup_lt hB n l fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **Every value of a scan that returns is below 2^32.** -/
theorem value_lt {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) (n : String) :
    P.value n < 2 ^ 32 := by
  obtain ⟨frame, rest, prof, s, -, -, -, hs, -, hv, -⟩ := ConfigReaders.polScan_parts h
  have hl := fold_lt (s := {}) (by intro x hx; cases hx) hs
  unfold PolScan.value
  rw [hv]
  exact lookup_lt (by decide) n _ fun p hp => hl p.2 (List.of_mem_zip hp).2

/-! ## 2 A number's decimal spelling is read back -/

theorem digit_lead : ∀ d, d < 10 → 0 < d → (48 + d).toUInt8 ≠ 0x30 := by decide

/-- The spelling of a number that is not 0 does not begin with the digit 0. -/
theorem lead_ne (x : Nat) : 0 < x → (bytesOf (toString x)).head? ≠ some 0x30 := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    by_cases h : x < 10
    · rw [bytes_small h]
      intro e
      exact digit_lead x h hx (Option.some.inj e)
    · have h10 : 10 ≤ x := Nat.le_of_not_lt h
      have i := ih (x / 10) (by omega) (by omega)
      rw [bytes_step h10]
      cases hb : bytesOf (toString (x / 10)) with
      | nil => exact absurd hb (spelled (x / 10)).2.1
      | cons a t =>
        rw [hb] at i
        exact i

/-- **The frame's reader of numerals reads a number's spelling back**, up to fifteen digits. -/
theorem number_spelled {x : Nat} (hl : (bytesOf (toString x)).length ≤ 15) :
    Params.number (bytesOf (toString x)) = some x := by
  obtain ⟨a, b, c⟩ := spelled x
  have h1 : (bytesOf (toString x)).isEmpty = false := by
    cases hb : bytesOf (toString x) with
    | nil => exact absurd hb b
    | cons _ _ => rfl
  have h2 : decide (15 < (bytesOf (toString x)).length) = false :=
    decide_eq_false (Nat.not_lt.2 hl)
  have h3 : ((bytesOf (toString x)).head? == some 0x30 &&
      decide (1 < (bytesOf (toString x)).length)) = false := by
    by_cases h : x < 10
    · rw [bytes_small h]
      exact Bool.and_false _
    · rw [beq_false_of_ne (lead_ne x (by omega))]
      rfl
  have h4 : ((bytesOf (toString x)).any fun c => decide (c < 0x30) || decide (0x39 < c)) =
      false := by
    rw [List.any_eq_false]
    intro c hc
    obtain ⟨l1, l2⟩ := digit_toNat (List.all_eq_true.1 a c hc)
    have k1 : ¬ c < 0x30 := by
      rw [UInt8.lt_iff_toNat_lt]
      have : (0x30 : UInt8).toNat = 48 := rfl
      omega
    have k2 : ¬ 0x39 < c := by
      rw [UInt8.lt_iff_toNat_lt]
      have : (0x39 : UInt8).toNat = 57 := rfl
      omega
    simp [k1, k2]
  unfold Params.number
  rw [h1, h2, h3, h4]
  exact congrArg some c

/-- The item's reader of numerals reads a number below 2^32 back. -/
theorem number32_spelled {x : Nat} (hl : (bytesOf (toString x)).length ≤ 15) (hx : x < 2 ^ 32) :
    number32 (bytesOf (toString x)) = some x := by
  unfold number32
  rw [number_spelled hl]
  show (if decide (x < 2 ^ 32) = true then some x else none) = some x
  rw [if_pos (decide_eq_true hx)]

/-! ## 3 A free line, cut at its blank -/

/-- A list without the byte c is one piece. -/
theorem splitAt_none (c : UInt8) : ∀ l : List UInt8, (∀ x ∈ l, x ≠ c) → splitAt c l = [l]
  | [], _ => rfl
  | x :: l, h => by
    have hx : (x == c) = false := by simpa using h x (List.mem_cons_self ..)
    have ih := splitAt_none c l fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [splitAt_foldr, List.foldr_cons, ← splitAt_foldr, ih, hx]
    rfl

/-- **A free line has two pieces: its name and its numeral.** -/
theorem split_fl {n q : String} (hq : bytesOf q = bytesOf n ++ [0x20])
    (hn : (bytesOf n).all (fun c => c != 0x20) = true) (x : Nat) :
    splitAt 0x20 (fl q x) = [bytesOf n, bytesOf (toString x)] := by
  unfold fl
  rw [hq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [splitAt_piece 0x20 _ (fun y hy => by simpa using List.all_eq_true.1 hn y hy),
    splitAt_none 0x20 _ fun y hy =>
      digit_ne (List.all_eq_true.1 (spelled x).1 y hy) (by decide)]

/-! ## 4 The lines at v, in eight blocks -/

/-- The names of the eleven free lines. -/
def freeNames : List String :=
  ["eps1_lo", "eps1_hi", "eps2_lo", "eps2_hi", "MF", "KF", "epsF_lo", "epsF_hi", "C", "theta",
   "cap"]

theorem freeValues_names (v : FreeLines) : (freeValues v).map Prod.fst = freeNames := rfl

/-- Written lines, each cut at its blanks. -/
def cut (ls : List (List UInt8)) : List (List (List UInt8)) := ls.map (splitAt 0x20)

/-- Free lines, each cut at its blank: the name, the numeral. -/
def fb (ps : List (String × Nat)) : List (List (List UInt8)) :=
  ps.map fun p => [bytesOf p.1, bytesOf (toString p.2)]

/-- The lines of the parameter file at v, as the item's reader cuts them. -/
def Lat (v : FreeLines) : ParamLines := ⟨(rawAt v).map (splitAt 0x20)⟩

theorem Lat_stored : Lat storedLines = linesW := rfl

theorem read_Lat (v : FreeLines) : ParamLines.read (policyFile v) = Lat v := read_policyFile v

theorem cut_free1 (v : FreeLines) :
    (fl0 (free1 v)).map (splitAt 0x20) = fb ((freeValues v).take 4) := by
  show [splitAt 0x20 (fl "eps1_lo " _), splitAt 0x20 (fl "eps1_hi " _),
    splitAt 0x20 (fl "eps2_lo " _), splitAt 0x20 (fl "eps2_hi " _)] = _
  rw [split_fl (n := "eps1_lo") (by decide +kernel) (by decide +kernel),
    split_fl (n := "eps1_hi") (by decide +kernel) (by decide +kernel),
    split_fl (n := "eps2_lo") (by decide +kernel) (by decide +kernel),
    split_fl (n := "eps2_hi") (by decide +kernel) (by decide +kernel)]
  rfl

theorem cut_free2 (v : FreeLines) :
    (fl0 (free2 v)).map (splitAt 0x20) = fb (((freeValues v).drop 4).take 4) := by
  show [splitAt 0x20 (fl "MF " _), splitAt 0x20 (fl "KF " _),
    splitAt 0x20 (fl "epsF_lo " _), splitAt 0x20 (fl "epsF_hi " _)] = _
  rw [split_fl (n := "MF") (by decide +kernel) (by decide +kernel),
    split_fl (n := "KF") (by decide +kernel) (by decide +kernel),
    split_fl (n := "epsF_lo") (by decide +kernel) (by decide +kernel),
    split_fl (n := "epsF_hi") (by decide +kernel) (by decide +kernel)]
  rfl

theorem cut_free3 (v : FreeLines) :
    (fl0 (free3 v)).map (splitAt 0x20) = fb ((freeValues v).drop 8) := by
  show [splitAt 0x20 (fl "C " _), splitAt 0x20 (fl "theta " _),
    splitAt 0x20 (fl "cap " _)] = _
  rw [split_fl (n := "C") (by decide +kernel) (by decide +kernel),
    split_fl (n := "theta") (by decide +kernel) (by decide +kernel),
    split_fl (n := "cap") (by decide +kernel) (by decide +kernel)]
  rfl

/-- **The lines at v**: five written blocks, and between them the three blocks of free lines. -/
theorem lines_Lat (v : FreeLines) : (Lat v).lines =
    cut frameLines ++ (cut linesA1 ++ (fb ((freeValues v).take 4) ++ (cut linesA2 ++
      (fb (((freeValues v).drop 4).take 4) ++ (cut linesA3 ++
        (fb ((freeValues v).drop 8) ++ cut linesB)))))) := by
  show (rawAt v).map (splitAt 0x20) = _
  unfold rawAt
  simp only [List.map_append]
  rw [cut_free1, cut_free2, cut_free3]
  rfl

/-! ## 5 The lines of one name -/

/-- The test by which a line is found: its first piece is w. -/
def isNamed (w : List UInt8) (l : List (List UInt8)) : Bool := l.head? == some w

theorem named_eq (L : ParamLines) (name : String) :
    L.named name = L.lines.filter (isNamed (bytesOf name)) := rfl

/-- Among free lines, those of one name. -/
theorem filter_fb (n : String) : ∀ ps : List (String × Nat),
    (fb ps).filter (isNamed (bytesOf n)) = fb (ps.filter fun p => p.1 == n)
  | [] => rfl
  | p :: ps => by
    have ih := filter_fb n ps
    show List.filter _ ([bytesOf p.1, bytesOf (toString p.2)] :: fb ps) = _
    by_cases e : p.1 = n
    · have t : isNamed (bytesOf n) [bytesOf p.1, bytesOf (toString p.2)] = true := by
        rw [e]
        show (some (bytesOf n) == some (bytesOf n)) = true
        exact beq_self_eq_true _
      rw [List.filter_cons_of_pos t, List.filter_cons_of_pos (by simpa using e), ih]
      rfl
    · have t : ¬ isNamed (bytesOf n) [bytesOf p.1, bytesOf (toString p.2)] = true := by
        intro k
        have k' : some (bytesOf p.1) = some (bytesOf n) := eq_of_beq k
        exact e (bytesOf_inj (Option.some.inj k'))
      rw [List.filter_cons_of_neg t, List.filter_cons_of_neg (by simpa using e), ih]

/-- Pairs with distinct names: those of one name that is there are one pair. -/
theorem filter_unique : ∀ {l : List (String × Nat)} {n : String} {x : Nat},
    (l.map Prod.fst).Nodup → (n, x) ∈ l → l.filter (fun p => p.1 == n) = [(n, x)]
  | [], _, _, _, hm => by cases hm
  | p :: l, n, x, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hm with e | hm'
    · subst e
      have z : l.filter (fun p => p.1 == n) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq hqn
        apply hnd.1
        show n ∈ l.map Prod.fst
        rw [← (eq_of_beq hqn : q.1 = n)]
        exact List.mem_map_of_mem (f := Prod.fst) hq
      have k : List.filter (fun p => p.1 == n) ((n, x) :: l) =
          (n, x) :: List.filter (fun p => p.1 == n) l :=
        List.filter_cons_of_pos (beq_self_eq_true n)
      rw [k, z]
    · have hne : ¬ (p.1 == n) = true := by
        intro k
        apply hnd.1
        rw [eq_of_beq k]
        exact List.mem_map_of_mem (f := Prod.fst) hm'
      have k : List.filter (fun p => p.1 == n) (p :: l) = List.filter (fun p => p.1 == n) l :=
        List.filter_cons_of_neg hne
      rw [k, filter_unique hnd.2 hm']

/-- Pairs none of which has the name. -/
theorem filter_absent {l : List (String × Nat)} {n : String} (h : n ∉ l.map Prod.fst) :
    l.filter (fun p => p.1 == n) = [] := by
  rw [List.filter_eq_nil_iff]
  intro q hq hqn
  apply h
  rw [← (eq_of_beq hqn : q.1 = n)]
  exact List.mem_map_of_mem hq

/-- The lines of one name at v: what the five written blocks hold, and the free lines of that name.
-/
theorem named_Lat (v : FreeLines) (n : String) : (Lat v).named n =
    (cut frameLines).filter (isNamed (bytesOf n)) ++ ((cut linesA1).filter (isNamed (bytesOf n)) ++
      (fb (((freeValues v).take 4).filter fun p => p.1 == n) ++
        ((cut linesA2).filter (isNamed (bytesOf n)) ++
          (fb ((((freeValues v).drop 4).take 4).filter fun p => p.1 == n) ++
            ((cut linesA3).filter (isNamed (bytesOf n)) ++
              (fb (((freeValues v).drop 8).filter fun p => p.1 == n) ++
                (cut linesB).filter (isNamed (bytesOf n)))))))) := by
  rw [named_eq, lines_Lat]
  simp only [List.filter_append, filter_fb]

/-- **At a name that is none of the eleven, the lines are the stored example's.** -/
theorem named_fixed (v : FreeLines) {n : String} (hn : n ∉ freeNames) :
    (Lat v).named n = linesW.named n := by
  have z : ∀ (u : FreeLines) (l : List (String × Nat)), l.Sublist (freeValues u) →
      l.filter (fun p => p.1 == n) = [] := by
    intro u l hl
    refine filter_absent fun hm => hn ?_
    rw [← freeValues_names u]
    exact (hl.map Prod.fst).subset hm
  rw [← Lat_stored, named_Lat, named_Lat,
    z v _ (List.take_sublist _ _), z v _ ((List.take_sublist _ _).trans (List.drop_sublist _ _)),
    z v _ (List.drop_sublist _ _), z storedLines _ (List.take_sublist _ _),
    z storedLines _ ((List.take_sublist _ _).trans (List.drop_sublist _ _)),
    z storedLines _ (List.drop_sublist _ _)]

/-- No written line has the name of a free line. -/
def writtenClear : Bool :=
  (cut frameLines ++ cut linesA1 ++ cut linesA2 ++ cut linesA3 ++ cut linesB).all fun l =>
    freeNames.all fun n => !isNamed (bytesOf n) l

theorem writtenClear_holds : writtenClear = true := by decide +kernel

/-- **At the name of a free line there is one line: that name and the numeral of its number.** -/
theorem named_free (v : FreeLines) {p : String × Nat} (hp : p ∈ freeValues v) :
    (Lat v).named p.1 = [[bytesOf p.1, bytesOf (toString p.2)]] := by
  have hn : p.1 ∈ freeNames := by
    rw [← freeValues_names v]
    exact List.mem_map_of_mem hp
  have c : ∀ ls, (∀ l ∈ cut ls, l ∈ cut frameLines ++ cut linesA1 ++ cut linesA2 ++ cut linesA3 ++
      cut linesB) → (cut ls).filter (isNamed (bytesOf p.1)) = [] := by
    intro ls hls
    rw [List.filter_eq_nil_iff]
    intro l hl k
    have t := List.all_eq_true.1 (List.all_eq_true.1 writtenClear_holds l (hls l hl)) p.1 hn
    rw [k] at t
    cases t
  have e : fb (((freeValues v).take 4).filter fun q => q.1 == p.1) ++
      (fb ((((freeValues v).drop 4).take 4).filter fun q => q.1 == p.1) ++
        fb (((freeValues v).drop 8).filter fun q => q.1 == p.1)) =
      fb ((freeValues v).filter fun q => q.1 == p.1) := by
    unfold fb
    rw [← List.map_append, ← List.map_append, ← List.filter_append, ← List.filter_append]
    rfl
  rw [named_Lat, c frameLines (by intro l hl; simp [hl]), c linesA1 (by intro l hl; simp [hl]),
    c linesA2 (by intro l hl; simp [hl]), c linesA3 (by intro l hl; simp [hl]),
    c linesB (by intro l hl; simp [hl])]
  simp only [List.nil_append, List.append_nil]
  rw [e, filter_unique (x := p.2) (by rw [freeValues_names]; decide) hp]
  rfl

/-! ## 6 What is read by name -/

theorem values_fixed (v : FreeLines) {n : String} (hn : n ∉ freeNames) :
    (Lat v).values n = linesW.values n := by
  unfold ParamLines.values
  rw [named_fixed v hn]

theorem lvalue_fixed (v : FreeLines) {n : String} (hn : n ∉ freeNames) :
    (Lat v).value n = linesW.value n := by
  unfold ParamLines.value
  rw [values_fixed v hn]

theorem text_fixed (v : FreeLines) {n : String} (hn : n ∉ freeNames) :
    (Lat v).text n = linesW.text n := by
  unfold ParamLines.text
  rw [named_fixed v hn]

/-- The eight lines of a table's digest. -/
theorem eight_fixed (v : FreeLines) {name : String}
    (hn : ((List.range 8).all fun i => !freeNames.contains (name ++ toString i)) = true) :
    (Lat v).eight name = linesW.eight name := by
  unfold ParamLines.eight
  have e : ((List.range 8).map fun i => (Lat v).value (name ++ toString i)) =
      (List.range 8).map fun i => linesW.value (name ++ toString i) := by
    refine List.map_congr_left fun i hi => lvalue_fixed v ?_
    have t := List.all_eq_true.1 hn i hi
    intro hm
    rw [List.contains_iff_mem.2 hm] at t
    cases t
  rw [e]

theorem last_fixed (v : FreeLines) : (Lat v).lastWords = linesW.lastWords := by
  unfold ParamLines.lastWords
  rw [lvalue_fixed v (n := "sec") (by decide), values_fixed v (n := "table") (by decide)]

/-- **At the name of a free line the item's reader gives the number that was written**, where the
scan returns. -/
theorem lvalue_free {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {p : String × Nat} (hp : p ∈ freeValues v) : (Lat v).value p.1 = some (P.value p.1) := by
  have hx : p.2 < 2 ^ 32 := by
    rw [← value_free h hp]
    exact value_lt h p.1
  unfold ParamLines.value ParamLines.values
  rw [named_free v hp, value_free h hp]
  show number32 (bytesOf (toString p.2)) = some p.2
  exact number32_spelled (Nat.le_trans (LPFPol.digits_free h hp) (by decide)) hx

/-! ## 7 The test on the numbers -/

/-- Each of the 97 names is a free line's or a fixed value line's. -/
def namesSorted : Bool :=
  (names2L ++ names37L ++ names103L ++ names130L).all fun n =>
    freeNames.contains n || (!freeNames.contains n && (fixedValues.map Prod.fst).contains n)

theorem namesSorted_holds : namesSorted = true := by decide +kernel

/-- The two readers agree at every name of a list of such names. -/
theorem agree_at_policy {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {l : List String} (hl : ∀ n ∈ l, n ∈ names2L ++ names37L ++ names103L ++ names130L)
    (hW : agreeB PW linesW l = true) : agreeB P (Lat v) l = true := by
  have hPW : polScan (policyFile storedLines) = .ok PW := by
    rw [← VerifierAndGoals.pol_zFull]
    exact scan_zFull
  unfold agreeB at hW ⊢
  rw [List.all_eq_true] at hW ⊢
  intro n hn
  have t := List.all_eq_true.1 namesSorted_holds n (hl n hn)
  rw [Bool.or_eq_true] at t
  rcases t with t | t
  · have hm : n ∈ (freeValues v).map Prod.fst := by
      rw [freeValues_names]
      exact List.contains_iff_mem.1 t
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    rw [lvalue_free h hp]
    exact beq_self_eq_true _
  · rw [Bool.and_eq_true] at t
    have hf : n ∉ freeNames := by
      intro hm
      rw [List.contains_iff_mem.2 hm] at t
      cases t.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.contains_iff_mem.1 t.2)
    rw [lvalue_fixed v hf, value_fixed h hp, ← value_fixed hPW hp]
    exact hW p.1 hn

/-- **MAIN. Where the strict scan returns at the parameter file with the free numbers v, the test on
the two readers passes.** -/
theorem numbers_at_policy {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    numbersB P (ParamLines.read (policyFile v)) = true := by
  have hPW : polScan (policyFile storedLines) = .ok PW := by
    rw [← VerifierAndGoals.pol_zFull]
    exact scan_zFull
  have eF : P.frame = PW.frame := (frame_eq h).trans (frame_eq hPW).symm
  have eT : ∀ t, P.tableExpected t = PW.tableExpected t := by
    intro t
    unfold PolScan.tableExpected
    rw [(scan_rest h).2.2.2.2.2.2.2.2.2.2.2, (scan_rest hPW).2.2.2.2.2.2.2.2.2.2.2]
  have hW := numbers_W
  rw [read_Lat]
  unfold numbersB at hW ⊢
  simp only [Bool.and_eq_true] at hW ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, a2⟩, a37⟩, a103⟩, a130⟩, t1⟩, t2⟩, t3⟩, t4⟩, hl⟩ := hW
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [values_fixed v (n := "version") (by decide)]
    exact h1
  · rw [lvalue_fixed v (n := "prof") (by decide)]
    exact h2
  · rw [lvalue_fixed v (n := "NE") (by decide)]
    exact h3
  · rw [lvalue_fixed v (n := "lt") (by decide)]
    exact h4
  · exact agree_at_policy h (by intro n hn; simp [hn]) a2
  · exact agree_at_policy h (by intro n hn; simp [hn]) a37
  · exact agree_at_policy h (by intro n hn; simp [hn]) a103
  · exact agree_at_policy h (by intro n hn; simp [hn]) a130
  · unfold eightB at t1 ⊢
    rw [eight_fixed v (by decide +kernel), eT]
    exact t1
  · unfold eightB at t2 ⊢
    rw [eight_fixed v (by decide +kernel), eT]
    exact t2
  · unfold eightB at t3 ⊢
    rw [eight_fixed v (by decide +kernel), eT]
    exact t3
  · unfold eightB at t4 ⊢
    rw [eight_fixed v (by decide +kernel), eT]
    exact t4
  · rw [last_fixed v]
    unfold PolScan.hb PolScan.lkW at hl ⊢
    rw [eF]
    exact hl

/-- **The text of the call lines is the stored example's**, at all v. -/
theorem text_at_policy (v : FreeLines) : ∀ name ∈ ["call", "callA", "callH"],
    (ParamLines.read (policyFile v)).text name = linesW.text name := by
  intro name hn
  rw [read_Lat]
  refine text_fixed v ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;> decide

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.value_lt
#print axioms AtPublicFiles.Start.number32_spelled
#print axioms AtPublicFiles.Start.split_fl
#print axioms AtPublicFiles.Start.lines_Lat
#print axioms AtPublicFiles.Start.named_fixed
#print axioms AtPublicFiles.Start.writtenClear_holds
#print axioms AtPublicFiles.Start.named_free
#print axioms AtPublicFiles.Start.lvalue_free
#print axioms AtPublicFiles.Start.namesSorted_holds
#print axioms AtPublicFiles.Start.numbers_at_policy
#print axioms AtPublicFiles.Start.text_at_policy
