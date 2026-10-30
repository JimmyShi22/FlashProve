-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedAsked.lean: at which strings the seeds of a stored table's record are asked for;
an algorithm that asks there; and that a log which holds the oracle's own answers at these strings
shows the seed. No probability.

`seedAt` (OnBytes/Slice/RecordRead.lean) reads a key's seed off a log by running the text of the
program's `recordSeeds` at a hash that reads the log. Here that text is followed through its one
loop: where a hash in the monad `Option` and a plain hash agree at every call that the text makes,
the two runs agree.

Main definitions.
 `Answers g σ`, `Asked σ s`   every entry of the log holds g's own answer; the log has an entry at
                        the byte string s.
 `seedFirst`, `seedRest`, `seedCalls`   THE STRINGS, WRITTEN OUT: one call number 160 under the
                        label 2^32 on the table's name; then `seedCalls` calls number 162, two
                        strings a call, with the first call's answer as the start.
 `askAll`, `askSeed lg s name`   asks the first string, then the strings made with its answer.
Main theorems.
 `askLog_of_asked`, `HM_of_asked`   in a log of g's own answers the hash that reads the log gives
                        what the hash over g's function gives, at a call that was asked and whose
                        number is not 169.
 `fetchFrom_some`, `queryW_some`   the format's loop over a round's calls, and one step of a chain,
                        at two hashes that agree where they are called.
 `recordSeedsW_of_asked`   so the program's text at the hash that reads the log gives what it gives
                        at the hash over g's function.
 `recordSeedsW_HO`, `seedAt_of_asked`   there it gives seeds (the round is written with work 0, and
                        the first value has 32 bytes); so the log shows the seed.
 `askSeed_noCoin`, `askSeed_bound`, `askSeed_asked`   no coin; 2 * `seedCalls` + 1 questions; its
                        log has an entry at each of the strings.

What is not claimed. Nothing on how the seeds are distributed. That any committer asks. WHICH seed a
log of g's own answers shows is not said here: OnBytes/Slice/SeedWhich.lean. `askLog` takes the
FIRST entry at a string; in a log of g's own answers all entries at one string agree. Nothing on any
hash function.

-/
import OnBytes.Slice.RecordRead
import OnBytes.Slice.Guard

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory Cb Cb.Ood
open OnBytes.Tie (IdKey firstId)

/-! ## A log that holds the oracle's own answers -/

/-- Every entry of the log holds g's own answer. -/
def Answers (g : Fam (rom 256)) (σ : Trace (rom 256)) : Prop := ∀ e ∈ σ, e.2.2 = g e.1 e.2.1

/-- The log has an entry at the byte string s. -/
def Asked (σ : Trace (rom 256)) (s : ByteArray) : Prop :=
  ∃ e ∈ σ, (e.2.1 : List Bool) = bytesToBits s

/-- In such a log, at a string that was asked and is no call with the number 169, `askLog` finds
the oracle's answer. -/
theorem askLog_of_asked (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ)
    (s : ByteArray) (h9 : (Fmt.wordAt s 65).toNat % 65536 ≠ 169) (hm : Asked σ s) :
    askLog σ s = some (oB (g ()) s) := by
  unfold askLog
  rw [if_neg h9]
  obtain ⟨e, he, hq⟩ := hm
  cases hf : σ.find? (fun e => decide ((e.2.1 : List Bool) = bytesToBits s)) with
  | none =>
    have h0 := List.find?_eq_none.1 hf e he
    exact absurd hq (by simpa using h0)
  | some e' =>
    have h1 : (e'.2.1 : List Bool) = bytesToBits s := by simpa using List.find?_some hf
    have h2 := hσ e' (List.mem_of_find?_eq_some hf)
    show some (digToBytes (e'.2.2 : Dig 256)) = some (digToBytes (g () (bytesToBits s)))
    rw [h2, ← h1]
    rfl

/-- So the hash that reads the log gives what the hash over g's function gives. -/
theorem HM_of_asked (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (n t i : ℕ)
    (st b : ByteArray) (hn : n % 65536 ≠ 169) (h0 : Asked σ (Fmt.oStr 0 n t i st b))
    (h1 : n = 162 → Asked σ (Fmt.oStr 1 n t i st b)) :
    Fmt.HM (m := Option) (askLog σ) n t i st b = some (Fmt.HO (oB (g ())) n t i st b) := by
  have a0 := askLog_of_asked g σ hσ _ (by rw [Tie.oStr_number]; exact hn) h0
  unfold Fmt.HM Fmt.HO
  by_cases h : n = 162
  · have a1 := askLog_of_asked g σ hσ _ (by rw [Tie.oStr_number]; exact hn) (h1 h)
    rw [if_pos h, if_pos h]
    show (askLog σ _).bind (fun a => (askLog σ _).bind fun c => some (a ++ c)) = _
    rw [a0, a1]
    rfl
  · rw [if_neg h, if_neg h]
    exact a0

/-! ## The program's text at two hashes that agree where it asks -/

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Option ByteArray)
  (H' : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (lab : ℕ) (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind) (w nonce : ℕ)

/-- The loop that fetches a round's blocks. -/
theorem fetchFrom_some : ∀ (n j : ℕ) (acc : Array ByteArray),
    (∀ j', j ≤ j' → j' < j + n → Fmt.callW h lab rho i msg kind w nonce j' =
      some (Fmt.callW (m := Id) H' lab rho i msg kind w nonce j')) →
    Fmt.fetchFrom h lab rho i msg kind w nonce n j acc =
      some (Fmt.fetchFrom (m := Id) H' lab rho i msg kind w nonce n j acc)
  | 0, _, _, _ => rfl
  | n + 1, j, acc, hc => by
    unfold Fmt.fetchFrom
    rw [hc j le_rfl (by omega)]
    exact fetchFrom_some n (j + 1) _ fun j' a b => hc j' (by omega) (by omega)

/-- One step of a chain. -/
theorem queryW_some (c : Fmt.Chain) (K : ℕ)
    (hc : ∀ j', j' < (Fmt.firstBlock w + K + 1) / 2 →
      Fmt.callW h c.label c.rho (c.round + 1) msg kind w nonce j' =
        some (Fmt.callW (m := Id) H' c.label c.rho (c.round + 1) msg kind w nonce j')) :
    Fmt.Chain.queryW h c msg kind w nonce K =
      some (Fmt.Chain.queryW (m := Id) H' c msg kind w nonce K) := by
  unfold Fmt.Chain.queryW
  by_cases ha : Fmt.askOK c.label c.rho (c.round + 1) msg kind w nonce = true
  · rw [if_pos ha, if_pos ha]
    unfold Fmt.fetchW
    rw [fetchFrom_some h H' c.label c.rho (c.round + 1) msg kind w nonce _ 0 #[]
      fun j' _ b => hc j' (by omega)]
    rfl
  · rw [if_neg ha, if_neg ha]
    rfl

end

/-! ## The strings at which the seeds are asked for -/

/-- The number of calls with the number 162 in the seeds' round: each gives two blocks. -/
def seedCalls (lg s : ℕ) : ℕ := (Fmt.firstBlock 0 + Fmt.blocksFor (s * (lg * 18 + 36)) + 1) / 2

/-- The string of the first value of the seeds' chain: a function of the table's name. -/
def seedFirst (name : ByteArray) : ByteArray :=
  Fmt.oStr 0 160 0 Fmt.recordLabel Fmt.zero32
    (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none)

/-- The strings of the seeds' round, two a call: functions of the first value ρ0. -/
def seedRest (ρ0 : ByteArray) (lg s : ℕ) : List ByteArray :=
  (List.range (seedCalls lg s)).flatMap fun j =>
    [Fmt.oStr 0 162 Fmt.recordLabel 1 ρ0 (ByteArray.empty ++ Fmt.tail .seeds 0 0 j),
      Fmt.oStr 1 162 Fmt.recordLabel 1 ρ0 (ByteArray.empty ++ Fmt.tail .seeds 0 0 j)]

/-- **In a log that holds g's own answers at these strings, the program's text at the hash that
reads the log gives what it gives at the hash over g's function.** -/
theorem recordSeedsW_of_asked (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ)
    (name : ByteArray) (lg s : ℕ) (h0 : Asked σ (seedFirst name))
    (h1 : ∀ x ∈ seedRest (oB (g ()) (seedFirst name)) lg s, Asked σ x) :
    recordSeedsW (m := Option) (Fmt.HM (askLog σ)) .two name lg s =
      some (recordSeedsW (m := Id) (Fmt.HO (oB (g ()))) .two name lg s) := by
  have e0 : Fmt.recordFirstW (m := Option) (Fmt.HM (askLog σ)) name =
      some (oB (g ()) (seedFirst name)) :=
    HM_of_asked g σ hσ 160 0 Fmt.recordLabel Fmt.zero32 _ (by decide) h0 (fun h => by cases h)
  have e1 := queryW_some (Fmt.HM (askLog σ)) (Fmt.HO (oB (g ()))) ByteArray.empty .seeds 0 0
    ⟨Fmt.recordLabel, oB (g ()) (seedFirst name), 0⟩ (Fmt.blocksFor (s * (lg * 18 + 36)))
    fun j' hj => HM_of_asked g σ hσ 162 Fmt.recordLabel 1 _ _ (by decide)
      (h1 _ (List.mem_flatMap.2 ⟨j', List.mem_range.2 hj, List.mem_cons_self⟩))
      (fun _ => h1 _ (List.mem_flatMap.2 ⟨j', List.mem_range.2 hj,
        List.mem_cons_of_mem _ List.mem_cons_self⟩))
  show (Fmt.recordFirstW (m := Option) (Fmt.HM (askLog σ)) name).bind (fun ρ0 =>
    (Fmt.Chain.queryW (Fmt.HM (askLog σ)) ⟨Fmt.recordLabel, ρ0, 0⟩ ByteArray.empty .seeds 0 0
      (Fmt.blocksFor (s * (lg * 18 + 36)))).bind fun r => some _) = _
  rw [e0, Option.bind_some, e1]
  rfl

/-- At the hash over a function with answers of 32 bytes the program's text gives seeds: the one
round has no work, and what the format asks of a query's data holds. -/
theorem recordSeedsW_HO (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (name : ByteArray)
    (lg s : ℕ) : ∃ l, recordSeedsW (m := Id) (Fmt.HO O) .two name lg s = some l := by
  have hs : (Fmt.recordFirstW (m := Id) (Fmt.HO O) name).size = 32 := hO _
  have ha : Fmt.askOK Fmt.recordLabel (Fmt.recordFirstW (m := Id) (Fmt.HO O) name) (0 + 1)
      ByteArray.empty .seeds 0 0 = true := by
    unfold Fmt.askOK
    rw [hs]
    decide
  obtain ⟨x, hx⟩ : ∃ x, Fmt.Chain.queryW (m := Id) (Fmt.HO O)
      ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) (Fmt.HO O) name, 0⟩ ByteArray.empty .seeds 0 0
      (Fmt.blocksFor (s * (lg * 18 + 36))) = some x := by
    unfold Fmt.Chain.queryW
    rw [if_pos ha]
    exact ⟨_, rfl⟩
  refine ⟨(timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf x.2) 0).1.map fun y =>
    (y.1.map E.ofTriple, E.ofTriple y.2), ?_⟩
  show Option.map _ (Fmt.Chain.queryW (m := Id) (Fmt.HO O)
    ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) (Fmt.HO O) name, 0⟩ ByteArray.empty .seeds 0 0
    (Fmt.blocksFor (s * (lg * 18 + 36)))) = _
  rw [hx]
  rfl

/-- **A log that holds g's own answers at the strings of the key's seeds shows the seed.** -/
theorem seedAt_of_asked (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (k : IdKey)
    (lg s : ℕ) (h0 : Asked σ (seedFirst (Key.nameOf k.1 k.2.1 k.2.2)))
    (h1 : ∀ x ∈ seedRest (oB (g ()) (seedFirst (Key.nameOf k.1 k.2.1 k.2.2))) lg s, Asked σ x) :
    ∃ ρ, seedAt lg s k σ = some ρ := by
  obtain ⟨l, hl⟩ := recordSeedsW_HO (oB (g ())) (fun _ => size_digToBytes _)
    (Key.nameOf k.1 k.2.1 k.2.2) lg s
  refine ⟨seedOf lg s l, ?_⟩
  unfold seedAt
  rw [recordSeedsW_of_asked g σ hσ _ lg s h0 h1, hl]
  rfl

/-! ## Asking for the seeds -/

/-- Asks the oracle at each string of a list. -/
def askAll : List ByteArray → OComp (rom 256) Unit
  | [] => .pure ()
  | x :: l => .query () (bytesToBits x) fun _ => askAll l

/-- **Asks for the seeds of the table with the given name**: the first value; then the strings of
the seeds' round, which are made with the answer. -/
def askSeed (lg s : ℕ) (name : ByteArray) : OComp (rom 256) Unit :=
  .query () (bytesToBits (seedFirst name)) fun d => askAll (seedRest (digToBytes d) lg s)

/-- It tosses no coin. -/
theorem askAll_noCoin : ∀ l : List ByteArray, (askAll l).NoCoin
  | [] => trivial
  | _ :: l => fun _ => askAll_noCoin l

/-- It asks as many questions as the list has strings. -/
theorem askAll_bound : ∀ l : List ByteArray, (askAll l).QueryBound l.length
  | [] => trivial
  | _ :: l => fun _ => askAll_bound l

/-- Its log has an entry at each string of the list. -/
theorem askAll_asked (g : Fam (rom 256)) : ∀ (l : List ByteArray) (x : ByteArray), x ∈ l →
    Asked ((askAll l).withTrace.det g).2 x
  | y :: l, x, hx => by
    show Asked ((OComp.query () (bytesToBits y) fun _ => askAll l).withTrace.det g).2 x
    rw [det_withTrace_query]
    rcases List.mem_cons.1 hx with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨e, he, hq⟩ := askAll_asked g l x h
      exact ⟨e, List.mem_cons_of_mem _ he, hq⟩

/-- `askSeed` tosses no coin. -/
theorem askSeed_noCoin (lg s : ℕ) (name : ByteArray) : (askSeed lg s name).NoCoin :=
  fun _ => askAll_noCoin _

/-- The number of questions for the seeds: one, and two for each call of the round. -/
theorem askSeed_bound (lg s : ℕ) (name : ByteArray) :
    (askSeed lg s name).QueryBound (2 * seedCalls lg s + 1) := fun d => by
  have h := askAll_bound (seedRest (digToBytes d) lg s)
  have hl : (seedRest (digToBytes d) lg s).length = 2 * seedCalls lg s := by
    unfold seedRest
    rw [List.length_flatMap]
    simp [Nat.mul_comm]
  rw [hl] at h
  exact h

/-- **Its log has an entry at each of the seeds' strings.** -/
theorem askSeed_asked (g : Fam (rom 256)) (lg s : ℕ) (name : ByteArray) :
    Asked ((askSeed lg s name).withTrace.det g).2 (seedFirst name) ∧
      ∀ x ∈ seedRest (oB (g ()) (seedFirst name)) lg s,
        Asked ((askSeed lg s name).withTrace.det g).2 x := by
  unfold askSeed
  rw [det_withTrace_query]
  refine ⟨⟨_, List.mem_cons_self, rfl⟩, fun x hx => ?_⟩
  obtain ⟨e, he, hq⟩ := askAll_asked g _ x hx
  exact ⟨e, List.mem_cons_of_mem _ he, hq⟩

end OnBytes.Slice
