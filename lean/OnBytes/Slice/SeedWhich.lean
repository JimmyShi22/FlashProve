-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedWhich.lean: WHICH seed a log shows: the seed under the oracle; in both directions.
No probability.

OnBytes/Slice/SeedAsked.lean says that a log of g's own answers which holds the seeds' strings shows
a seed. Here the seed is named (`seedUnder`: the text of the program's `recordSeeds` at the hash
over g's function), and the converse is shown: whatever a log of g's own answers holds, if it shows
a seed at all, it shows that one. So wherever `seedAt` reads a seed off a log of g's own answers (a
committer's, a longer one, one with what is asked put behind it), it reads one value. (`seedAt` is
the field `seed` of `logRead`; of another `LogRead` nothing is said.)

Main definition.
 `seedUnder lg s k g`   the seed of the key k's table under g; `seedUnder_some`: there is one.
Main theorems.
 `seedAt_eq_of_asked`   under the hypotheses of `seedAt_of_asked`: `seedAt lg s k σ = seedUnder lg s
                        k g`. With `seedAt_text`, `seedUnder_text`, `bind_some_seedOf`,
                        `seedAt_step`.
 `askLog_sound`, `HM_sound`   what the hash that reads a log of g's own answers gives is what the
                        hash over g's function gives.
 `fetchFrom_sound`, `queryW_sound`, `recordSeedsW_sound`   the format's loop, one step of a chain
                        and the text of `recordSeeds`: what they give at a hash in the monad
                        `Option` they give at a plain hash with which that hash agrees wherever it
                        answers.
 `seedAt_sound`         THE CONVERSE: `Answers g σ` and `seedAt lg s k σ = some ρ` give `seedUnder
                        lg s k g = some ρ`.
 `seedAt_ask_eq`        behind a log of g's own answers the log of `askSeed` shows the seed under g.

What is not claimed. That `seedUnder` is what any checker computes: a checker that runs the
program's text by asking the oracle g would get it; no such checker is written. At the format's own
hash the text is the program's `recordSeeds` (`recordSeedsW_H`, OnBytes/Slice/RecordRead.lean); g is
any oracle. Nothing here on how the seeds are distributed (OnBytes/Slice/SeedBias.lean,
SeedRow.lean). Nothing on any hash function.

-/
import OnBytes.Slice.FineAtRecWrap

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory Cb Cb.Ood
open OnBytes.Tie (IdKey firstId)

/-- **The seed of the key k's table under the oracle g**: the text of the program's `recordSeeds` at
the hash over g's function, on the table's name. -/
noncomputable def seedUnder (lg s : ℕ) (k : IdKey) (g : Fam (rom 256)) :
    Option (Fin s → (Fin lg → GE) × NZ) :=
  (recordSeedsW (m := Id) (Fmt.HO (oB (g ()))) .two (Key.nameOf k.1 k.2.1 k.2.2) lg s).map
    (seedOf lg s)

/-- There is one. -/
theorem seedUnder_some (lg s : ℕ) (k : IdKey) (g : Fam (rom 256)) :
    ∃ ρ, seedUnder lg s k g = some ρ := by
  obtain ⟨l, hl⟩ := recordSeedsW_HO (oB (g ())) (fun _ => size_digToBytes _)
    (Key.nameOf k.1 k.2.1 k.2.2) lg s
  exact ⟨seedOf lg s l, by unfold seedUnder; rw [hl]; rfl⟩

/-- `seedAt`, written out. -/
theorem seedAt_text (lg s : ℕ) (k : IdKey) (σ : Trace (rom 256)) :
    seedAt lg s k σ =
      (recordSeedsW (m := Option) (Fmt.HM (askLog σ)) .two (Key.nameOf k.1 k.2.1 k.2.2) lg s).bind
        fun r => r.map (seedOf lg s) := rfl

/-- `seedUnder`, written out. -/
theorem seedUnder_text (lg s : ℕ) (k : IdKey) (g : Fam (rom 256)) :
    seedUnder lg s k g =
      Option.map (seedOf lg s)
        (recordSeedsW (m := Id) (Fmt.HO (oB (g ()))) .two (Key.nameOf k.1 k.2.1 k.2.2) lg s) := rfl

/-- What `seedAt` makes of a text that gives X, for a letter X. -/
theorem bind_some_seedOf (lg s : ℕ) (X : Option (List (List E × E))) :
    (some X).bind (fun r => r.map (seedOf lg s)) = X.map (seedOf lg s) := rfl

/-- `recordSeedsW_of_asked` (OnBytes/Slice/SeedAsked.lean) under what `seedAt` makes of the text. -/
theorem seedAt_step (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (k : IdKey)
    (lg s : ℕ) (h0 : Asked σ (seedFirst (Key.nameOf k.1 k.2.1 k.2.2)))
    (h1 : ∀ x ∈ seedRest (oB (g ()) (seedFirst (Key.nameOf k.1 k.2.1 k.2.2))) lg s, Asked σ x) :
    (recordSeedsW (m := Option) (Fmt.HM (askLog σ)) .two (Key.nameOf k.1 k.2.1 k.2.2) lg s).bind
        (fun r => r.map (seedOf lg s)) =
      (some (recordSeedsW (m := Id) (Fmt.HO (oB (g ()))) .two (Key.nameOf k.1 k.2.1 k.2.2)
        lg s)).bind (fun r => r.map (seedOf lg s)) :=
  congrArg (fun z => Option.bind z fun r => Option.map (seedOf lg s) r)
    (recordSeedsW_of_asked g σ hσ _ lg s h0 h1)

/-- **WHICH seed a log shows**: a log that holds g's own answers at the strings of the key's seeds
shows the seed under g. The proof is a chain of four named equations, written as a term. -/
theorem seedAt_eq_of_asked (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (k : IdKey)
    (lg s : ℕ) (h0 : Asked σ (seedFirst (Key.nameOf k.1 k.2.1 k.2.2)))
    (h1 : ∀ x ∈ seedRest (oB (g ()) (seedFirst (Key.nameOf k.1 k.2.1 k.2.2))) lg s, Asked σ x) :
    seedAt lg s k σ = seedUnder lg s k g :=
  (seedAt_text lg s k σ).trans ((seedAt_step g σ hσ k lg s h0 h1).trans
    ((bind_some_seedOf lg s _).trans (seedUnder_text lg s k g).symm))

/-! ## The converse: a log of g's own answers that shows a seed shows g's -/

/-- What `askLog` finds in a log of g's own answers is g's answer. -/
theorem askLog_sound (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (x b : ByteArray)
    (h : askLog σ x = some b) : b = oB (g ()) x := by
  unfold askLog at h
  by_cases h9 : (Fmt.wordAt x 65).toNat % 65536 = 169
  · rw [if_pos h9] at h
    cases h
  · rw [if_neg h9] at h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
    have h1 : (e.2.1 : List Bool) = bytesToBits x := by simpa using List.find?_some he
    have h2 := hσ e (List.mem_of_find?_eq_some he)
    show digToBytes (e.2.2 : Dig 256) = digToBytes (g () (bytesToBits x))
    rw [h2, ← h1]
    rfl

/-- So what the hash that reads the log gives is what the hash over g's function gives. -/
theorem HM_sound (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (n t i : ℕ)
    (st b x : ByteArray) (h : Fmt.HM (m := Option) (askLog σ) n t i st b = some x) :
    x = Fmt.HO (oB (g ())) n t i st b := by
  unfold Fmt.HM at h
  unfold Fmt.HO
  by_cases hn : n = 162
  · rw [if_pos hn] at h
    rw [if_pos hn]
    obtain ⟨a, ha, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c, hc, h3⟩ := Option.bind_eq_some_iff.1 h2
    rw [← askLog_sound g σ hσ _ a ha, ← askLog_sound g σ hσ _ c hc]
    exact (Option.some.inj h3).symm
  · rw [if_neg hn] at h
    rw [if_neg hn]
    exact askLog_sound g σ hσ _ x h

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Option ByteArray)
  (H' : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (hh : ∀ n t i st b x, h n t i st b = some x → x = H' n t i st b)
  (lab : ℕ) (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind) (w nonce : ℕ)

include hh

/-- The loop that fetches a round's blocks: what it gives at h it gives at H'. -/
theorem fetchFrom_sound : ∀ (n j : ℕ) (acc x : Array ByteArray),
    Fmt.fetchFrom h lab rho i msg kind w nonce n j acc = some x →
      x = Fmt.fetchFrom (m := Id) H' lab rho i msg kind w nonce n j acc
  | 0, _, _, _, e => (Option.some.inj e).symm
  | n + 1, j, acc, x, e => by
    unfold Fmt.fetchFrom at e ⊢
    obtain ⟨c, hc, e2⟩ := Option.bind_eq_some_iff.1 e
    have hc' : c = Fmt.callW (m := Id) H' lab rho i msg kind w nonce j := hh _ _ _ _ _ _ hc
    subst hc'
    exact fetchFrom_sound n (j + 1) _ x e2

/-- One step of a chain. -/
theorem queryW_sound (c : Fmt.Chain) (K : ℕ) (x : Option (Fmt.Chain × Array ByteArray))
    (e : Fmt.Chain.queryW h c msg kind w nonce K = some x) :
    x = Fmt.Chain.queryW (m := Id) H' c msg kind w nonce K := by
  unfold Fmt.Chain.queryW at e ⊢
  by_cases ha : Fmt.askOK c.label c.rho (c.round + 1) msg kind w nonce = true
  · rw [if_pos ha] at e
    rw [if_pos ha]
    obtain ⟨bs, hb, e2⟩ := Option.bind_eq_some_iff.1 e
    unfold Fmt.fetchW at hb
    obtain ⟨bs0, hb0, e3⟩ := Option.bind_eq_some_iff.1 hb
    have h0 := fetchFrom_sound h H' hh c.label c.rho (c.round + 1) msg kind w nonce _ 0 #[] bs0 hb0
    subst h0
    obtain rfl := Option.some.inj e3
    exact (Option.some.inj e2).symm
  · rw [if_neg ha] at e
    rw [if_neg ha]
    exact (Option.some.inj e).symm

/-- The text of `recordSeeds`. -/
theorem recordSeedsW_sound (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (x : Option (List (List E × E))) (e : recordSeedsW (m := Option) h f name bits count = some x) :
    x = recordSeedsW (m := Id) H' f name bits count := by
  obtain ⟨ρ0, h0, e2⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨r, hr, e3⟩ := Option.bind_eq_some_iff.1 e2
  have a0 : ρ0 = Fmt.recordFirstW (m := Id) H' name := hh _ _ _ _ _ _ h0
  subst a0
  have a1 := queryW_sound h H' hh ByteArray.empty .seeds 0 0 _ _ r hr
  subst a1
  exact (Option.some.inj e3).symm

end

/-- **A log of g's own answers that shows a seed shows the seed under g.** No condition on what the
log holds. -/
theorem seedAt_sound (g : Fam (rom 256)) (σ : Trace (rom 256)) (hσ : Answers g σ) (k : IdKey)
    (lg s : ℕ) (ρ : Fin s → (Fin lg → GE) × NZ) (h : seedAt lg s k σ = some ρ) :
    seedUnder lg s k g = some ρ := by
  unfold seedAt at h
  obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
  have e := recordSeedsW_sound (Fmt.HM (askLog σ)) (Fmt.HO (oB (g ())))
    (fun n t i st b x hx => HM_sound g σ hσ n t i st b x hx) .two _ lg s r hr
  unfold seedUnder
  rw [← e]
  exact h2

/-- Behind a log of g's own answers, the log of `askSeed` under g shows the seed under g. -/
theorem seedAt_ask_eq (lg s : ℕ) (g : Fam (rom 256)) (σ : Trace (rom 256)) (k : IdKey)
    (hσ : Answers g σ) :
    seedAt lg s k (σ ++ ((askSeed lg s (Key.nameOf k.1 k.2.1 k.2.2)).withTrace.det g).2) =
      seedUnder lg s k g := by
  obtain ⟨ρ, hρ⟩ := seedAt_ask lg s g σ k hσ
  rw [hρ]
  exact (seedAt_sound g _ (fun e he => (List.mem_append.1 he).elim (hσ e)
    (det_withTrace_ans g _ e)) k lg s ρ hρ).symm

end OnBytes.Slice
