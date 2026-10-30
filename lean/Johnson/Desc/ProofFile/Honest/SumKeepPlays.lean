-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumKeepPlays.lean: `play` (Honest/Frame.lean) on the rounds of the
masked sumcheck's part with a kept state (`keepPart`, Honest/SumKeep.lean) returns the rounds that
`sumPart` at the earlier job plays, and leaves the state as it found it. Lemmas with their proofs.

How it relates to its neighbours. Honest/SumKeepLaw.lean proves that the two parts, played alone,
show the same rounds (`alone_keep_on`). The lemmas of Honest/SumLaw/Plays.lean and
Honest/SumLaw/PlaysWhole.lean that compute `play` on one part's rounds have two more hypotheses:
every message has the shape that its round declares (`fitsFrom`), and the whole list of rounds as
played, with the tables (`playedFrom`). This file carries both over, by the induction of
`aloneFrom_agree`, and applies `play_steps_whole`. What the part is handed before its rounds
(`Seen`, Honest/Frame.lean: the rounds shown and the columns opened) is a bound letter in
every lemma that names it, the same value on both sides; `play_keep_on` starts at a state of the run
that shows it.

  1  `fitsFrom_agree`, `playedFrom_agree`   lists of moves that agree have the same test on shapes
     and the same rounds as played
  2  `fits_keep_on`, `played_keep_on`   the two parts
  3  `sumPart_rounds`, `play_keep_on`   `play` on the part's rounds

Limits.
  * As in Honest/SumKeepLaw.lean: the run starts at a state without a kept state, and the hypothesis
    `KeepJob.FaithfulOn` has to be proved by whoever supplies the job.
  * `play_keep_on` speaks of one part's rounds. Lists of several parts are joined by `play_append`
    (Honest/Law/Play.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Keep
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw

variable {V W X K : Type}

/-! ## 1 Lists of moves that agree -/

/-- **Lists that agree have the same test on the messages' shapes.** -/
theorem fitsFrom_agree (J : KeepJob W X K) {name endName : String}
    (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle))
      (l₁ : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E))
      (l₂ : List (SumCoins name endName J.base → Seen → State W X → List E)) (n : Nat)
      (own : List Fmt.Drawn) (shown : List Fmt.RoundView) (k : Option K) (ds : List Fmt.Drawn),
      Agree J c w H x S n l₁ l₂ → own.length = n → shown.length = n → Kept J w H x own k →
      fitsFrom (C := SumCoins name endName J.base) c rs (withPass J.pass n (l₁.map mvOf))
          ⟨w, H ++ own, (x, k)⟩ (S.plus shown) ds =
        fitsFrom c rs (l₂.map mvOf) ⟨w, H ++ own, x⟩ (S.plus shown) ds
  | [], [], [], _, _, _, _, [], _, _, _, _ => rfl
  | [], [], [], _, _, _, _, _ :: _, _, _, _, _ => rfl
  | _ :: _, [], [], _, _, _, _, [], _, _, _, _ => rfl
  | _ :: _, [], [], _, _, _, _, _ :: _, _, _, _, _ => rfl
  | [], _ :: _, _ :: _, _, _, _, _, [], _, _, _, _ => rfl
  | [], _ :: _, _ :: _, _, _, _, _, _ :: _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _, _, _, _, [], _, _, _, _ => rfl
  | r :: rs, a :: l₁, b :: l₂, n, own, shown, k, d :: ds, hA, ho, hs, hk => by
    obtain ⟨k', hp, hk'⟩ := pass_kept J w H x n own d k ho hk
    have e := hA.head own shown k ho hs hk
    have o' : (own ++ [d]).length = n + 1 := by
      rw [List.length_append, ho]
      rfl
    have s' : (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]).length = n + 1 := by
      rw [List.length_append, hs]
      rfl
    show ((sayE (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩)).fits r.1 r.2 &&
        fitsFrom (C := SumCoins name endName J.base) c rs (withPass J.pass (n + 1) (l₁.map mvOf))
          ⟨w, (H ++ own) ++ [d], J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩⟩
          ((S.plus shown).plus [rvSaid (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩) d]) ds) =
      ((sayE (b c (S.plus shown) ⟨w, H ++ own, x⟩)).fits r.1 r.2 &&
        fitsFrom c rs (l₂.map mvOf) ⟨w, (H ++ own) ++ [d], x⟩
          ((S.plus shown).plus [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) ds)
    rw [hp, e, List.append_assoc H, Seen.plus_plus S,
      fitsFrom_agree J c w H x S rs l₁ l₂ (n + 1) (own ++ [d])
        (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) k' ds hA.tail o' s' hk']
  | _, [], _ :: _, _, _, _, _, _, hA, _, _, _ => False.elim hA
  | _, _ :: _, [], _, _, _, _, _, hA, _, _, _ => False.elim hA

/-- **Lists that agree have the same rounds as played.** -/
theorem playedFrom_agree (J : KeepJob W X K) {name endName : String}
    (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen)
    (nm : String) (ad : Addr) :
    ∀ (l₁ : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E))
      (l₂ : List (SumCoins name endName J.base → Seen → State W X → List E)) (n : Nat)
      (own : List Fmt.Drawn) (shown : List Fmt.RoundView) (k : Option K) (ds : List Fmt.Drawn),
      Agree J c w H x S n l₁ l₂ → own.length = n → shown.length = n → Kept J w H x own k →
      playedFrom (C := SumCoins name endName J.base) nm ad c (withPass J.pass n (l₁.map mvOf))
          ⟨w, H ++ own, (x, k)⟩ (S.plus shown) ds =
        playedFrom nm ad c (l₂.map mvOf) ⟨w, H ++ own, x⟩ (S.plus shown) ds
  | [], [], _, _, _, _, [], _, _, _, _ => rfl
  | [], [], _, _, _, _, _ :: _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, _, _, [], _, _, _, _ => rfl
  | a :: l₁, b :: l₂, n, own, shown, k, d :: ds, hA, ho, hs, hk => by
    obtain ⟨k', hp, hk'⟩ := pass_kept J w H x n own d k ho hk
    have e := hA.head own shown k ho hs hk
    have o' : (own ++ [d]).length = n + 1 := by
      rw [List.length_append, ho]
      rfl
    have s' : (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]).length = n + 1 := by
      rw [List.length_append, hs]
      rfl
    show (playedFrom (C := SumCoins name endName J.base) nm ad c
        (withPass J.pass (n + 1) (l₁.map mvOf))
        ⟨w, (H ++ own) ++ [d], J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩⟩
        ((S.plus shown).plus [rvSaid (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩) d]) ds).map
          ((⟨nm, ad.place, ad.part, true,
            (sayE (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩)).vals.map Said.got,
            (sayE (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩)).tables.map some, d⟩ : Played) :: ·) =
      (playedFrom nm ad c (l₂.map mvOf) ⟨w, (H ++ own) ++ [d], x⟩
        ((S.plus shown).plus [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) ds).map
          ((⟨nm, ad.place, ad.part, true,
            (sayE (b c (S.plus shown) ⟨w, H ++ own, x⟩)).vals.map Said.got,
            (sayE (b c (S.plus shown) ⟨w, H ++ own, x⟩)).tables.map some, d⟩ : Played) :: ·)
    rw [hp, e, List.append_assoc H, Seen.plus_plus S,
      playedFrom_agree J c w H x S nm ad l₁ l₂ (n + 1) (own ++ [d])
        (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) k' ds hA.tail o' s' hk']
  | [], _ :: _, _, _, _, _, _, hA, _, _, _ => False.elim hA
  | _ :: _, [], _, _, _, _, _, hA, _, _, _ => False.elim hA

/-! ## 2 The two parts -/

/-- **The test on the messages' shapes is `sumPart`'s.** -/
theorem fits_keep_on (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (w : W) (h : List Fmt.Drawn) (x : X)
    (hOk : Ok w h x) (seen : Seen) (ds : List Fmt.Drawn) :
    fitsFrom (C := SumCoins name endName J.base) c rs (keepPart (V := V) name endName J).moves
        ⟨w, h, (x, none)⟩ seen ds =
      fitsFrom (C := SumCoins name endName J.base) c rs
        (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds := by
  have e := fitsFrom_agree J c w h x seen rs (sumGs name endName J.job)
    (sumGs name endName J.base) 0 [] [] none ds (agree_all J hJ c w h x hOk seen) rfl rfl
    (Or.inl rfl)
  rw [List.append_nil, Seen.plus_nil] at e
  rw [keepPart_moves, sumPart_moves]
  exact e

/-- **The rounds as played are `sumPart`'s.** -/
theorem played_keep_on (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (nm : String) (ad : Addr) (w : W) (h : List Fmt.Drawn) (x : X) (hOk : Ok w h x)
    (seen : Seen) (ds : List Fmt.Drawn) :
    playedFrom (C := SumCoins name endName J.base) nm ad c
        (keepPart (V := V) name endName J).moves ⟨w, h, (x, none)⟩ seen ds =
      playedFrom (C := SumCoins name endName J.base) nm ad c
        (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds := by
  have e := playedFrom_agree J c w h x seen nm ad (sumGs name endName J.job)
    (sumGs name endName J.base) 0 [] [] none ds (agree_all J hJ c w h x hOk seen) rfl rfl
    (Or.inl rfl)
  rw [List.append_nil, Seen.plus_nil] at e
  rw [keepPart_moves, sumPart_moves]
  exact e

/-! ## 3 `play` on the part's rounds -/

/-- `sumPart` has as many moves as its call has rounds. -/
theorem sumPart_rounds (name endName : String) (J : SumJob W X) :
    (sumPart (V := V) name endName J).moves.length = (scalarsOf J.shape).length := by
  have e : ((sumGs name endName J).map mvOf).length = (scalarsOf J.shape).length := by
    rw [List.length_map]
    exact sumGs_rounds name endName J
  rw [sumPart_moves]
  exact e

/-- **`play` on the rounds of the part with a kept state**: where `sumPart` at the earlier job
passes the test on shapes and plays the rounds `l`, `play` returns `l`; after it the part's own
challenges are heard, what was passed on is unchanged, no kept state is left, and the columns opened
(`seen.opened`) stay as they were. -/
theorem play_keep_on (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (nm : String) (ad : Addr) (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (w : W)
    (h : List Fmt.Drawn) (x : X) (hOk : Ok w h x) (loc : List Fmt.Drawn) (seen : Seen)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (l : List Played)
    (hf : fitsFrom (C := SumCoins name endName J.base) c rs
      (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds = true)
    (hp : playedFrom (C := SumCoins name endName J.base) nm ad c
      (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds = some l) :
    play ((keepPart (V := V) name endName J).steps nm ad rs v c) ds back
        ⟨⟨w, h, (x, none)⟩, loc, seen.rounds, seen.opened⟩ =
      .ok (l, ⟨⟨w, h ++ ds, (x, none)⟩, loc ++ ds, seen.rounds ++ roundsOf l, seen.opened⟩) := by
  have hl : ds.length = (scalarsOf J.base.shape).length :=
    (fits_lengths c rs _ _ seen ds hf).2.trans (sumPart_rounds name endName J.base)
  have f' := (fits_keep_on (V := V) name endName J Ok hJ c rs w h x hOk seen ds).trans hf
  have p' := (played_keep_on (V := V) name endName J Ok hJ c nm ad w h x hOk seen ds).trans hp
  have q := play_steps_whole (keepPart (V := V) name endName J) (fun _ _ => rfl)
    (fun _ _ _ => rfl) nm ad rs v c ds back
        ⟨⟨w, h, (x, none)⟩, loc, seen.rounds, seen.opened⟩ l f' p'
  refine q.trans ?_
  show (Except.ok (l, (⟨stateFrom (keepPart (V := V) name endName J).moves ⟨w, h, (x, none)⟩ ds,
    loc ++ ds, seen.rounds ++ roundsOf l, seen.opened⟩ : Mid W (X × Option K))) :
      Except Refusal (List Played × Mid W (X × Option K))) = _
  rw [state_keep name endName J w h x ds hl]

end ProofFile.Honest.Keep

#print axioms ProofFile.Honest.Keep.fitsFrom_agree
#print axioms ProofFile.Honest.Keep.playedFrom_agree
#print axioms ProofFile.Honest.Keep.fits_keep_on
#print axioms ProofFile.Honest.Keep.played_keep_on
#print axioms ProofFile.Honest.Keep.sumPart_rounds
#print axioms ProofFile.Honest.Keep.play_keep_on
