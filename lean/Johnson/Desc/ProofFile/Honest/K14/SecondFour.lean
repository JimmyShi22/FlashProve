-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/SecondFour.lean: the linear claim's second part ("K14, second
part", the place ⟨3, none, 0, .K14⟩: the first member of a proof file's last chain): FOUR OF THE
FIVE STATEMENTS ON ONE SUB-PROTOCOL (PlaysS, BehindS, ExchangeS, RidesPastS,
Honest/Thread/PaysS.lean) AT THE MEMBER 0 OF THE LAST CHAIN's THREAD (Honest/Thread/Last.lean),
general in the thread's letters, each under premises on these letters. The fifth, AcceptedS, is
second_acceptedS_last (Honest/K14/SecondDoor.lean), under a premise of its own.

The member has no round. Its decide function takes Omega over from the shared chain's end, joins it
to the request's own group and lays the row (Dot). Its row of the table shuts the items ev and dot
(the row (Eval) holds; (Dot)'s equation holds) and owes the item rows (every open row of the own
group holds).

TWO LIMITS THAT A READER MUST KNOW FIRST.
(1) NEITHER THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS ev AND dot. ExchangeS takes both from the
invariant in front of the member, where
they are open from the chain's start. The shared chain's honest thread does not carry them
(Honest/Thread/SharedRows.lean leaves the request's own items out), so they have to be shown where
the three chains are joined, and neither this file nor any file that it imports shows them there.
That (Dot)'s equation holds of an honest prover's
words is this member's one piece of mathematics. The library has it on values in a field
(dotEq_honest, Johnson/Desc/K14/Honest/Values.lean), tied to no thread and no witness.
(2) BehindS AND ExchangeS HOLD VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE. They are stated
with the form laid as the library's closed test fillZ (Johnson/Desc/Last/ShapeRowZero.lean); the
invariant in front of the member then asks that test, and neither this file nor any file that it
imports evaluates it at a state (on the test: Honest/K14/SecondBehind.lean's head).

  second_rows_behind  **THE STEP FORWARD, ON WORDS IN A FIELD**: behind a yes of the member: if
                      every open row of the own group in front holds of the words m, and (Dot)'s
                      equation holds of m, then every open row of the own group behind holds of m.
                      The library has the way back (row0_back, Johnson/Desc/Third/Law/Row0.lean);
                      both rest on two equivalences of the library's: old_says and dot_means
  second_rows_behindW the same with the words read through the state: the forward twin of the
                      library's row0_backW (Johnson/Desc/Third/Law/Row0Words.lean)
  second_owes0, second_shuts0   what the member's row owes and shuts: by evaluation
  second_playsS       PlaysS: the member declares no round and no oracle message
  second_behindS      BehindS: the form behind and what the member keeps are second_formKeeps
                      (Honest/K14/SecondBehind.lean); of the clause on the letter rides nothing is
                      shown: it goes to the caller in four premises
  second_exchangeS    **ExchangeS**, from second_rows_behindW, under hPL, hblk and five premises
                      that tie the thread's letters to words (below)
  rowsThereL          a value for the letter ML at which the premise hRows holds by its text: the
                      library's RowsThere; general in the reading and the reader of words
  second_ridesPastS   RidesPastS: the three pins go past. By their type they read nothing of the
                      last chain's state. TWO PREMISES, STRONGER THAN THE STATEMENT: a pin that
                      holds at the tables at hand still holds when rounds are added to them, at
                      every table, number and handed part
  pin_at_words        at this kind's maker of the items' meaning (mgWords,
                      Honest/K14/Thread2.lean) the second of these two premises holds: a shared
                      message's pin reads no string

THE FIVE PREMISES OF second_exchangeS. The caller picks a reading ρ into a field, a reader `words`
of a witness's words at a state, a fence Ok on two states, and readers omW, wv of Omega's and W's
words; the last three may hang on what was handed to the chain. The member brings Omega as a new
message at the next free number, so a reader that finds a message by the state's own book reads
other words behind the member than in front: hR is the library's structure Reads, which asks what is
needed and no more. hOk: the fence holds on both sides of a yes, where fillZ's test at border 0 says
yes. hEv: there the item ev gives that every open row of the own group in front holds. THIS IS MORE
THAN "(Eval) HOLDS": it says it of every open row that lies there. hDot: there the item dot gives
the semantic (Dot) (DotSem) at omW and wv. hRows: where fillZ's test at border 1 says yes, RowsThere
gives the item rows. hR and hOk are shown at the library's closed family of readers in
Honest/K14/SecondWords.lean, and hRows there at the library's closed sentence rowsOpen; hEv and hDot
at no letters.

What is not claimed. That the premises hold at any letters. That the thread's invariant holds at any
state. That the member accepts. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondBehind
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.Third.Law.Row0Words
import Johnson.Desc.Last.ShapeGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Later (Carries)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (Says AtDot Names RowsHold DotHolds DotSem RowsThere Reads
  says_congr dotEq_congr dot_means old_says own_same law_k14Second)
open VerifiableInference.Desc.Last (ItemL startLast fillZ shapeAt_of_fill fill_of_shapeAt step_zero
  atDot_of_shape started_of_shape names_of)
open Desc.K14 (P14 St)

/-! ## 1 The step forward, on words in a field -/

section core
variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- **Behind a yes of the member: the own group's open rows in front and (Dot)'s equation give the
own group's open rows behind.** h, hk: what a yes of the member says. a, n: two facts on the state
in front (Johnson/Desc/Third/Law/AtDot.lean; Row0.lean). -/
theorem second_rows_behind (p : P₁₄) (s s' : S₃) (h : Says p s s') (hk : Carries s.st s'.st)
    (a : AtDot p s) (n : Names s) (m : Words K) (hr : RowsHold ρ s m) (hd : DotHolds ρ p s m) :
    RowsHold ρ s' m := by
  obtain ⟨b, G, G', dot, hb, hG, hG', hrows, hm⟩ := dot_means ρ p s s' h a
  intro G'' hG'' r hr'
  rw [own_same p s s' h] at hG''
  obtain rfl : G' = G'' := Option.some.inj (hG'.symm.trans hG'')
  rw [hrows, Array.toList_push] at hr'
  rcases List.mem_append.1 hr' with h1 | h1
  · exact (old_says ρ s s' hk r (n G hG r h1) m).2 (hr G hG r h1)
  · obtain rfl := List.mem_singleton.1 h1
    obtain ⟨b', hb', e⟩ := hd
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    exact (hm m).2 e

end core

/-- **Behind a yes of the member, with the words read through the state**: the own group's open rows
in front and the semantic (Dot) give the own group's open rows behind. -/
theorem second_rows_behindW {K W : Type} [Field K] (ρ : OnBytes.Model.Reading K) (p : P₁₄)
    (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K) (omW wv : W → Nat → K)
    (hR : Reads p Ok words omW wv) (s s' : S₃) (ok : Ok s s') (h : Says p s s')
    (hk : Carries s.st s'.st) (a : AtDot p s) (n : Names s) (w : W)
    (hr : RowsHold ρ s (words s w)) (hd : DotSem ρ p omW wv s w) :
    RowsHold ρ s' (words s' w) := by
  refine second_rows_behind ρ p s s' h hk a n (words s' w) (fun G hG r hr' => ?_) ?_
  · exact (says_congr ρ s.st r _ _ (hR.older s s' w ok h)).2 (hr G hG r hr')
  · obtain ⟨b, hb, e⟩ := hd
    exact ⟨b, hb, dotEq_congr _ _ _ _ _ _ _ _ (fun y hy => (hR.omega s s' w ok h y hy).symm)
      (fun c hc => (hR.w s s' w ok h c hc).symm) e⟩

/-! ## 2 The member's row of the table -/

/-- What the member number 0 owes. -/
theorem second_owes0 : (LastRows.rows 0).owes = ([.rows] : List ItemL) := by decide

/-- What the member number 0 shuts. -/
theorem second_shuts0 : (LastRows.rows 0).shuts = ([.ev, .dot] : List ItemL) := by decide

/-! ## 3 The four, general in the letters -/

section general
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P S₁ Wt : Type}
  (L : LastThread.Letters Bk St S₃ Cl W₀ Rc Xi Tr X (P × S₁) Wt) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (fs : P × S₁ → VerifiableInference.Desc.First.S)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)

/-- **PlaysS at the member 0**, where what stands at the number 0 declares no round and no oracle
message. -/
theorem second_playsS {blk : Block S₃ Cl} (hb : L.bs[0]? = some blk) (hr : blk.rounds = [])
    (ho : blk.oracles = []) : PlaysS L.thread Said 0 :=
  playsS_of _ _ (plays_quiet (T := L.thread) hb hr ho)

/-- **BehindS at the member 0.** It holds vacuously wherever fillZ's test at border 0 is false. hPL,
hblk, hK, hO: second_formKeeps' four premises on the letters. hr, h₀, hst, hl: the clause on the
letter rides, handed on to the caller: the letter is a sentence R₀ and a list of clauses cs; R₀
holds behind the member's accepted step; each clause that speaks on both sides of the member stays
by what the member keeps; each clause that begins at border 1 holds behind the member's accepted
step. -/
theorem second_behindS (hPL : L.PL = fillZ p R fs)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hK : ∀ s s', SecondLaid p s s' → L.keeps 0 s s')
    (hO : ∀ x e s', (fillZ p R fs).shape 1 x e s' = true → L.order s')
    {R₀ : Nat → Local W₀ Rc Xi Tr → S₃ → Prop} {cs : List (RiderCl (Local W₀ Rc Xi Tr) S₃)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ R₀ b w s ∧ ridersOf cs b w s)
    (h₀ : ∀ blk, L.thread.bs[0]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said 0 k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (0 + 1) m.st.input s')
    (hst : ∀ x ∈ cs, x.lo ≤ 0 → 0 + 1 ≤ x.hi → StaysBy L.thread 0 x)
    (hl : ∀ x ∈ cs, x.lo = 0 + 1 → LaysAtS L.thread Said 0 x) : BehindS L.thread Said 0 :=
  behindS_of_keeps_and L.thread Said hr
    (formKeepsS_of Said (second_formKeeps L p R fs hPL hblk hK hO)) h₀ hst hl

/-- **ExchangeS at the member 0**: behind the member's accepted step the item rows holds, at every
continuation of the challenges. It takes the items ev and dot from the invariant in front, and holds
vacuously wherever fillZ's test at border 0 is false. hPL, hblk: the form is fillZ; what stands at
the number 0 has no round and the member's decide function. hR: the library's Reads, at every handed
part. hOk: the fence holds on both sides of a yes. hEv: ev gives that every open row of the own
group in front holds. hDot: dot gives the semantic (Dot). hRows: where fillZ's test at border 1 says
yes, RowsThere gives the item rows. -/
theorem second_exchangeS {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)
    (words : S₃ → Wt → Words K) (Ok : (P × S₁) × St → S₃ → S₃ → Prop)
    (omW wv : (P × S₁) × St → Wt → Nat → K) (hPL : L.PL = fillZ p R fs)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hR : ∀ u, Reads p (Ok u) words (omW u) (wv u))
    (hOk : ∀ a e s s', (fillZ p R fs).shape 0 a e s = true →
      (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide s rs gs = .ok s') → Ok (a, e) s s')
    (hEv : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).ev a y v →
      RowsHold ρ s (words s v))
    (hDot : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).dot a e y v →
      DotSem ρ p (omW (a, e)) (wv (a, e)) s v)
    (hRows : ∀ a e s' v, (fillZ p R fs).shape 1 a e s' = true → RowsThere ρ s' (words s' v) →
      L.ML.rows s' v) :
    ExchangeS L.thread Said 0 := by
  intro blk hb k s m E ds y cols s' hA hds hS
  obtain ⟨-, -, ⟨hF, -⟩, hI, -, -, -⟩ := hA.1
  obtain ⟨hM, hst⟩ := hS
  obtain ⟨gs, hd⟩ := Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [(hblk blk hb).decide] at hd
  have hk := (law_k14Second (Cl := Cl) p).1 _ _ _ _ hd
  have hs := (law_k14Second (Cl := Cl) p).2 _ _ _ _ hd
  -- the member has no round: no challenge comes
  rw [(hblk blk hb).rounds] at hds
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hds
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have ei := (play_mid _ _ _ _ _ hy).1
  have eh := play_heard _ _ _ _ _ hy
  rw [List.append_nil] at eh
  -- the form in front
  have hF' : (L.PL.shape 0 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
      (!decide (VerifiableInference.Desc.Last.lastPlaces.length ≤ 0) || L.PL.nothingLeft s)) =
      true := hF
  rw [Bool.and_eq_true] at hF'
  have h0 := hF'.1
  rw [hPL] at h0
  obtain ⟨f, o, hf, ho, hs0⟩ := shapeAt_of_fill p R _ _ h0
  have h1 := fill_of_shapeAt p R _ _ hf ho (step_zero (Cl := Cl) hs0 _ gs hd)
  have a : AtDot p s := atDot_of_shape hs0
  have n : Names s := names_of (started_of_shape hs0).2.2.1
  intro ds' (i : ItemL) hi
  have hi' : i ∈ (LastRows.rows 0).owes := hi
  rw [second_owes0] at hi'
  obtain rfl := List.mem_singleton.1 hi'
  show L.ML.rows s' (L.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [ei, eh]
  obtain ⟨_, G, G', dot, -, -, hG', hrows, -⟩ := dot_means ρ p s s' hs a
  have hG'' : s'.st.groups[s'.loc.own]? = some G' := by
    rw [own_same p s s' hs]
    exact hG'
  have e1 : (L.Mg m.st.input).ev (L.thread.seat k m s).1.1 (L.thread.strs E)
      (L.wit k m.st.input (m.st.heard ++ ds')) :=
    hI ds' ItemL.ev (show ItemL.ev ∈ startLast by decide)
  have e2 : (L.Mg m.st.input).dot (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2
      (L.thread.strs E) (L.wit k m.st.input (m.st.heard ++ ds')) :=
    hI ds' ItemL.dot (show ItemL.dot ∈ startLast by decide)
  refine hRows _ _ _ _ h1 ⟨G', hG'', ?_, ?_⟩
  · rw [hrows, Array.toList_push]
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  · exact second_rows_behindW ρ p _ words _ _ (hR _) s s' (hOk _ _ s s' h0 ⟨_, gs, hd⟩) hs hk a n _
      (hEv _ _ _ _ _ _ h0 e1) (hDot _ _ _ _ _ _ h0 e2) G' hG''

/-- **A value for the last chain's one item of its own**: the library's RowsThere at the words that
the witness gives at the state: the own group is there, has an open row, and every open row of it
holds. At it second_exchangeS's premise hRows holds by its text. -/
def rowsThereL {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (words : S₃ → Wt → Words K) :
    VerifiableInference.Desc.Last.MeaningL S₃ Wt :=
  { rows := fun s v => RowsThere ρ s (words s v) }

/-- **RidesPastS at the member 0**: the three pins go past. hPin₁, hPin: a pin that holds at the
tables at hand still holds when rounds are added to them: asked at every table, number and handed
part, with no invariant in front: so the two are stronger than the statement. Of the last chain's
state a pin reads nothing, by its type, so nothing is asked of what the member keeps. -/
theorem second_ridesPastS
    (hPin₁ : ∀ inp a b q E ps v, (L.Mg inp).pin₁ a b q (L.thread.strs E) v →
      (L.Mg inp).pin₁ a b q (L.thread.strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v, (L.Mg inp).pin a b e (L.thread.strs E) v →
      (L.Mg inp).pin a b e (L.thread.strs (E.add ps)) v) :
    RidesPastS L.thread Said 0 := by
  intro k s m E s' ps (i : ItemL) v _ _ hi hs _ h
  have hi' : i ∈ startLast := hi
  have hs' : i ∉ (LastRows.rows 0).shuts := hs
  rw [second_shuts0] at hs'
  simp only [startLast, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact hPin₁ _ _ _ _ _ _ _ h
  · exact hPin₁ _ _ _ _ _ _ _ h
  · exact absurd (by decide) hs'
  · exact absurd (by decide) hs'
  · exact hPin _ _ _ _ _ _ _ h

end general

/-- At this kind's maker of the items' meaning a shared message's pin reads no string. -/
theorem pin_at_words {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) (a b : Nat) (e : St) (y y' : Strs) (v : Wt)
    (h : (mgWords ℓ Q N Mg₀).pin a b e y v) : (mgWords ℓ Q N Mg₀).pin a b e y' v := h

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.second_rows_behind
#print axioms ProofFile.Honest.K14.second_rows_behindW
#print axioms ProofFile.Honest.K14.second_owes0
#print axioms ProofFile.Honest.K14.second_shuts0
#print axioms ProofFile.Honest.K14.second_playsS
#print axioms ProofFile.Honest.K14.second_behindS
#print axioms ProofFile.Honest.K14.second_exchangeS
#print axioms ProofFile.Honest.K14.second_ridesPastS
#print axioms ProofFile.Honest.K14.pin_at_words
