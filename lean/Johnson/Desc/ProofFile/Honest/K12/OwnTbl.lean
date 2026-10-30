-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OwnTbl.lean: OWN 7's TEXT.
Where J.fresh is none the first fold's table goes out at round 1,
in the FIRST part, whose coins testTbl does not read. One definition beside testTbl, at the first
part's coins.

  handedFirst    what the frame hands the test's first part off a run's coins; nothing where it refuses
  ownTbl         the first fold's own table: the table of the message of round 1: no second text of what
                 is sent; the place in every branch
  lendRow_first  of a row of two parts the first's coins are lendPart's at number 0
  ownTbl_depth   its depth at all k, w, h, where laysB says yes, at ok the constant yes
  own_in_run     THE TIE at round 1, at V := Empty: entry 0 of tablesOf y.1 is ownTbl's pair

ON THIS TEXT. It stands at PART 0's own coins: ScriptLots.lean's head speaks of part 1, and that
file says of this tree «in no lot». No statement here names `ownTbl` together with a measure over
coins. What a law over coins at this text has to mind:
(0-1) THE OWNER: ⟨place, 0⟩, start 0, count dueFresh s₀. The book's fact that lends it is that
`handedFirst` answers at the real book. `lendPart` also asks part 0's carried runs, so that the text
answers wordless where one is not lent though the table reads none: the Limits below say so, as
ScriptLots' point (v) does: whether it answers is a fact on the book, public.
(0-2) «No coin stands at two entries» can hold of part 0's own cut at the free entries and the pad
alone; at the packed coefficients where h > 0 it is false by the format.
(0-3) THE FRESH TABLE's COINS HAVE ONE OWNER, PART 0. In a law over this text alone the measure runs
over part 0's own cut. In any law that has BOTH this text and a text of part 1, these coins stand
ONCE under the measure, at part 0, and part 1's text is a function of them, as carried data: never
two draws, and never «for all» at one text and a measure at the other within one statement.
ScriptLots.lean's head says it from part 1's side; this says it from part 0's.

Beside the tie: tables_at_own_round, by name, and no premise on rows₀. own_in_run ties the table to the
run's coins, so it bears the label NOT IN FRONT OF A LAW OVER COINS, unless the tied letters are the
terms made of index, coins and seed.
The book's fact does not enter here.

A YES WOULD NOT SHOW: that a tree's text at part 0's coins is allowed · any V but
Empty: firstPart's coins hang on J.fresh by a match, so at a free J the crossing of TableOfRun.lean does
not type here; at the key V is Empty · the round's vals, which read rec₀ · a half behind the guard ·
anything over coins, and nothing on hiding.

Limits. ok as in testTbl; ownTbl_depth and own_in_run at the constant yes alone. lendPart at the first
part asks its carried runs too, so the text answers wordless if one of them is not lent, though the table
reads none of them. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS)

variable {Bk : ProverCoinCounts} {V W X : Type}

/-- What the frame hands the test's first part off a run's coins; nothing where it refuses. -/
def handedFirst (ch : ℕ) (J : TestJob W X) (k : Coins Bk) :
    Option (firstPart (V := Empty) J).Coins :=
  (lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨J.p.place, 0⟩ (firstPart (V := Empty) J)).toOption

/-- **The first fold's own table**, at the first part's coins: the one table of the message of round
1. The table of no word where the frame does not lend and where ok says no. -/
def ownTbl (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    Coins Bk → W → List Fmt.Drawn → VerifiableInference.Desc.Place × ProofFile.Honest.Table :=
  fun k w h =>
    match handedFirst ch J k with
    | some c =>
      if ok w (h.take n₀) (firstRd J c).mem then
        (J.p.place, ((msgAt J w (frontAt own₀ n₀ h) (firstRd J c) (testDrawsAt n₀ h)
          1).tables.head?).getD K1.wordlessTable)
      else (J.p.place, K1.wordlessTable)
    | none => (J.p.place, K1.wordlessTable)

/-- Of a row of two parts the first's coins are lendPart's at number 0. -/
theorem lendRow_first {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : VerifiableInference.Desc.Place} {p q : Part V W X} {c : RowCoins [p, q]}
    (h : lendRow B rows look a [p, q] 0 = .ok c) : lendPart B rows look ⟨a, 0⟩ p = .ok c.1 := by
  simp only [lendRow, Nat.zero_add] at h
  cases h0 : lendPart B rows look ⟨a, 0⟩ p with
  | error e =>
    rw [h0] at h
    cases h
  | ok c₁ =>
    rw [h0] at h
    cases h1 : lendPart B rows look ⟨a, 1⟩ q with
    | error e =>
      rw [h1] at h
      cases h
    | ok c₂ =>
      rw [h1] at h
      have e : c = (c₁, c₂, ()) := (Except.ok.inj h).symm
      subst e
      rfl

theorem handedFirst_of_row (ch : ℕ) (J : TestJob W X) (k : Coins Bk)
    (c : RowCoins [(firstPart J : Part Empty W X), restPart J])
    (hc : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part Empty W X), restPart J] 0 = .ok c) :
    handedFirst ch J k = some c.1 := by
  unfold handedFirst
  rw [lendRow_first hc]
  rfl

/-- **Own 7's text has its depth at all k, w, h**, where laysB says yes, at ok the constant yes. -/
theorem ownTbl_depth (J : TestJob W X) (hf : J.fresh = none) (ch : ℕ) (hch : ch = 0 ∨ ch = 1)
    (hB : laysB Bk ch J = true) (own₀ : X) (n₀ : ℕ) {a : ℕ} (ha : depthAt J 1 = some a)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn) :
    (ownTbl ch J own₀ n₀ (fun _ _ _ => true) k w h).2.logLength = a := by
  obtain ⟨c, hc⟩ := lends_of_B (V := Empty) Bk ch hch J hB k
  obtain ⟨T, hT, h1, -⟩ := tables_at_own_round J hf w (frontAt own₀ n₀ h) (frontAt own₀ n₀ h)
    (firstRd J c.1) (testDrawsAt n₀ h) ha
  unfold ownTbl
  simp only [handedFirst_of_row ch J k c hc, ↓reduceIte]
  rw [h1]
  exact hT

/-- **THE TIE AT ROUND 1.** Where the frame lends and play of the half returns, entry 0 of tablesOf
y.1 is ownTbl's pair. NOT IN FRONT OF A LAW OVER COINS (the head). -/
theorem own_in_run (J : TestJob W X) (hf : J.fresh = none)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (name : String) (v : Option Empty)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
    (hrs : rs.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (ch : ℕ) (k : Coins Bk) (c : RowCoins [(firstPart J : Part Empty W X), restPart J])
    (hc : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part Empty W X), restPart J] 0 = .ok c)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (hplay : play (rowSteps name J.p.place v [(firstPart J : Part Empty W X), restPart J] 0 rs c)
      ds back m = .ok y)
    (own₀ : X) (n₀ : ℕ) (hn : m.st.heard.length = n₀) (h : List Fmt.Drawn)
    (hh : h.take (n₀ + 1) = (m.st.heard ++ ds).take (n₀ + 1)) :
    (tablesOf y.1)[0]? =
      some (some (ownTbl ch J own₀ n₀ (fun _ _ _ => true) k m.st.input h)) := by
  have hfi : J.fresh.isNone = true := by simp [hf]
  have ha : depthAt J 1 = some s.Z.a := by
    unfold depthAt
    rw [hst, hfi]
    rfl
  have h2 : 2 ≤ firstLen J.p.nums.stages := by
    rw [hst]
    show 2 ≤ 2 + s.k
    omega
  obtain ⟨hT, -⟩ := half_tables J s t rest hst name v rs hrs c ds back m y hplay
  have hpl : ∀ p ∈ y.1, p.place = J.p.place :=
    play_place_all J.p.place _ ds back m y (row_place name J.p.place v _ 0 rs c) hplay
  obtain ⟨T, -, h1, h3⟩ := tables_at_own_round J hf m.st.input (frontOf m) (frontAt own₀ n₀ h)
    (firstRd J c.1) (byNo ds) ha
  have h4 : msgAt J m.st.input (frontAt own₀ n₀ h) (firstRd J c.1) (testDrawsAt n₀ h) 1 =
      msgAt J m.st.input (frontAt own₀ n₀ h) (firstRd J c.1) (byNo ds) 1 :=
    msgAt_causal J _ _ _ _ _ _ fun i hi => (draws_agree hn hh hi).symm
  have hText : ownTbl ch J own₀ n₀ (fun _ _ _ => true) k m.st.input h = (J.p.place, T) := by
    unfold ownTbl
    simp only [handedFirst_of_row ch J k c hc, ↓reduceIte]
    rw [h4, h3]
    rfl
  let B : ℕ → List (Option ProofFile.Honest.Table) := fun i =>
    (msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i).tables.map some
  have hlen : ∀ i, (B i).length =
      ((none :: depths J.fresh.isNone J.p.nums.stages).getD i none).toList.length := by
    intro i
    show ((msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i).tables.map some).length
      = _
    rw [List.length_map, tables_length]
    rfl
  have hco : coinsAtRound J c 1 = firstRd J c.1 := by
    unfold coinsAtRound
    rw [if_pos (by omega)]
  have hB1 : B 1 = [some T] := by
    show (msgAt J m.st.input (frontOf m) (coinsAtRound J c 1) (byNo ds) 1).tables.map some = _
    rw [hco, h1]
    rfl
  have hcnt : (flatTo B 1).length = 0 := by
    rw [flatTo_len B _ hlen]
    rfl
  have hat := flatTo_at B hB1 (rs.length - 2)
  rw [show 1 + 1 + (rs.length - 2) = rs.length by omega, hcnt] at hat
  have htab : tablesOf y.1 = (flatTo B rs.length).map (Option.map fun x => (J.p.place, x)) := by
    rw [tablesOf_at _ _ hpl, hT]
    rfl
  rw [htab, List.getElem?_map, hat, hText]
  rfl

end ProofFile.Honest.K12

end

#print axioms ProofFile.Honest.K12.handedFirst
#print axioms ProofFile.Honest.K12.ownTbl
#print axioms ProofFile.Honest.K12.lendRow_first
#print axioms ProofFile.Honest.K12.handedFirst_of_row
#print axioms ProofFile.Honest.K12.ownTbl_depth
#print axioms ProofFile.Honest.K12.own_in_run
