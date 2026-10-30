-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/SameRounds.lean: **a lookup's row that passes its tables
on, at the jobs and the store of Honest/K3/RowKeepFill.lean, shows the rounds of the earlier row at
`fastJobs`**, played alone and seated in a chain's letters; and it leaves the state as it found it.
Conditional on: the input is settled at a.base; a.base challenges at least are heard in front of the
row; the two rows' coins are read alike; for the seated row, laws of get and set. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the kept row is `lookRowKeep (fastKeeps R row a) a`, the
earlier row `lookRow R (fastJobs a.face row).asked a`; a row played alone is `aloneRow`, the state
behind it `endRow` (Honest/K3/Law/PlayPart.lean).

What is shown.
  1 `faithfulOn_mono`, `fastKeeps_lawful`, `fastKeeps_steady`, `alpha_number`, `alpha_real`: the
    filling shows the hypotheses of Honest/K3/Law/Keep/RowKeepLaw.lean: `Keeps.Lawful` without a
    hypothesis; `Keeps.SteadyFrom` under `Reads.Steady` and `Ask.Settled`; alpha's number in the
    row.
  2 `sameRounds`, `sameEnd`: the two main theorems at a reader of the challenges that is steady from
    n on. `sameRounds_real`, `sameEnd_real`: **at the reader that a lot seats (`theReads`).**
    `sameCoins`: for all coins of the kept row there are coins of the earlier row that are read
    alike.
  3 `aloneSeat_keep`, `endSeat_keep`, `unlift_onto`, `seatCoins_keep`: the same of the seated rows,
    at the row's letters. `sameSeat_real`, `sameSeatEnd_real`, `sameSeatCoins`: **at the filling and
    at `theReads`.**

Hypotheses that remain, by name.
  `hw : Ask.Settled a.base w`: from a.base challenges on the input no longer moves (`askOf_settled`,
    Honest/K3/WitLaw.lean, shows it at the inputs that are seated, under its own condition on the
    digits).
  `hb : a.base ≤ h.length`: at the state in front of the row a.base challenges at least are heard.
    Without it the store could be made of challenges that are not there, and the statement could
    fail: that a store made of fewer than `pastAlpha a` challenges differs is tried in
    Honest/K3/StoreToy.lean [not in this library].
  `hc`: the two rows' coins are read alike, part by part (`RowRel SpentSame`); `sameCoins` and
    `sameSeatCoins` say that such coins of the earlier row exist for all coins of the kept row.
  `hl` in the theorems on the state: there are as many challenges as the row has moves.
  For the seated row: hgs: get (set x y) = y; h0: get t₁.own = rowOwn₀; for the state behind it also
    hss: set (set x y) y' = set x y' and hsg: set x (get x) = x. These four (`hgs`, `h0`, `hss`,
    `hsg`) are for whoever fills the chain's state and seats the row in it to show.
  At a reader that is steady from n on, and at the row's letters: `hR`: `Reads.Steady`; `hα`:
    alpha's own challenge is the n-th at the latest; `hL`, `hS`: `Keeps.Lawful`, `Keeps.SteadyFrom`.
    `h`, `hi`: (in `faithfulOn_mono`) `FaithfulOn` at Ok; Ok' gives Ok. `h`: (in `alpha_number`,
    `alpha_real`) alpha is the stage number j.

Imported: Honest/SumKeepLaw.lean, Honest/SumKeep.lean and Honest/SumLaw/.

Users. Honest/K3/Law/Keep/SeatPlays.lean [not in this library],
Honest/K3/Law/Keep/SeatKeepFits.lean, Honest/K3/Law/Keep/CoinsBack.lean [not in this library],
Honest/K3/Law/Keep/LotsSame.lean [not in this library]; tried at two small cases in
Honest/K3/Law/Keep/SameRoundsToy.lean [not in this library; so here read: not tested in this
library]. Meant for a lot beside `rowLot` at the real letters.

Limits. The rows are played alone: that the frame's player goes through on the kept row is shown,
conditional on `Keeps.Shaped`, in Honest/K3/Law/Keep/RowKeepFits.lean, and on the seated kept row,
with the rounds of the seated earlier row, under the hypotheses that its head names, in
Honest/K3/Law/Keep/SeatPlays.lean [not in this library; so here read: not proved in this library].
The kept row starts at `rowOwn₀`. Both rows stand at one letter row for the table's rows and at one
place; nothing is said here of two lots: that the two lots show the same rounds is shown in
Honest/K3/Law/Keep/LotsSame.lean [not in this library; so here read: not proved in this library].
That all coins of the earlier row have coins of the kept row that are read alike is shown in
Honest/K3/Law/Keep/CoinsBack.lean [not in this library; so here read: not proved in this library].
How long a move takes is not said and has not been measured here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowKeepFill
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKeyLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.StoreStays
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.StoreGives
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.LiftLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)

variable {V V₁ W₁ X₁ : Type}

/-! ## 1 The filling shows the hypotheses on the letters -/

/-- `KeepJob.FaithfulOn` at a condition gives it at every condition that implies that one. -/
theorem faithfulOn_mono {W X K : Type} {J : KeepJob W X K}
    {Ok Ok' : W → List Fmt.Drawn → X → Prop} (h : J.FaithfulOn Ok)
    (hi : ∀ w hd x, Ok' w hd x → Ok w hd x) : J.FaithfulOn Ok' :=
  ⟨fun w f rs ho hl => h.round w f rs (hi _ _ _ ho) hl,
    fun w f rs m ho hl => h.inY w f rs m (hi _ _ _ ho) hl,
    fun w f rs ho hl => h.ends w f rs (hi _ _ _ ho) hl⟩

/-- **The filling fits the earlier row at `fastJobs`.** No hypothesis. -/
theorem fastKeeps_lawful (R : Reads) (row : E → Nat → E) (a : At) :
    (fastKeeps R row a).Lawful R (fastJobs a.face row).asked a where
  job_some := fastKeeps_some R row a
  job_none := fastKeeps_none R row a
  faithful := fun s hs Jk hJ => by
    have key : ∀ (J₀ : KeepJob Ask (Option Store) Kept)
        (Ok : Ask → List Fmt.Drawn → Option Store → Prop), J₀.FaithfulOn Ok →
        (∀ w hd x, StoreOk R row a w hd x → Ok w hd x) → some J₀ = some Jk →
        Jk.FaithfulOn (fastKeeps R row a).StoreOk := by
      intro J₀ Ok h1 h2 e
      obtain rfl := Option.some.inj e
      exact faithfulOn_mono h1 h2
    cases s with
    | tie m =>
      cases m with
      | zero => exact key _ _ (tie0Keep_faithful R row a) (fun _ _ _ hx => storeOk_tie0 hx) hJ
      | succ m => exact key _ _ (tieKeep_faithful R row a m) (fun _ _ _ hx => storeOk_tie hx) hJ
    | split i =>
      exact key _ _ (splitKeep_faithful R row a i (by have := stages_split_range hs; omega))
        (fun _ _ _ hx => storeOk_split hx) hJ
    | key i k =>
      exact key _ _ (keyKeep_faithful R row a i k) (fun _ _ _ hx => storeOk_key_row hx hs) hJ
    | tab l => exact key _ _ (tabKeep_faithful R row a l) (fun _ _ _ hx => storeOk_tab_row hx hs) hJ
    | leaves => exact key _ _ (leavesKeep_faithful R row a) (fun _ _ _ hx => storeOk_leaves hx) hJ
    | bits => exact key _ _ (bitsKeep_faithful R row a) (fun _ _ _ hx => storeOk_bits hx) hJ
    | shift => exact none_some hJ
    | alpha => exact none_some hJ
    | join => exact none_some hJ
    | keyLine i k => exact none_some hJ
    | tabLine l => exact none_some hJ
    | zero => exact none_some hJ

/-- **The filling's store no longer moves.** Conditional on `Reads.Steady` and `Ask.Settled` at n.
-/
theorem fastKeeps_steady (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (n : Nat)
    (hR : R.Steady a n) (hw : Ask.Settled n w) : (fastKeeps R row a).SteadyFrom w n :=
  fun h more hn => storeAt_append row hR hw h more hn

/-- Alpha's number in the row is not below `oAlpha`. -/
theorem alpha_number (f : LFace) (j : Nat) (h : (stages f)[j]? = some .alpha) : oAlpha f ≤ j := by
  unfold oAlpha
  by_cases hs : f.shifted = true
  · rw [if_pos hs]
    cases j with
    | zero => simp [stages, hs] at h
    | succ j => omega
  · rw [if_neg hs]
    omega

/-- Alpha's own challenge is number `pastAlpha a` at the latest. -/
theorem alpha_real (a : At) (j : Nat) (h : (stages a.face)[j]? = some .alpha) :
    pastAlpha a ≤ a.base + j + 1 := by
  have := alpha_number a.face j h
  unfold pastAlpha
  omega

/-! ## 2 The rows, played alone -/

/-- **The kept row shows the rounds of the earlier row**, at a reader of the challenges that is
steady from n on. Conditional on `Reads.Steady`, `Ask.Settled` at n, hα (alpha's own challenge is
the n-th at the latest), hb (a.base challenges at least are heard in front of the row) and hc (the
coins are read alike). -/
theorem sameRounds (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (n : Nat) (hR : R.Steady a n)
    (hw : Ask.Settled n w) (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1)
    (c : RowCoins (lookRowKeep (V := V) (fastKeeps R row a) a))
    (c' : RowCoins (lookRow (V := V) R (fastJobs a.face row).asked a))
    (hc : RowRel SpentSame _ _ c c') (h : List Fmt.Drawn) (hb : a.base ≤ h.length)
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneRow (lookRowKeep (fastKeeps R row a) a) c ⟨w, h, rowOwn₀⟩ seen ds =
      aloneRow (lookRow R (fastJobs a.face row).asked a) c' ⟨w, h, ()⟩ seen ds :=
  aloneRow_keep _ R _ a w n (fastKeeps_lawful R row a) (fastKeeps_steady R row a w n hR hw) hα c c'
    hc h hb seen ds

/-- **Behind the kept row its own state is `rowOwn₀` again.** Conditional as `sameRounds`, without
hc; hl: as many challenges as the row has moves. -/
theorem sameEnd (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (n : Nat) (hR : R.Steady a n)
    (hw : Ask.Settled n w) (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1)
    (h : List Fmt.Drawn) (hb : a.base ≤ h.length) (ds : List Fmt.Drawn)
    (hl : ds.length = ((lookRowKeep (V := V) (fastKeeps R row a) a).map (·.moves.length)).sum) :
    endRow (lookRowKeep (V := V) (fastKeeps R row a) a) ⟨w, h, rowOwn₀⟩ ds =
      ⟨w, h ++ ds, rowOwn₀⟩ :=
  endRow_keep _ R _ a w n (fastKeeps_lawful R row a) (fastKeeps_steady R row a w n hR hw) hα h hb ds
    hl

/-- **At the reader that a lot seats: the kept row shows the rounds of the earlier row.**
Conditional on hw (the input is settled at a.base), hb (a.base challenges at least are heard in
front of the row) and hc (the coins are read alike). -/
theorem sameRounds_real (row : E → Nat → E) (a : At) (w : Ask) (hw : Ask.Settled a.base w)
    (c : RowCoins (lookRowKeep (V := V) (fastKeeps theReads row a) a))
    (c' : RowCoins (lookRow (V := V) theReads (fastJobs a.face row).asked a))
    (hc : RowRel SpentSame _ _ c c') (h : List Fmt.Drawn) (hb : a.base ≤ h.length)
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneRow (lookRowKeep (fastKeeps theReads row a) a) c ⟨w, h, rowOwn₀⟩ seen ds =
      aloneRow (lookRow theReads (fastJobs a.face row).asked a) c' ⟨w, h, ()⟩ seen ds :=
  sameRounds theReads row a w (pastAlpha a) (steady_real a) (hw.mono (base_le_pastAlpha a))
    (alpha_real a) c c' hc h hb seen ds

/-- **At the reader that a lot seats: behind the kept row its own state is `rowOwn₀` again.**
Conditional on hw, hb and hl. -/
theorem sameEnd_real (row : E → Nat → E) (a : At) (w : Ask) (hw : Ask.Settled a.base w)
    (h : List Fmt.Drawn) (hb : a.base ≤ h.length) (ds : List Fmt.Drawn)
    (hl : ds.length =
      ((lookRowKeep (V := V) (fastKeeps theReads row a) a).map (·.moves.length)).sum) :
    endRow (lookRowKeep (V := V) (fastKeeps theReads row a) a) ⟨w, h, rowOwn₀⟩ ds =
      ⟨w, h ++ ds, rowOwn₀⟩ :=
  sameEnd theReads row a w (pastAlpha a) (steady_real a) (hw.mono (base_le_pastAlpha a))
    (alpha_real a) h hb ds hl

/-- **For all coins of the kept row there are coins of the earlier row that are read alike.** No
hypothesis. Some coins: not said to be a run's: never cited of a run; of a run cite the forms at
lent coins (`lotsSame_lent`, `lotsPlayed_lent`, `lotsWhole_lent`, Honest/K3/Law/Keep/LentLots.lean
[not in this library]).
-/
theorem sameCoins (R : Reads) (row : E → Nat → E) (a : At)
    (c : RowCoins (lookRowKeep (V := V) (fastKeeps R row a) a)) :
    ∃ c' : RowCoins (lookRow (V := V) R (fastJobs a.face row).asked a),
      RowRel SpentSame _ _ c c' :=
  rowRel_keep_total _ R _ a (fastKeeps_lawful R row a) c

/-! ## 3 The rows, seated in a chain's letters -/

/-- **The seated kept row shows the rounds of the seated earlier row**, at the row's letters.
Conditional on `Keeps.Lawful`, `Keeps.SteadyFrom`, hα, hb and hc as `aloneRow_keep`; on hgs:
get (set x y) = y; and on h0: in front of the row get reads `rowOwn₀`. -/
theorem aloneSeat_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (n : Nat)
    (wit : W₁ → Ask) (get : X₁ → RowOwn) (set : X₁ → RowOwn → X₁)
    (hgs : ∀ x y, get (set x y) = y) (t₁ : State W₁ X₁) (h0 : get t₁.own = rowOwn₀)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom (wit t₁.input) n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1)
    (hb : a.base ≤ t₁.heard.length)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts)
    (c' : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts)
    (hc : RowRel SpentSame _ _ (unliftG (fun _ => ()) wit get set (lookRowKeep Kp a) c)
      (unlift (fun _ => ()) wit (lookRow R J a) c'))
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneRow (proverSideOfLookupInChainKeepingTablesAtOneOwner Kp wit get set a).parts c t₁ seen ds =
      aloneRow (proverSideOfLookupInChainAtOneOwner R J wit a).parts c' t₁ seen ds := by
  have e1 := aloneRow_liftG (V := V₁) (fun _ => ()) wit get set hgs (lookRowKeep Kp a) c t₁ seen ds
  have e2 := aloneRow_lift (V := V₁) (X := X₁) (fun _ => ()) wit (lookRow R J a) c' t₁ seen ds
  have e3 : t₁.narrow wit get = ⟨wit t₁.input, t₁.heard, rowOwn₀⟩ := by
    show (⟨wit t₁.input, t₁.heard, get t₁.own⟩ : State Ask RowOwn) = _
    rw [h0]
  rw [e3] at e1
  exact e1.trans ((aloneRow_keep Kp R J a (wit t₁.input) n hL hS hα _ _ hc t₁.heard hb seen
    ds).trans e2.symm)

/-- **Behind the seated kept row the chain's state is as it was**, with the row's challenges heard.
Conditional on `Keeps.Lawful`, `Keeps.SteadyFrom`, hα, hb; on hgs, hss, hsg; on h0; hl: as many
challenges as the row has moves. -/
theorem endSeat_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (n : Nat)
    (wit : W₁ → Ask) (get : X₁ → RowOwn) (set : X₁ → RowOwn → X₁)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x y y', set (set x y) y' = set x y')
    (hsg : ∀ x, set x (get x) = x) (t₁ : State W₁ X₁) (h0 : get t₁.own = rowOwn₀)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom (wit t₁.input) n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1)
    (hb : a.base ≤ t₁.heard.length) (ds : List Fmt.Drawn)
    (hl : ds.length = ((lookRowKeep (V := Unit) Kp a).map (·.moves.length)).sum) :
    endRow (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts t₁ ds =
      ⟨t₁.input, t₁.heard ++ ds, t₁.own⟩ := by
  have hl' : ds.length =
      ((proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts.map (·.moves.length)).sum := by
    show _ = (((lookRowKeep (V := Unit) Kp a).map (Part.lift (fun _ => ()) wit get set)).map
      (·.moves.length)).sum
    rw [lift_moves_sum]
    exact hl
  have e3 : t₁.narrow wit get = ⟨wit t₁.input, t₁.heard, rowOwn₀⟩ := by
    show (⟨wit t₁.input, t₁.heard, get t₁.own⟩ : State Ask RowOwn) = _
    rw [h0]
  have e1 := endRow_lift_own (V := V₁) (fun _ => ()) wit get set hgs hss hsg (lookRowKeep Kp a) t₁
    ds
  rw [e3, endRow_keep Kp R J a (wit t₁.input) n hL hS hα t₁.heard hb ds hl] at e1
  have e4 : set t₁.own rowOwn₀ = t₁.own := by rw [← h0, hsg]
  rw [endRow_eq _ t₁ ds hl']
  exact congrArg (fun z => (⟨t₁.input, t₁.heard ++ ds, z⟩ : State W₁ X₁)) (e1.trans e4)

/-- All coins of a row are those of some coins of the seated row. -/
theorem unlift_onto {V' W' W X : Type} (see : V → V') (wit : W → W') :
    ∀ (ps : List (Part V' W' Unit)) (c₀ : RowCoins ps),
      ∃ c : RowCoins (ps.map (liftU (X := X) see wit)), unlift see wit ps c = c₀
  | [], _ => ⟨(), rfl⟩
  | p :: ps, c₀ => by
    obtain ⟨c₂, h₂⟩ := unlift_onto (X := X) see wit ps c₀.2
    refine ⟨((c₀.1, c₂) : p.Coins × RowCoins (ps.map (liftU (X := X) see wit))), ?_⟩
    show (c₀.1, unlift see wit ps c₂) = c₀
    rw [h₂]
    rfl

/-- **For all coins of the seated kept row there are coins of the seated earlier row that are read
alike.** Conditional on `Keeps.Lawful`. Some coins: not said to be a run's: never cited of a run; of
a run cite the forms at lent coins (`lotsSame_lent`, `lotsPlayed_lent`, `lotsWhole_lent`,
Honest/K3/Law/Keep/LentLots.lean [not in this library]). -/
theorem seatCoins_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (wit : W₁ → Ask)
    (get : X₁ → RowOwn) (set : X₁ → RowOwn → X₁) (hL : Kp.Lawful R J a)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts) :
    ∃ c' : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts,
      RowRel SpentSame _ _ (unliftG (fun _ => ()) wit get set (lookRowKeep Kp a) c)
        (unlift (fun _ => ()) wit (lookRow R J a) c') := by
  obtain ⟨c₀, h₀⟩ := rowRel_keep_total Kp R J a hL
    (unliftG (fun _ => ()) wit get set (lookRowKeep Kp a) c)
  obtain ⟨c', h'⟩ := unlift_onto (V := V₁) (X := X₁) (fun _ => ()) wit (lookRow R J a) c₀
  exact ⟨c', by rw [h']; exact h₀⟩

/-- **At the filling and at the reader that a lot seats: the seated kept row shows the rounds of the
seated earlier row.** Conditional on hw (the input is settled at a.base), hb (a.base challenges at
least are heard in front of the row), hc (the coins are read alike), hgs and h0. -/
theorem sameSeat_real (row : E → Nat → E) (a : At) (wit : W₁ → Ask) (get : X₁ → RowOwn)
    (set : X₁ → RowOwn → X₁) (hgs : ∀ x y, get (set x y) = y) (t₁ : State W₁ X₁)
    (h0 : get t₁.own = rowOwn₀) (hw : Ask.Settled a.base (wit t₁.input))
    (hb : a.base ≤ t₁.heard.length)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) (fastKeeps theReads row a) wit get set a).parts)
    (c' : RowCoins
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) theReads (fastJobs a.face row).asked wit a).parts)
    (hc : RowRel SpentSame _ _
      (unliftG (fun _ => ()) wit get set (lookRowKeep (fastKeeps theReads row a) a) c)
      (unlift (fun _ => ()) wit (lookRow theReads (fastJobs a.face row).asked a) c'))
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneRow (proverSideOfLookupInChainKeepingTablesAtOneOwner (fastKeeps theReads row a) wit get set a).parts c t₁ seen ds =
      aloneRow (proverSideOfLookupInChainAtOneOwner theReads (fastJobs a.face row).asked wit a).parts c' t₁ seen ds :=
  aloneSeat_keep _ theReads _ a (pastAlpha a) wit get set hgs t₁ h0 (fastKeeps_lawful theReads row a)
    (fastKeeps_steady theReads row a _ _ (steady_real a) (hw.mono (base_le_pastAlpha a)))
    (alpha_real a) hb c c' hc seen ds

/-- **The same of the state behind the seated kept row.** Conditional on hw, hb, hl, h0, hgs, hss
and hsg. -/
theorem sameSeatEnd_real (row : E → Nat → E) (a : At) (wit : W₁ → Ask) (get : X₁ → RowOwn)
    (set : X₁ → RowOwn → X₁) (hgs : ∀ x y, get (set x y) = y)
    (hss : ∀ x y y', set (set x y) y' = set x y') (hsg : ∀ x, set x (get x) = x)
    (t₁ : State W₁ X₁) (h0 : get t₁.own = rowOwn₀) (hw : Ask.Settled a.base (wit t₁.input))
    (hb : a.base ≤ t₁.heard.length) (ds : List Fmt.Drawn)
    (hl : ds.length =
      ((lookRowKeep (V := Unit) (fastKeeps theReads row a) a).map (·.moves.length)).sum) :
    endRow (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) (fastKeeps theReads row a) wit get set a).parts t₁ ds =
      ⟨t₁.input, t₁.heard ++ ds, t₁.own⟩ :=
  endSeat_keep _ theReads _ a (pastAlpha a) wit get set hgs hss hsg t₁ h0
    (fastKeeps_lawful theReads row a)
    (fastKeeps_steady theReads row a _ _ (steady_real a) (hw.mono (base_le_pastAlpha a)))
    (alpha_real a) hb ds hl

/-- **The same of the coins.** No hypothesis. Some coins: not said to be a run's: never cited of a
run; of a run cite the forms at lent coins (`lotsSame_lent`, `lotsPlayed_lent`, `lotsWhole_lent`,
Honest/K3/Law/Keep/LentLots.lean [not in this library]). -/
theorem sameSeatCoins (R : Reads) (row : E → Nat → E) (a : At) (wit : W₁ → Ask)
    (get : X₁ → RowOwn) (set : X₁ → RowOwn → X₁)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) (fastKeeps R row a) wit get set a).parts) :
    ∃ c' : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R (fastJobs a.face row).asked wit a).parts,
      RowRel SpentSame _ _ (unliftG (fun _ => ()) wit get set (lookRowKeep (fastKeeps R row a) a) c)
        (unlift (fun _ => ()) wit (lookRow R (fastJobs a.face row).asked a) c') :=
  seatCoins_keep _ R _ a wit get set (fastKeeps_lawful R row a) c

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.faithfulOn_mono
#print axioms ProofFile.Honest.K3.Law.fastKeeps_lawful
#print axioms ProofFile.Honest.K3.Law.fastKeeps_steady
#print axioms ProofFile.Honest.K3.Law.alpha_number
#print axioms ProofFile.Honest.K3.Law.alpha_real
#print axioms ProofFile.Honest.K3.Law.sameRounds
#print axioms ProofFile.Honest.K3.Law.sameEnd
#print axioms ProofFile.Honest.K3.Law.sameRounds_real
#print axioms ProofFile.Honest.K3.Law.sameEnd_real
#print axioms ProofFile.Honest.K3.Law.sameCoins
#print axioms ProofFile.Honest.K3.Law.aloneSeat_keep
#print axioms ProofFile.Honest.K3.Law.endSeat_keep
#print axioms ProofFile.Honest.K3.Law.unlift_onto
#print axioms ProofFile.Honest.K3.Law.seatCoins_keep
#print axioms ProofFile.Honest.K3.Law.sameSeat_real
#print axioms ProofFile.Honest.K3.Law.sameSeatEnd_real
#print axioms ProofFile.Honest.K3.Law.sameSeatCoins
