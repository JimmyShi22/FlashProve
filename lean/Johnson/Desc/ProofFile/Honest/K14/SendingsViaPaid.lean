-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaPaid.lean: "it plays" (Plays, Honest/Thread/Pays.lean)
is proved at a member of a chain's thread WHERE AtVia HOLDS: beside the member stands a CALL of the
shared sending's own part (sendPart, Johnson/Desc/ProofFile/Honest/K1/Part.lean), as
Honest/K14/SendingsVia.lean calls it at the two sendings of the batch's shared rounds; the member
declares the sending's two rounds; the thread's own fields fixed and table at the new trees are laid
as AtVia asks; and the part's public test sendFits accepts. That part returns an error where the job
does not fit its place: so sendFits is a NAMED PREMISE here. NO FILE OF THIS TREE SHOWS A THREAD AT
WHICH AtVia HOLDS, AND NONE CALLS via_Plays.

  via_seed_fits, via_answer_fits   the part's two messages fit the two rounds that a sending of the
                  shared chain declares: the first where the sending's codes are the plan's (hc),
                  the second for a list of as many entries as the sending has answers (hl)
  lately_one      the last challenge heard
  seeds_fit       a challenge that the round "SEND seed" can sample holds just the seeds' elements
  viaTablesAt, viaSaidAt, viaShownAt   what the part sends in its two rounds, as terms: they are
                  total, the call is not: they are what it sends where it returns (via_moves)
  via_moves       what the shared part's two moves return where the job fits its place
  via_plays       **the row plays**, under sendFits and at a first challenge that holds the seeds,
                  at a sub-protocol that has just two rounds which the part's messages fit
  ViaDeclared, via_moved   what is asked of the sub-protocol; the prover's side of the member's
                  step: under sendFits and ViaDeclared, where the half is found at the member's
                  place, chainSteps returns and the challenges fit; and no column is read
  via_declares    where the library's blocks A.P returns eight sub-protocols (hb), the second and
                  the fifth of them declare such rounds, at the two calls
  ViaReads, viaTablesAt_eq, viaPoint_eq, viaU_reads, viaOmega_reads   a job's data reads none but
                  the first n challenges, and nothing of what has been shown (rounds and opened
                  columns); then so do its tables; the two calls' data read none but the challenges
                  up to "LIN point"'s
  viaTable        the function to lay as a thread's table at the call's tree number i
  AtVia, via_Plays   **AtVia gives Plays**: at all coins

What is assumed, in AtVia. fits: sendFits at the job. member: the member declares K1's own two
rounds at the job's parameters, the first with oracle messages that the tables fit. half: the half
at the member's place is the lifted part. fixed, table: as in Honest/K14/SendingsPaid.lean's
TreesLaid, with viaTable. All fields but fits speak of whatever stands at the number b: beyond the
list AtVia is sendFits alone, and Plays is met vacuously. No file of this tree shows a thread at
which AtVia holds; AtVia, via_Plays, viaTable, ViaReads and the four lemmas on what is read are
named by no other file of it. (Files that are not part of this tree had AtVia at a small thread and
at a term of letters2, over any O.)
What is not claimed. That AtVia holds at the shared chain's thread of the IOP as written in Lean.
That sendFits holds at a plan (from the kind's own test on a sending's shapes, at the ride
rideBySort: fits_tie, Honest/K14/TieCounts.lean). Nothing on the frame's other sentences at a member
(Behind, Exchange, RidesPast, Accepted): Exchange at the calls, under premises of its own, is
exchange_via (Honest/K14/SendingsViaShows.lean); among the files that name the calls none states
RidesPast, Accepted or a whole Behind. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsVia
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Block Place OpenedColumn K1.Par K1.seedEntry K1.answerEntry itemOf)
open Desc.K14 (P14 oraclesOf)
open ProofFile.Honest.K13 (chainSteps_one)
open ProofFile.Honest.K1 (sendPart sendFits seedsFit treeTables seedsAt stAt dueR)
open Johnson.Prover.Send (Rows answers)

variable {Bk : ProverCoinCounts} {S Cl W X Pb : Type}

/-- The part's first message fits "SEND seed", where the sending's codes are the plan's (hc). -/
theorem via_seed_fits (P : P14) (Q : K1.Par) (groups : List (List Nat)) (hc : Q.codes = P.codes)
    (Vr : Nat → Rows) :
    ({ vals := [], tables := treeTables Q Vr } : Sending).fits { entry := K1.seedEntry Q }
      (oraclesOf P.codes Q.sent groups) = true := by
  have e : (treeTables Q Vr).map (fun t => (t.logLength, t.words)) =
      (sentTables Q.codes Q.sent fun _ => ⟨fun _ _ => default, fun _ _ => default,
        fun _ _ => default, fun _ _ => default⟩).map fun t => (t.logLength, t.words) := by
    unfold treeTables sentTables VerifiableInference.Desc.K1.Par.trees
    cases VerifiableInference.Desc.Own.treesMade Q.codes Q.sent <;>
      simp [List.map_map, Function.comp_def]
  have h := seed_fits P Q groups hc fun _ => ⟨fun _ _ => default, fun _ _ => default,
    fun _ _ => default, fun _ _ => default⟩
  unfold Sending.fits at h ⊢
  rw [e]
  exact h

/-- The part's second message fits "SEND answer": any list of as many entries as the sending has
answers (hl). -/
theorem via_answer_fits (Q : K1.Par) (l : List Fmt.Ext3) (hl : l.length = Q.answers) :
    ({ vals := l.map fun a => .answer (toE a), tables := [] } : Sending).fits
      { entry := K1.answerEntry Q } [] = true := by
  have h1 : (Fmt.DeclaredRound.items { entry := K1.answerEntry Q }).filter (· != .root) =
      List.replicate Q.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.answerEntry]
  have h2 : ∀ l : List Fmt.Ext3, ((l.map fun a => (Said.answer (toE a))).map fun v =>
      itemOf v.got) = List.replicate l.length .answer := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.length_cons, List.replicate_succ, ih]
      rfl
  unfold Sending.fits
  rw [h1, h2, hl]
  simp

/-- Of a list of challenges that ends in x, lately 1 is [x]: the last challenge heard. -/
theorem lately_one {W' Y : Type} (a : W') (h : List Fmt.Drawn) (x : Fmt.Drawn) (o : Y) :
    ({ input := a, heard := h ++ [x], own := o } : State W' Y).lately 1 = [x] := by
  unfold State.lately
  show (h ++ [x]).drop ((h ++ [x]).length - 1) = [x]
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]

/-- A challenge that "SEND seed" can sample holds just the seeds' elements. -/
theorem seeds_fit (Q : K1.Par) (x : Fmt.Drawn) (h : drawFit { entry := K1.seedEntry Q } x = true) :
    seedsFit Q [x] = true := by
  unfold drawFit at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

/-- **The tables that the call sends, where it returns** (via_moves: where sendFits accepts);
elsewhere the term still has a value and the call returns an error. own: the part's own coins; a:
the input as the part is handed it; h: the challenges heard; sn: what is shown (the frame's Seen).
The literal 0 is the part's round number (SendJob.rows). -/
def viaTablesAt (J : ProofFile.Honest.K1.SendJob Ask Unit) (own : Cs (dueR J.P J.ride)) (a : Ask)
    (h : List Fmt.Drawn) (sn : Seen) : List Table :=
  treeTables J.P (J.rows own sn { input := a, heard := h, own := () } 0)

/-- **What the call says in its second round, where it returns** (via_moves: where sendFits accepts
and the last challenge holds just the seeds' elements): the OOD answers; elsewhere the term still
has a value and the call returns an error. h: the challenges heard, the round's own seeds the last:
at h = [] lately 1 is [] and seedsAt cuts the seeds off the empty list. The words of the messages in
front of the sending are laid as 0 (held (fun _ _ _ => 0)). The literal 1 is the part's round
number. -/
def viaSaidAt (J : ProofFile.Honest.K1.SendJob Ask Unit) (own : Cs (dueR J.P J.ride)) (a : Ask)
    (h : List Fmt.Drawn) (sn : Seen) : List Said :=
  (answers J.P (stAt J.P J.first) J.first
    (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
      (J.rows own sn { input := a, heard := h, own := () } 1))
    (seedsAt J.P (({ input := a, heard := h, own := () } : State Ask Unit).lately 1))).map
      fun y => Said.answer (toE y)

/-- The same as the items in the clear of a round as played: total as viaSaidAt is. -/
def viaShownAt (J : ProofFile.Honest.K1.SendJob Ask Unit) (own : Cs (dueR J.P J.ride)) (a : Ask)
    (h : List Fmt.Drawn) (sn : Seen) : List Fmt.ItemValue :=
  (viaSaidAt J own a h sn).map Said.got

/-- **The shared part's two moves**, where the job fits its place: what they say. -/
theorem via_moves (J : ProofFile.Honest.K1.SendJob Ask Unit) :
    ∃ a b : Move (sendPart J : Part Empty Ask Unit).Coins Ask Unit,
      (sendPart J : Part Empty Ask Unit).moves = [a, b] ∧
      (sendFits J.P J.ride = true → ∀ c s t,
        a.say c s t = .ok { vals := [], tables := treeTables J.P (J.rows c.1 s t 0) }) ∧
      (sendFits J.P J.ride = true → ∀ c s t, seedsFit J.P (t.lately 1) = true →
        b.say c s t = .ok { vals := (answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P (J.rows c.1 s t 1))
          (seedsAt J.P (t.lately 1))).map fun y => .answer (toE y), tables := [] }) := by
  refine ⟨_, _, rfl, fun hf c s t => ?_, fun hf c s t hx => ?_⟩
  · show (if !sendFits J.P J.ride then _ else _) = _
    rw [hf]
    rfl
  · show (if !sendFits J.P J.ride then _ else if !seedsFit J.P (t.lately 1) then _ else _) = _
    rw [hf, hx]
    rfl

/-- **The row plays**, where the job fits its place (hfit), the first challenge holds the seeds
(hx), the sub-protocol's rounds and oracle messages are just the two pairs (d₀, os) and (d₁, [])
(hb), and the part's messages fit them: every list of tables d₀ with os (hf₀), every list of as many
answers as the sending has d₁ (hf₁). -/
theorem via_plays (J : ProofFile.Honest.K1.SendJob Ask Unit) (wit : W → Ask)
    (hfit : sendFits J.P J.ride = true) (b : Block S Cl) (d₀ d₁ : Fmt.DeclaredRound)
    (os : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d₀, os), (d₁, [])])
    (hf₀ : ∀ Vr, ({ vals := [], tables := treeTables J.P Vr } : Sending).fits d₀ os = true)
    (hf₁ : ∀ l : List Fmt.Ext3, l.length = J.P.answers →
      ({ vals := l.map fun a => .answer (toE a), tables := [] } : Sending).fits d₁ [] = true)
    (v : Option Empty) (c : RowCoins [(liftSend wit (sendPart J) : Part Empty W X)])
    (m : Mid W X) (x₀ x₁ : Fmt.Drawn) (hx : seedsFit J.P [x₀] = true) :
    play (({ place := b.place, parts := [liftSend wit (sendPart J)] } :
        Placed Empty W X).steps b v c) [x₀, x₁] [] m =
      .ok ([playedBy b [] ((viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown).map some) x₀,
          playedBy b (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])
            (m.shown.plus [⟨[], x₀⟩])) [] x₁],
        pastOf (pastOf m [] x₀)
          (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀]) (m.shown.plus [⟨[], x₀⟩]))
          x₁) := by
  obtain ⟨a, b', hm, ha, hb'⟩ := via_moves J
  have hm' : (liftSend wit (sendPart J) : Part Empty W X).moves =
      [Move.lift wit (fun _ => ()) (fun x _ => x) a,
        Move.lift wit (fun _ => ()) (fun x _ => x) b'] := by
    show ((sendPart J : Part Empty Ask Unit).moves.map _) = _
    rw [hm]
    rfl
  have hx' : seedsFit J.P
      ((⟨wit m.st.input, m.st.heard ++ [x₀], ()⟩ : State Ask Unit).lately 1) = true := by
    rw [lately_one]
    exact hx
  have hz₀ : (Move.lift wit (fun _ => ()) (fun x _ => x) a : Move _ W X).say c.1
      m.shown m.st =
      .ok ⟨[], viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown⟩ :=
    ha hfit c.1 m.shown ⟨wit m.st.input, m.st.heard, ()⟩
  have hz₁ : b'.say c.1 (m.shown.plus [⟨[], x₀⟩])
      ⟨wit m.st.input, m.st.heard ++ [x₀], ()⟩ =
      .ok ⟨viaSaidAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀]) (m.shown.plus [⟨[], x₀⟩]), []⟩ :=
    hb' hfit c.1 (m.shown.plus [⟨[], x₀⟩]) ⟨wit m.st.input, m.st.heard ++ [x₀], ()⟩ hx'
  have hf : (⟨viaSaidAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀]) (m.shown.plus [⟨[], x₀⟩]),
      []⟩ : Sending).fits d₁ [] = true :=
    hf₁ _ (Johnson.Prover.Send.length_answers _ _ _ _ _)
  have h := two_plays b d₀ d₁ os [] hb (liftSend wit (sendPart J)) _ _ hm' (fun _ _ => rfl)
    (fun w => nomatch w) v c m x₀ x₁ _ _ hz₀ (hf₀ _) hz₁ hf
  exact h

/-- What via_moved asks of a sub-protocol b and a job J of the shared part. -/
structure ViaDeclared (b : Block S Cl) (J : ProofFile.Honest.K1.SendJob Ask Unit) : Prop where
  rounds : ∃ d₀ d₁ os, b.rounds = [d₀, d₁] ∧ b.oracles = [os, []] ∧
    (∀ Vr, ({ vals := [], tables := treeTables J.P Vr } : Sending).fits d₀ os = true) ∧
    (∀ l : List Fmt.Ext3, l.length = J.P.answers →
      ({ vals := l.map fun a => .answer (toE a), tables := [] } : Sending).fits d₁ [] = true) ∧
    (∀ x, drawFit d₀ x = true → seedsFit J.P [x] = true) ∧
    d₀.opens = [] ∧ d₀.stored = [] ∧ d₁.opens = [] ∧ d₁.stored = []

/-- **A call of the shared part: played**, where the job fits its place (hfit), the sub-protocol is
as ViaDeclared asks (hD), the first half found at its place holds the lifted part alone (hf),
chainSteps returns at the member (hl) and the challenges fit its rounds (hd). Then lendRow and play
return, and nothing is read: fillCols returns no column. c: the coins that the book lends the
row. -/
theorem via_moved (J : ProofFile.Honest.K1.SendJob Ask Unit) (wit : W → Ask)
    (hfit : sendFits J.P J.ride = true) (b : Block S Cl) (hD : ViaDeclared b J)
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option Empty}
    {hs : List (Placed Empty W X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftSend wit (sendPart J)] })
    {l : List (Step W X)} (hl : chainSteps B rows look v [b] hs = .ok l) (m : Mid W X)
    (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true) :
    ∃ (x₀ x₁ : Fmt.Drawn) (c : RowCoins [(liftSend wit (sendPart J) : Part Empty W X)]),
      ds = [x₀, x₁] ∧
      lendRow B rows look b.place [(liftSend wit (sendPart J) : Part Empty W X)] 0 = .ok c ∧
      play l ds [] m =
        .ok ([playedBy b [] ((viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown).map some) x₀,
          playedBy b (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])
            (m.shown.plus [⟨[], x₀⟩])) [] x₁],
        pastOf (pastOf m [] x₀)
          (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀]) (m.shown.plus [⟨[], x₀⟩]))
          x₁) ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, hsd, ho₀, hs₀, ho₁, hs₁⟩ := hD.rounds
  obtain ⟨c, hc, rfl⟩ := chainSteps_one hf hl
  obtain ⟨x₀, x₁, rfl, h0, -⟩ := drawsFit_two (d₀ := d₀) (d₁ := d₁) (ds := ds)
    (by rw [← hr]; exact hd)
  refine ⟨x₀, x₁, c, rfl, hc,
    via_plays J wit hfit b d₀ d₁ os (by rw [hr, ho]; rfl) hf₀ hf₁ v c m x₀ x₁ (hsd x₀ h0),
    fun chain ft stored tree => ?_⟩
  rw [hr, reads_none_two chain ft stored tree d₀ d₁ x₀ x₁ ho₀ hs₀ ho₁ hs₁]
  rfl

/-- **The two sendings that the library makes at the parameters A.P declare such rounds**, at their
places, and the shared part's messages at the two calls fit them: b2 and b5 are the second and the
fifth of the eight sub-protocols that blocks A.P returns, where it returns eight (hb). -/
theorem via_declares (A : ViaPub) (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hb : Desc.K14.blocks A.P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ViaDeclared b2 (viaU A) ∧ b2.place = (viaU A).P.place ∧
      ViaDeclared b5 (viaOmega A) ∧ b5.place = (viaOmega A).P.place := by
  obtain ⟨sentU, hU, rfl, rfl⟩ := Desc.K14.Law.two_sendings A.P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have eU : (viaU A).P = Desc.K14.parK1 A.P 2 "o_u and the first mask" sentU := by
    show Desc.K14.parK1 A.P 2 "o_u and the first mask" ((Desc.K14.withU A.P.S).getD #[]) = _
    rw [hU]
    rfl
  refine ⟨⟨_, _, _, rfl, rfl, fun Vr => ?_, fun l hl => ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨_, _, _, rfl, rfl, fun Vr => ?_, fun l hl => ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩,
    rfl⟩
  · rw [eU]
    exact via_seed_fits A.P _ _ rfl Vr
  · rw [eU] at hl
    exact via_answer_fits _ l hl
  · rw [eU]
    exact seeds_fit _ x hx
  · rw [eU]
    rfl
  · exact via_seed_fits A.P _ _ rfl Vr
  · exact via_answer_fits _ l hl
  · exact seeds_fit _ x hx

/-- A job's data reads none but the first n challenges, and nothing of what has been shown (rounds
and opened columns). -/
def ViaReads (J : ProofFile.Honest.K1.SendJob Ask Unit) (n : Nat) : Prop :=
  ∀ a (fr fr' : Front Unit), fr.heard.take n = fr'.heard.take n → J.data a fr = J.data a fr'

/-- Then so do its tables. -/
theorem viaTablesAt_eq {J : ProofFile.Honest.K1.SendJob Ask Unit} {n : Nat} (hJ : ViaReads J n)
    (own : Cs (dueR J.P J.ride)) (a : Ask) (h h' : List Fmt.Drawn) (sn sn' : Seen)
    (e : h.take n = h'.take n) : viaTablesAt J own a h sn = viaTablesAt J own a h' sn' := by
  have e' := hJ a
    { heard := h.take (h.length - 0), own := (), seen := sn.front 0 }
    { heard := h'.take (h'.length - 0), own := (), seen := sn'.front 0 }
    (by
      show (h.take (h.length - 0)).take n = (h'.take (h'.length - 0)).take n
      rw [Nat.sub_zero, Nat.sub_zero, List.take_length, List.take_length]
      exact e)
  show treeTables J.P (ProofFile.Honest.K1.rowsR J.P J.ride (J.data a _) own) =
    treeTables J.P (ProofFile.Honest.K1.rowsR J.P J.ride (J.data a _) own)
  rw [e']

/-- The shared point is read off the first atPoint + 1 challenges. -/
theorem viaPoint_eq (A : ViaPub) (fr fr' : Front Unit)
    (e : fr.heard.take (A.atPoint + 1) = fr'.heard.take (A.atPoint + 1)) :
    viaPoint A fr = viaPoint A fr' := by
  unfold viaPoint
  have k : ∀ l : List Fmt.Drawn, (l.drop A.atPoint).take 1 =
      ((l.take (A.atPoint + 1)).drop A.atPoint).take 1 := fun l => by
    rw [List.drop_take, Nat.add_sub_cancel_left, List.take_take, Nat.min_self]
  rw [k fr.heard, k fr'.heard, e]

/-- The call at "send o_u" reads none but the challenges up to "LIN point"'s. -/
theorem viaU_reads (A : ViaPub) : ViaReads (viaU A) (A.atPoint + 1) := by
  intro a fr fr' e
  show (fun k r j => if k == 0 then vectorData A.P.codes A.P.S.fold.u A.P.S.fold.rowsHigh
    (Desc.K14.Honest.uAtE A.P.S (viaPoint A fr) a.rows) r j else none) = fun k r j => if k == 0 then
    vectorData A.P.codes A.P.S.fold.u A.P.S.fold.rowsHigh
      (Desc.K14.Honest.uAtE A.P.S (viaPoint A fr') a.rows) r j else none
  rw [viaPoint_eq A fr fr' e]

/-- The call at "send o_omega" reads none but the challenges up to "LIN point"'s. -/
theorem viaOmega_reads (A : ViaPub) : ViaReads (viaOmega A) (A.atPoint + 1) := by
  intro a fr fr' e
  show (fun k r j => if k == 0 then vectorData A.P.codes A.P.S.omega A.P.S.omegaRowsHigh
    (Desc.K14.Honest.omegaAtE A.P.S (viaPoint A fr) a.rows) r j else none) = fun k r j =>
    if k == 0 then vectorData A.P.codes A.P.S.omega A.P.S.omegaRowsHigh
      (Desc.K14.Honest.omegaAtE A.P.S (viaPoint A fr') a.rows) r j else none
  rw [viaPoint_eq A fr fr' e]

/-- **The function to lay as a thread's table at the call's tree number i.** pl: the sender's place;
ch: the chain's number. Where the coins are not at hand, or the call has no such tree: a table of
one empty symbol. It reads viaTablesAt at no round shown and no columns handed (Seen.bare []): under
ViaReads the tables read nothing of what has been shown (viaTablesAt_eq). A job whose data read
Seen.opened would be handed the value none here, whatever the run hands; such a job does not meet
ViaReads. -/
def viaTable (J : ProofFile.Honest.K1.SendJob Ask Unit) (wit : W → Ask) (pl : Place) (ch i : Nat)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn) : Place × Table :=
  (pl, match (k.look ch { place := pl, part := 0 }).2.cut { f := 0, e := 0 }
      (dueR J.P J.ride) with
    | some own => (viaTablesAt J own (wit w) h (.bare [])).getD i
        { logLength := 0, words := 0, sym := fun _ j => j.elim0 }
    | none => { logLength := 0, words := 0, sym := fun _ j => j.elim0 })

variable (T : Thread Bk S Cl Empty W X Pb)

/-- **The member number b is a sending, beside a call of the shared part.** i: the number of a new
tree among the member's. -/
structure AtVia (b : Nat) (J : ProofFile.Honest.K1.SendJob Ask Unit) (wit : W → Ask) : Prop where
  fits : sendFits J.P J.ride = true
  member : ∀ blk, T.bs[b]? = some blk → ViaDeclared blk J
  half : ∀ blk, T.bs[b]? = some blk → (T.hs.find? fun h => h.place == blk.place) =
    some { place := blk.place, parts := [liftSend wit (sendPart J)] }
  fixed : ∀ blk, T.bs[b]? = some blk → ∀ i, i < (blk.oracles.flatMap id).length →
    T.fixed (.own (treesTo T.bs b + i)) ≤ T.front + roundsTo T.bs b ∧
      ViaReads J (T.fixed (.own (treesTo T.bs b + i)))
  table : ∀ blk, T.bs[b]? = some blk → ∀ i, i < (blk.oracles.flatMap id).length →
    T.table (.own (treesTo T.bs b + i)) = viaTable J wit blk.place T.chain i

variable {T} {b : Nat} {J : ProofFile.Honest.K1.SendJob Ask Unit} {wit : W → Ask}

/-- **A call of the shared part: it plays, where AtVia holds at b**: at all coins. -/
theorem via_Plays (h : AtVia T b J wit) : Plays T b := by
  intro blk hb k s m E ds l hT hd _ hl
  obtain ⟨x₀, x₁, c, rfl, hc, hp, hcols⟩ :=
    via_moved J wit h.fits blk (h.member blk hb) (h.half blk hb) hl m ds hd
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, -, -, -, -, -, -⟩ := (h.member blk hb).rounds
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hcols _ _ _ _⟩, ?_⟩
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := fresh_mem_own T hb hσ
  obtain ⟨hfx, hrd⟩ := h.fixed blk hb i hi
  have hos : (blk.oracles.flatMap id).length = os.length := by
    rw [ho]
    simp
  have hlen : (viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown).length = os.length := by
    have hf := hf₀ (J.rows c.1.1 m.shown ⟨wit m.st.input, m.st.heard, ()⟩ 0)
    unfold Sending.fits at hf
    rw [Bool.and_eq_true] at hf
    have e := congrArg List.length (beq_iff_eq.1 hf.2)
    rw [List.length_map, List.length_map] at e
    exact e
  have hi' : i < (viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown).length := by
    rw [hlen, ← hos]
    exact hi
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have htree : (E.add
      [playedBy blk [] ((viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown).map some) x₀,
        playedBy blk (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])
          (m.shown.plus [⟨[], x₀⟩])) [] x₁]).tree (.own (treesTo T.bs b + i)) =
      some (blk.place, (viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown)[i]) := by
    rw [← hsent, add_own]
    simp [tablesOf, playedBy, hi']
  have hheard : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  have hown : (k.look T.chain ⟨blk.place, 0⟩).2.cut ⟨0, 0⟩ (dueR J.P J.ride) = some c.1.1 :=
    lendRow_own (p := (liftSend wit (sendPart J) : Part Empty W X)) hc
  have htab : T.tableAt (.own (treesTo T.bs b + i)) k
      (pastOf (pastOf m [] x₀) (viaShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])
        (m.shown.plus [⟨[], x₀⟩])) x₁) =
      (blk.place, (viaTablesAt J c.1.1 (wit m.st.input) m.st.heard m.shown)[i]) := by
    unfold Thread.tableAt
    rw [h.table blk hb i hi]
    show viaTable J wit blk.place T.chain i k m.st.input
      (((m.st.heard ++ [x₀]) ++ [x₁]).take _) = _
    rw [List.append_assoc, List.take_append_of_le_length (by rw [hheard]; exact hfx)]
    unfold viaTable
    rw [hown]
    show (blk.place,
        (viaTablesAt J c.1.1 (wit m.st.input) (m.st.heard.take _) (.bare [])).getD i _) = _
    rw [viaTablesAt_eq hrd c.1.1 (wit m.st.input) (m.st.heard.take _) m.st.heard (.bare []) m.shown
      (by rw [List.take_take, Nat.min_self]), List.getD_eq_getElem _ _ hi']
  unfold Thread.handAt
  rw [htree, htab]
  simp [Table.same]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.via_seed_fits
#print axioms ProofFile.Honest.K14.via_answer_fits
#print axioms ProofFile.Honest.K14.lately_one
#print axioms ProofFile.Honest.K14.seeds_fit
#print axioms ProofFile.Honest.K14.via_moves
#print axioms ProofFile.Honest.K14.via_plays
#print axioms ProofFile.Honest.K14.via_moved
#print axioms ProofFile.Honest.K14.via_declares
#print axioms ProofFile.Honest.K14.viaTablesAt_eq
#print axioms ProofFile.Honest.K14.viaPoint_eq
#print axioms ProofFile.Honest.K14.viaU_reads
#print axioms ProofFile.Honest.K14.viaOmega_reads
#print axioms ProofFile.Honest.K14.via_Plays
#print axioms ProofFile.Honest.K14.viaTablesAt
#print axioms ProofFile.Honest.K14.viaSaidAt
#print axioms ProofFile.Honest.K14.viaShownAt
#print axioms ProofFile.Honest.K14.ViaDeclared
#print axioms ProofFile.Honest.K14.ViaReads
#print axioms ProofFile.Honest.K14.viaTable
#print axioms ProofFile.Honest.K14.AtVia
