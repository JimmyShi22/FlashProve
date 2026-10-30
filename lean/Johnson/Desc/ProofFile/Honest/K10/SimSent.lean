-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimSent.lean: the closing of a segment (K10): Honest/K10/Sim.lean's (3b), and with it
(3c) and (2), proved at the total form (tot = true), at every job. The spender's half alone, as Sim.lean's head says.

What is proved. At every job J, under the statement's own premises (the place's `closePlan`; challenges that the rounds
can draw; a third, `closeOn true`, asks nothing) and no other: what the literal member `closeAt true J` shows, played by
the frame's own `play`, is the simulator's form's laying of `runSent` of the run plus what "FOLD epsilon" drew times
values that are named in front of the run. No premise on a table's size. Of `closePlan`, 1 ≤ k is spent; h ≤ k nowhere.

  `drawFit_elems`, `draws_ones`, `close_draws`   challenges that the part's rounds can draw: 2 + k of them, each of
                   one element
  `askZero`, `askWith`, `askOr_is`   the closing's data at the run of zeros, or nothing (where `closeAsk` refuses, or
                   no statement is at hand); the data that the fold's words are handed: these tables, or empty ones,
                   and the run; what a move of the total form is handed, at a stand that is written out
  `steps_get`, `stopBoth_none`, `standAt`, `standAt_zero`, `standAt_succ`, `fits_of`, `lately_is`, `get_round`   the
                   part's rounds by number; where the play stands in front of round i, written out; a message of n
                   elements has the stated shape
  `saysAt`, `says_tables`, **`plays_is`**   what round i says; the part is at no fault, at any stand, any coins and any
                   such challenges, and says just that (no move of this form can refuse: `askOr true` makes nothing of
                   every refusal: to that extent "no fault" is met for nothing, as Sim.lean's head says; shown beside
                   it: no stop; each message has the round's declared shape)
  `shown_aux`, `shown_plain`   rounds without a table show their items and no column, whatever positions are asked
  `read_run`, `shareAt`, `sigma_val`, `round_val`, `says_lay`   the values, by Honest/K10/SimWords.lean. `shareAt`:
                   the tables' share: of the job, `askZero`'s value and what the rounds "FOLD round" drew: it is
                   handed neither the run nor what "FOLD epsilon" drew
  **`sent_is`**      `CloseSentIs S Cl V X Pb true J`
    `close_oneToOne`   `CloseOneToOne S Cl V X Pb true J`: by `oneToOne_of` (Honest/K10/SimLaws.lean) and
                   `run_one_to_one` (SimMap.lean)
  **`close_exact`**  `CloseExact S Cl V X Pb true J`: by `exact_of_sentIs` (Honest/K10/SimLaws.lean)
  `seated_sentIs`, `seated_oneToOne`, `seated_exact`, `seated_fresh`   Honest/K10/SimSeat.lean's four at the seated
                   job: instances. `seated_fresh` is without content, as `close_fresh`: it is not the `fresh` that the
                   run's owners owe

Which theorem carries what. `sent_is` says what `CloseSentIs` says and no more: there the values q are bound behind the
challenges, behind ∃, and in front of the part's coins: that order of the binders is all that it says of what q can hang
on: it does not say that they do not hang on what "FOLD epsilon" drew. That, and which values they are, is `says_lay`'s:
it names `shareAt`, at a letter for the closing's data; which value stands for that letter (`askZero`: of the input,
what was shown and heard in front, "BAT"'s challenge and the carried runs) is `plays_is`'s premise: no one statement
holds the whole.

Limits. By type the total form's default can hang on more than what is public, shown or heard. `CloseAskPublic` (and, at
the seated job, `SeatedAskPublic`) says that it does not: a definition: no statement of this library concludes it, and
none takes it as a premise. What this part sends has the simulator's law either way (`close_exact`, `close_fresh`). The
lot that lays the cured part: `seatLotT` (Honest/K10/SeatLotT.lean), which no definition and no maker of a description
calls. `seatLotC` (Honest/K10/SeatLotC.lean) lays the same part at the closings alone, and `closeLotAt`
(Honest/AtPureWiderK10.lean) lays its halves in a filling. At tot = true alone: of the other form nothing is proved
here. The statements bind a face of the frame: at a job typed at no face's input they have no face to bind. Where
`closeAsk` refuses or yields nothing the tables are empty and the share is what the words make of empty tables: the law
holds there too; whether that end is taken hangs on what `closeAsk` reads, of which (4'') speaks, and with it the law
that the statement in front of "BAT" is one, and this file does not. That the premises can be met together is shown by
no theorem here. The challenges are fixed. Nothing is said of what a run of the protocol shows of these coins elsewhere.
Nothing ties the run's order here to the sender's table. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimPlay
import Johnson.Desc.ProofFile.Honest.K10.SimWords
import Johnson.Desc.ProofFile.Honest.K10.SimLaws
import Johnson.Desc.ProofFile.Honest.K10.SimSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE)
open OnBytes.Slice (toE ofE toE_ofE)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par entries)

variable {S Cl V W X Pb : Type}

/-! ## Challenges that the rounds can draw -/

theorem drawFit_elems {z : Fmt.DeclaredRound} {d : Fmt.Drawn} (h : drawFit z d = true) :
    d.elems.length = z.entry.drawE := by
  simp only [drawFit, Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1.1.1.1.1.1.1

theorem draws_ones : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit zs ds = true →
    (∀ z ∈ zs, z.entry.drawE = 1) → ds.length = zs.length ∧ ∀ d ∈ ds, d.elems.length = 1
  | [], [], _, _ => ⟨rfl, fun d hd => by cases hd⟩
  | [], _ :: _, h, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _ => by simp [drawsFit] at h
  | z :: zs, d :: ds, h, h1 => by
      rw [drawsFit, Bool.and_eq_true] at h
      obtain ⟨hl, ha⟩ := draws_ones zs ds h.2 fun z' hz => h1 z' (List.mem_cons_of_mem _ hz)
      refine ⟨by rw [List.length_cons, List.length_cons, hl], fun d' hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · rw [drawFit_elems h.1, h1 z List.mem_cons_self]
      · exact ha d' hd

theorem close_draws (P : Par) (ds : List Fmt.Drawn)
    (h : drawsFit ((closeRounds P).map (·.1)) ds = true) :
    ∃ d0 d1 gs, ds = d0 :: d1 :: gs ∧ gs.length = P.k ∧ ∀ d ∈ ds, d.elems.length = 1 := by
  obtain ⟨hl, ha⟩ := draws_ones _ ds h (by
    intro z hz
    simp only [closeRounds, entries, List.map_cons, List.map_map, List.mem_cons, List.mem_map,
      List.mem_replicate] at hz
    rcases hz with rfl | rfl | ⟨e, ⟨_, rfl⟩, rfl⟩ <;> rfl)
  have hl' : ds.length = 2 + P.k := by
    rw [hl]
    simp only [closeRounds, entries, List.length_map, List.length_cons, List.length_replicate]
    omega
  match ds, hl', ha with
  | d0 :: d1 :: gs, hl', ha =>
    exact ⟨d0, d1, gs, rfl, by simp only [List.length_cons] at hl'; omega, ha⟩

/-! ## What a move of the total form is handed, at a stand that is written out -/

/-- The closing's data at the run of zeros, or nothing: named in front of the run. -/
def askZero (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) : Option FoldAsk :=
  (closeAsk J w sn h0 d0 (fun _ => zeroE) ca).toOption.join

/-- The data that the fold's words are handed: the tables of `askZero`, or empty ones; and the run. At data A the k and
h are the place's, and A's own k, h and run are dropped (at what `closeAsk` yields, k and h are the place's anyway:
`ask_run`, SimPlay.lean; but o is a letter here). -/
def askWith (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E) : FoldAsk :=
  match o with
  | some A => { k := J.pub.par.k, h := J.pub.par.h, c := A.c, d := A.d, m := A.m, mu := A.mu,
                keptV := A.keptV, w := u }
  | none => bareAsk J.pub.par u

theorem askOr_is (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t : State W X)
    (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn) (gs : List Fmt.Drawn) (r0 rs : List Fmt.RoundView)
    (ht : t.heard = h0 ++ d0 :: gs) (hn : gs.length = n) (hs : s.rounds = r0 ++ rs)
    (hr : rs.length = n + 1) (hg : ∀ g ∈ gs, g.elems.length = 1) :
    askOr true J n c s t =
      .ok ((askZero J t.input ⟨r0, s.opened⟩ h0 d0 c.2.2).map fun A =>
        (askWith J (some A) (spentRun J c), drawnE gs)) := by
  unfold askOr askZero
  rw [if_pos rfl, askAt_is J n c s t h0 d0 gs r0 rs ht hn hs hr hg,
    ask_run J t.input ⟨r0, s.opened⟩ h0 d0 (spentRun J c) (fun _ => zeroE) c.2.2]
  cases closeAsk J t.input ⟨r0, s.opened⟩ h0 d0 (fun _ => zeroE) c.2.2 with
  | error e => rfl
  | ok o => cases o <;> rfl

/-! ## The part's rounds, by number -/

theorem steps_get (p : Part V W X) (name : String) (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle))
    (v : Option V) (c : p.Coins) (i : Nat) (s : Step W X) (h : (p.steps name a rs v c)[i]? = some s) :
    ∃ r mv, rs[i]? = some r ∧ p.moves[i]? = some mv ∧
      s = ⟨name, a, r.1, r.2, p.bad, fun f o => v.bind fun w => p.hid w f o, i,
        i + 1 == p.moves.length, some ⟨fun _ => mv.say c, mv.hand⟩⟩ := by
  unfold Part.steps at h
  rw [List.getElem?_map, List.getElem?_zipIdx] at h
  cases hz : (rs.zip p.moves)[i]? with
  | none =>
    rw [hz] at h
    cases h
  | some z =>
    rw [hz] at h
    obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 hz
    refine ⟨z.1, z.2, h1, h2, ?_⟩
    have := Option.some.inj h
    rw [← this]
    simp only [Nat.zero_add]

theorem stopBoth_none (n m : Nat) (f o : List Fmt.Drawn) :
    stopBoth n m (fun _ _ => none) (fun _ _ => none) f o = none := by
  unfold stopBoth
  split <;> split <;> rfl

/-- Where the play stands in front of round i, written out. Where ds has no number j the empty challenge is laid: read
only at an i beyond the list's length. -/
def standAt (m : Mid W X) (ds : List Fmt.Drawn) (Z : Nat → Sending) (i : Nat) : Mid W X :=
  ⟨⟨m.st.input, m.st.heard ++ ds.take i, m.st.own⟩, m.loc ++ ds.take i,
    m.seen ++ (List.range i).map fun j => ⟨(Z j).vals.map Said.got, ds.getD j ⟨[], [], [], none⟩⟩, m.opened⟩

theorem standAt_zero (m : Mid W X) (ds : List Fmt.Drawn) (Z : Nat → Sending) : standAt m ds Z 0 = m := by
  unfold standAt
  simp only [List.take_zero, List.append_nil, List.range_zero, List.map_nil]

theorem standAt_succ (m : Mid W X) (ds : List Fmt.Drawn) (Z : Nat → Sending) (i : Nat) (d : Fmt.Drawn)
    (hd : ds[i]? = some d) (mv : Move Unit W X) (hh : ∀ t, mv.hand t = t.own) :
    standAt m ds Z (i + 1) = (standAt m ds Z i).after mv ((Z i).vals.map Said.got) d := by
  have e1 : ds.take (i + 1) = ds.take i ++ [d] := by rw [List.take_add_one, hd]; rfl
  have e2 : ds.getD i ⟨[], [], [], none⟩ = d := by rw [List.getD_eq_getElem?_getD, hd]; rfl
  unfold standAt Mid.after State.hears
  simp only [hh, e1, List.range_succ, List.map_append, List.map_cons, List.map_nil, e2,
    List.append_assoc]

/-- A message of n elements and no table has the shape of an entry with 24 n bytes, no root and no answer. -/
theorem fits_of (z : Sending) (e : Fmt.Entry) (n : Nat)
    (hv : z.vals.map (fun v => itemOf v.got) = List.replicate n .e) (ht : z.tables = [])
    (ha : e.answers = 0) (hr : e.roots = 0) (hm : e.msg = 24 * n) :
    z.fits { entry := e } [] = true := by
  unfold Sending.fits Fmt.DeclaredRound.items Fmt.Entry.cut
  rw [hv, ht, ha, hr, hm]
  simp

theorem lately_is (t : State W X) (h0 gs : List Fmt.Drawn) (n : Nat) (ht : t.heard = h0 ++ gs)
    (hn : gs.length = n) : t.lately n = gs := by
  unfold State.lately
  have : t.heard.length - n = h0.length := by
    rw [ht, List.length_append, hn]
    omega
  rw [this, ht, List.drop_left]

/-- **What round i of the part says**: o: the closing's data at the run of zeros, or nothing; u: the run; d1: what
"FOLD epsilon" drew; gs: what the rounds "FOLD round" drew. It yields a message beyond the 2 + k rounds too. -/
def saysAt (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E) (d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) : Nat → Sending
  | 0 => ⟨[], []⟩
  | 1 => sayE [foldWords.sigma (askWith J o u)]
  | j + 2 =>
    let g := drawnE (d1 :: gs.take j)
    let q := foldWords.round (askWith J o u) (g.headD zeroE) (g.drop 1)
    sayE [q.1, q.2]

theorem get_round {α β : Type} (a₀ a₁ : β) (f : α → β) (g : Nat → α) (k j : Nat) (hj : j < k) (x : β)
    (h : (a₀ :: a₁ :: ((List.range k).map g).map f)[j + 2]? = some x) : f (g j) = x := by
  rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_map, List.getElem?_map,
    List.getElem?_range hj] at h
  exact Option.some.inj h

theorem says_tables (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E)
    (d1 : Fmt.Drawn) (gs : List Fmt.Drawn) : ∀ i, (saysAt J o u d1 gs i).tables = []
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- **The total form's part, played by the frame's own `play`, is at no fault, and says `saysAt`.** No move of this form
can refuse: to that extent "no fault" is met for nothing (this file's head). -/
theorem plays_is (J : CloseJob W) (name : String) (a : Addr) (v : Option V)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins) (m : Mid W X)
    (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn) (hk : gs.length = J.pub.par.k)
    (h1 : ∀ d ∈ d0 :: d1 :: gs, d.elems.length = 1) (o : Option FoldAsk)
    (ho : o = askZero J m.st.input m.shown m.st.heard d0 (handSnd c).2.2) :
    ∃ y, play ((closePart (foldShellT true J foldWords)).steps name a (closeRounds J.pub.par) v c)
        (d0 :: d1 :: gs) [] m = .ok y ∧
      y.1.map (fun p => (p.vals, p.tables)) =
        (List.range (2 + J.pub.par.k)).map fun i =>
          ((saysAt J o (spentRun J (handSnd c)) d1 gs i).vals.map Said.got, []) := by
  have hlen : ((closePart (foldShellT true J foldWords)).steps name a (closeRounds J.pub.par) v
      c).length = (d0 :: d1 :: gs).length := by
    unfold Part.steps
    rw [List.length_map, List.length_zipIdx, List.length_zip, moves_len, Nat.min_self]
    simp only [closeRounds, entries, List.length_map, List.length_cons, List.length_replicate, hk]
  obtain ⟨y, hy, e⟩ := play_all _ (d0 :: d1 :: gs)
    (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs))
    (saysAt J o (spentRun J (handSnd c)) d1 gs) hlen (by
    intro i s d hs hd
    obtain ⟨r, mv, hr, hm, rfl⟩ := steps_get _ name a _ v c i s hs
    refine ⟨fun f o => stopBoth_none _ _ f o, fun f o => ?_, ⟨fun _ => mv.say c, mv.hand⟩, rfl, ?_⟩
    · cases v with
      | none => rfl
      | some w => exact stopBoth_none _ _ f o
    match i, hr, hm, hd with
    | 0, hr, hm, hd =>
      obtain rfl := Option.some.inj hr
      obtain rfl := Option.some.inj hm
      exact ⟨rfl, fits_of _ _ 0 rfl rfl rfl rfl rfl, standAt_succ _ _ _ 0 d hd _ fun _ => rfl⟩
    | 1, hr, hm, hd =>
      obtain rfl := Option.some.inj hr
      obtain rfl := Option.some.inj hm
      refine ⟨?_, fits_of _ _ 1 rfl rfl rfl rfl rfl, standAt_succ _ _ _ 1 d hd _ fun _ => rfl⟩
      have key : askOr true J 0 (handSnd c)
          (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs) 1).shown
          (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs) 1).st =
          .ok (o.map fun A => (askWith J (some A) (spentRun J (handSnd c)), drawnE [])) := by
        rw [ho]
        exact askOr_is J 0 (handSnd c) _ _ m.st.heard d0 [] m.seen _ rfl rfl rfl rfl
          (fun g hg => by cases hg)
      simp only [Move.recoin]
      refine (congrArg (Except.map _) key).trans ?_
      cases o <;> rfl
    | j + 2, hr, hm, hd =>
      have hd' : gs[j]? = some d := hd
      obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.1 hd'
      rw [hk] at hj
      have hr' := hr
      simp only [closeRounds, entries, List.map_cons, List.getElem?_cons_succ, List.getElem?_map,
        List.getElem?_replicate, hj, if_true, Option.map_some] at hr'
      obtain rfl := Option.some.inj hr'
      obtain rfl := get_round _ _ _ _ J.pub.par.k j hj mv hm
      have hgl : (d1 :: gs.take j).length = j + 1 := by
        rw [List.length_cons, List.length_take, hk, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hh : (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs) (j + 2)).st.heard =
          m.st.heard ++ d0 :: (d1 :: gs.take j) := rfl
      refine ⟨?_, fits_of _ _ 2 rfl rfl rfl rfl rfl, standAt_succ _ _ _ (j + 2) d hd _ fun _ => rfl⟩
      have key : askOr true J (j + 1) (handSnd c)
          (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs) (j + 2)).shown
          (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs) (j + 2)).st =
          .ok (o.map fun A =>
            (askWith J (some A) (spentRun J (handSnd c)), drawnE (d1 :: gs.take j))) := by
        rw [ho]
        exact askOr_is J (j + 1) (handSnd c) _ _ m.st.heard d0 (d1 :: gs.take j) m.seen _ hh hgl rfl
          (by rw [List.length_map, List.length_range])
          (fun g hg => h1 g (by
            rcases List.mem_cons.1 hg with rfl | hg
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hg))))
      have hlate : (standAt m (d0 :: d1 :: gs) (saysAt J o (spentRun J (handSnd c)) d1 gs)
          (j + 2)).st.lately (j + 1) = d1 :: gs.take j :=
        lately_is _ (m.st.heard ++ [d0]) _ _ (by rw [hh]; simp) hgl
      simp only [Move.recoin]
      rw [hlate]
      refine (congrArg (Except.map _) key).trans ?_
      cases o <;> rfl)
  rw [standAt_zero] at hy
  refine ⟨y, hy, ?_⟩
  have hl2 : (d0 :: d1 :: gs).length = 2 + J.pub.par.k := by
    rw [List.length_cons, List.length_cons, hk]
    omega
  rw [e, hlen, hl2]
  exact List.map_congr_left fun i _ => by rw [says_tables]; rfl

/-! ## What is shown -/

theorem shown_aux (asks : List (List (List Nat))) : ∀ (ps : List Played) (n : Nat),
    (∀ p ∈ ps, p.tables = []) →
    (ps.zipIdx n).map (fun x => (⟨x.1.vals, x.1.tables.zipIdx.map fun y =>
      match y.1 with
      | some t => ((((asks[x.2]?).getD [])[y.2]?).getD []).map fun p => (p, t.col p)
      | none => []⟩ : Shown)) = ps.map fun p => ⟨p.vals, []⟩
  | [], _, _ => rfl
  | p :: ps, n, h => by
      rw [List.zipIdx_cons, List.map_cons, List.map_cons,
        shown_aux asks ps (n + 1) fun q hq => h q (List.mem_cons_of_mem _ hq)]
      refine congrArg (· :: _) ?_
      show (⟨p.vals, p.tables.zipIdx.map _⟩ : Shown) = ⟨p.vals, []⟩
      rw [h p List.mem_cons_self]
      rfl

/-- Rounds without a table show their items and no column, whatever positions are asked. -/
theorem shown_plain (ps : List Played) (asks : List (List (List Nat))) (L : List (List Fmt.ItemValue))
    (h : ps.map (fun p => (p.vals, p.tables)) = L.map fun v => (v, [])) :
    shownOf ps asks = L.map fun v => ⟨v, []⟩ := by
  have ht : ∀ p ∈ ps, p.tables = [] := by
    intro p hp
    have h2 : (p.vals, p.tables) ∈ ps.map fun p => (p.vals, p.tables) :=
      List.mem_map.2 ⟨p, hp, rfl⟩
    rw [h] at h2
    obtain ⟨v, _, e⟩ := List.mem_map.1 h2
    exact (congrArg Prod.snd e).symm
  have hv : ps.map (·.vals) = L := by
    have h3 := congrArg (List.map Prod.fst) h
    rw [List.map_map, List.map_map] at h3
    exact h3.trans ((List.map_congr_left fun _ _ => rfl).trans (List.map_id L))
  refine (shown_aux asks ps 0 ht).trans ?_
  rw [← hv, List.map_map]
  rfl

/-! ## The values -/

/-- The run as the part reads it, read back in the field, is the run. -/
theorem read_run (J : CloseJob W)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) :
    Wd.runW J.pub.par.k (fun i => (spentRun J c i).triple) =
      atN (let u : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit := c.2.1; u.1.e) := by
  funext n
  unfold Wd.runW atN
  split
  · exact toE_ofE _
  · rfl

/-- The tables' share of what is sent, by number: named in front of the run and of what "FOLD epsilon" drew. -/
noncomputable def shareAt (J : CloseJob W) (o : Option FoldAsk) (gs : List Fmt.Drawn) :
    Fin (2 * J.pub.par.k + 1) → Cb.Gl.E := fun i =>
  let A := askWith J o fun _ => zeroE
  match i.1 with
  | 0 => 0
  | n + 1 =>
    if n % 2 = 0 then
      Wd.tab0 J.pub.par.k J.pub.par.h (A.c.map (·.triple)) (A.d.map (·.triple)) (A.m.map (·.triple))
        (A.mu.map (·.triple)) A.keptV.triple ((drawnE (gs.take (n / 2))).map (·.triple))
    else
      Wd.tab2 J.pub.par.k J.pub.par.h (A.c.map (·.triple)) (A.d.map (·.triple)) (A.m.map (·.triple))
        (A.mu.map (·.triple)) ((drawnE (gs.take (n / 2))).map (·.triple))

theorem sigma_val (J : CloseJob W) (hk : 1 ≤ J.pub.par.k) (o : Option FoldAsk)
    (u : Fin (2 * J.pub.par.k + 1) → E) :
    toE (foldWords.sigma (askWith J o u)).triple =
      runSentN J.pub.par.k (Wd.runW J.pub.par.k fun i => (u i).triple) 0 := by
  have e : (foldWords.sigma (askWith J o u)).triple =
      Johnson.Prover.Link.foldSigmaW J.pub.par.k fun i => (u i).triple := by cases o <;> rfl
  rw [e]
  exact Wd.sigma_is _ _ hk

theorem round_val (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E)
    (x : Fmt.Ext3) (gs : List Fmt.Drawn) (j : Nat) (hj : j < J.pub.par.k) (hg : gs.length = J.pub.par.k) :
    toE (foldWords.round (askWith J o u) (E.ofTriple x) (drawnE (gs.take j))).1.triple =
        runSentN J.pub.par.k (Wd.runW J.pub.par.k fun i => (u i).triple) (2 * j + 1) +
          toE x * shareAt J o gs ⟨2 * j + 1, by omega⟩ ∧
      toE (foldWords.round (askWith J o u) (E.ofTriple x) (drawnE (gs.take j))).2.triple =
        runSentN J.pub.par.k (Wd.runW J.pub.par.k fun i => (u i).triple) (2 * j + 1 + 1) +
          toE x * shareAt J o gs ⟨2 * j + 1 + 1, by omega⟩ := by
  have hl : ((drawnE (gs.take j)).map (·.triple)).length = j := by
    unfold drawnE
    rw [List.length_map, List.length_map, List.length_take, hg, Nat.min_eq_left (Nat.le_of_lt hj)]
  have h0 : (2 * j) % 2 = 0 := by omega
  have h1 : (2 * j) / 2 = j := by omega
  have h2 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have h3 : (2 * j + 1) / 2 = j := by omega
  have key := Wd.round_is J.pub.par.k (fun i => (u i).triple) J.pub.par.h
    ((askWith J o fun _ => zeroE).c.map (·.triple)) ((askWith J o fun _ => zeroE).d.map (·.triple))
    ((askWith J o fun _ => zeroE).m.map (·.triple)) ((askWith J o fun _ => zeroE).mu.map (·.triple))
    (askWith J o fun _ => zeroE).keptV.triple x ((drawnE (gs.take j)).map (·.triple))
    (by rw [hl]; exact hj)
  rw [hl] at key
  constructor
  · show _ = _ + toE x * (if (2 * j) % 2 = 0 then _ else _)
    rw [if_pos h0, h1, ← key.1]
    cases o <;> rfl
  · show _ = _ + toE x * (if (2 * j + 1) % 2 = 0 then _ else _)
    rw [if_neg h2, h3, ← key.2]
    cases o <;> rfl

/-- The list of what the rounds say, against the simulator's form's laying. -/
theorem says_lay (J : CloseJob W) (hk1 : 1 ≤ J.pub.par.k) (o : Option FoldAsk)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (d0 d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (hk : gs.length = J.pub.par.k) (x : Fmt.Ext3) (hx : d1.elems = [x])
    (r : Fin (2 * J.pub.par.k + 1) → Cb.Gl.E)
    (hr : r = (let u : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit := c.2.1; u.1.e)) :
    ((List.range (2 + J.pub.par.k)).map fun i =>
      (⟨(saysAt J o (spentRun J c) d1 gs i).vals.map Said.got, []⟩ : Shown)) =
      layF J.pub.par.k fun i =>
        runSent J.pub.par.k r i + epsOf (d0 :: d1 :: gs) * shareAt J o gs i := by
  have he : epsOf (d0 :: d1 :: gs) = toE x := by
    unfold epsOf
    simp [hx]
  have hR : Wd.runW J.pub.par.k (fun i => (spentRun J c i).triple) = atN r := by
    rw [hr]
    exact read_run J c
  apply List.ext_getElem?
  intro i
  match i with
  | 0 =>
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  | 1 =>
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    have v1 : toE (foldWords.sigma (askWith J o (spentRun J c))).triple =
        runSent J.pub.par.k r ⟨0, by omega⟩ +
          epsOf (d0 :: d1 :: gs) * shareAt J o gs ⟨0, by omega⟩ := by
      rw [sigma_val J hk1, hR]
      show _ = runSentN J.pub.par.k (atN r) 0 + epsOf (d0 :: d1 :: gs) * 0
      rw [mul_zero, add_zero]
    show some (⟨[.e (ofE (toE (foldWords.sigma (askWith J o (spentRun J c))).triple))], []⟩ : Shown) =
      some ⟨[.e (ofE (runSent J.pub.par.k r ⟨0, by omega⟩ +
        epsOf (d0 :: d1 :: gs) * shareAt J o gs ⟨0, by omega⟩))], []⟩
    rw [v1]
  | j + 2 =>
    by_cases hj : j < J.pub.par.k
    · rw [List.getElem?_map, List.getElem?_range (by omega)]
      unfold layF
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_ofFn, dif_pos hj]
      obtain ⟨v1, v2⟩ := round_val J o (spentRun J c) x gs j hj hk
      rw [hR, ← he] at v1 v2
      have hd : drawnE (d1 :: gs.take j) = E.ofTriple x :: drawnE (gs.take j) := by
        unfold drawnE
        rw [List.map_cons, hx]
        rfl
      have w1 : (⟨1 + 2 * j, by omega⟩ : Fin (2 * J.pub.par.k + 1)) = ⟨2 * j + 1, by omega⟩ :=
        Fin.ext (by show 1 + 2 * j = 2 * j + 1; omega)
      have w2 : (⟨2 + 2 * j, by omega⟩ : Fin (2 * J.pub.par.k + 1)) = ⟨2 * j + 1 + 1, by omega⟩ :=
        Fin.ext (by show 2 + 2 * j = 2 * j + 1 + 1; omega)
      show some (⟨[.e (ofE (toE (foldWords.round (askWith J o (spentRun J c))
            ((drawnE (d1 :: gs.take j)).headD zeroE) ((drawnE (d1 :: gs.take j)).drop 1)).1.triple)),
          .e (ofE (toE (foldWords.round (askWith J o (spentRun J c))
            ((drawnE (d1 :: gs.take j)).headD zeroE) ((drawnE (d1 :: gs.take j)).drop 1)).2.triple))],
          []⟩ : Shown) =
        some ⟨[.e (ofE (runSent J.pub.par.k r ⟨1 + 2 * j, by omega⟩ +
            epsOf (d0 :: d1 :: gs) * shareAt J o gs ⟨1 + 2 * j, by omega⟩)),
          .e (ofE (runSent J.pub.par.k r ⟨2 + 2 * j, by omega⟩ +
            epsOf (d0 :: d1 :: gs) * shareAt J o gs ⟨2 + 2 * j, by omega⟩))], []⟩
      rw [hd, w1, w2]
      show some (⟨[.e (ofE (toE (foldWords.round (askWith J o (spentRun J c)) (E.ofTriple x)
            (drawnE (gs.take j))).1.triple)),
          .e (ofE (toE (foldWords.round (askWith J o (spentRun J c)) (E.ofTriple x)
            (drawnE (gs.take j))).2.triple))], []⟩ : Shown) = _
      rw [v1, v2]
      rfl
    · rw [List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]
      unfold layF
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_ofFn, dif_neg hj]

/-- **(3b) at the total form, at every job.** -/
theorem sent_is (J : CloseJob W) : CloseSentIs S Cl V X Pb true J := by
  intro hp σ φ ca m front ds asks _ hd
  obtain ⟨d0, d1, gs, rfl, hk, h1⟩ := close_draws J.pub.par ds hd
  obtain ⟨x, hx⟩ := one_of_length (h1 d1 (List.mem_cons_of_mem _ List.mem_cons_self))
  refine ⟨shareAt J (askZero J m.st.input m.shown m.st.heard d0 ca) gs, rfl, fun c => ?_⟩
  obtain ⟨y, hy, e⟩ := plays_is (V := V) J σ.block.name ⟨σ.block.place, 0⟩ (φ.sees m.st.input)
    (c.1, c.2, ca) m d0 d1 gs hk h1 _ rfl
  have h2 : σ.shows φ (closeAt true J) (c.1, c.2, ca) m (d0 :: d1 :: gs) asks =
      some (shownOf y.1 asks) :=
    congrArg (fun r : Except Refusal (List Played × Mid W X) =>
      r.toOption.map fun z : List Played × Mid W X => shownOf z.1 asks) hy
  rw [h2, shown_plain y.1 asks ((List.range (2 + J.pub.par.k)).map fun i =>
    (saysAt J (askZero J m.st.input m.shown m.st.heard d0 (handSnd (c.1, c.2, ca)).2.2)
      (spentRun J (handSnd (c.1, c.2, ca))) d1 gs i).vals.map Said.got)
    (by rw [e, List.map_map]; rfl), List.map_map]
  exact congrArg some (says_lay J hp.1 _ (handSnd (c.1, c.2, ca)) d0 d1 gs hk x hx _ rfl)

/-- **So (3c) at the total form, at every job.** -/
theorem close_oneToOne (J : CloseJob W) : CloseOneToOne S Cl V X Pb true J :=
  oneToOne_of run_one_to_one (sent_is J)

/-- **And (2).** -/
theorem close_exact (J : CloseJob W) : CloseExact S Cl V X Pb true J := exact_of_sentIs (sent_is J)

/-! ## At the seated job -/

section
variable {W₀ Rc Xi Tr : Type} (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
  (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr)
  (segs : List ProofFile.Honest.K2.SegmentPub)
  (stAt : StAtOf Xi) (pub : ClosePub)

/-- Honest/K10/SimSeat.lean's (3b) at the seated job. -/
theorem seated_sentIs : SeatedSentIs readers rows lay addrs segs stAt pub S Cl X := sent_is _

/-- Its (3c). -/
theorem seated_oneToOne : SeatedOneToOne readers rows lay addrs segs stAt pub S Cl X := close_oneToOne _

/-- Its (2). -/
theorem seated_exact : SeatedExact readers rows lay addrs segs stAt pub S Cl X := close_exact _

/-- Its (5). Without content, as `close_fresh` (Honest/K10/SimLaws.lean): the frame's sentence for an owner, at a part
that owns no coin: both sides are drawn over one point. It is not the `fresh` that the run's owners owe. -/
theorem seated_fresh : SeatedFresh readers rows lay addrs segs stAt pub S Cl X := close_fresh true _

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.drawFit_elems
#print axioms ProofFile.Honest.K10.draws_ones
#print axioms ProofFile.Honest.K10.close_draws
#print axioms ProofFile.Honest.K10.askZero
#print axioms ProofFile.Honest.K10.askWith
#print axioms ProofFile.Honest.K10.askOr_is
#print axioms ProofFile.Honest.K10.steps_get
#print axioms ProofFile.Honest.K10.stopBoth_none
#print axioms ProofFile.Honest.K10.standAt
#print axioms ProofFile.Honest.K10.standAt_zero
#print axioms ProofFile.Honest.K10.standAt_succ
#print axioms ProofFile.Honest.K10.fits_of
#print axioms ProofFile.Honest.K10.lately_is
#print axioms ProofFile.Honest.K10.saysAt
#print axioms ProofFile.Honest.K10.get_round
#print axioms ProofFile.Honest.K10.says_tables
#print axioms ProofFile.Honest.K10.plays_is
#print axioms ProofFile.Honest.K10.shown_aux
#print axioms ProofFile.Honest.K10.shown_plain
#print axioms ProofFile.Honest.K10.read_run
#print axioms ProofFile.Honest.K10.shareAt
#print axioms ProofFile.Honest.K10.sigma_val
#print axioms ProofFile.Honest.K10.round_val
#print axioms ProofFile.Honest.K10.says_lay
#print axioms ProofFile.Honest.K10.sent_is
#print axioms ProofFile.Honest.K10.close_oneToOne
#print axioms ProofFile.Honest.K10.close_exact
#print axioms ProofFile.Honest.K10.seated_sentIs
#print axioms ProofFile.Honest.K10.seated_oneToOne
#print axioms ProofFile.Honest.K10.seated_exact
#print axioms ProofFile.Honest.K10.seated_fresh
