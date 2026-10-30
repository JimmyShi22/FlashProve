-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyHeardTies.lean: THREE OF THE FOUR TIES OF `HeardIs` (E2E/KeyEvalSays.lean), AT THE VERIFIER's
OWN TEXT OF THE BATCHING: what that text reads off its rounds is what W's job reads off the
challenges heard. Equations between two readers of the same challenges. Statements and proofs.

The setting. The text of the batching of the rows on the matrix (`K13.batt`,
Johnson/Desc/K13/Text.lean) is handed 2 + k rounds: in the first one element is sampled; in the
second the joining element; in each further one the challenge of a column variable. W's job
(E2E/KeySendJobs.lean) is handed the list of all challenges heard in front of its part, and reads it
by number (`elemAt`).

What is shown.
  `elemAt_one`, `oneDrawn_one`, `oneRound_one`, `rounds_one`, `heard_one`: small steps on the two
    readers.
  **`ties_at`**: THE THREE TIES AT LETTERS, under the clauses of the library's `batt_ok`
    (Johnson/Desc/K13/Law/Law.lean): x is the challenge number base, the joining element the
    challenge number base + 1, the sumcheck's point the k challenges from base + 2 on.
  `BattTies`, **`ties_of_batt`**: where the text accepts its rounds rs, and the list of challenges
    heard holds the challenges of rs from the number base on: there are letters with EIGHT OF THE
    TEN CLAUSES that `batt_ok` has of them (which round sampled x; which mask entries were taken, so
    what the list of fresh slots is; what was heard; the sumcheck's return; the row and the state
    that the text returns; left out: "no count of rows waits", "a coefficient a row") AND the three
    ties: so a law that is stated at what was heard and at the fresh slots can be joined.
  **`BattTies.heardIs`**: so `HeardIs` at the three public rounds (base, base + 1, base + 2), from
    its first tie alone.
  **`ties_of_battB`**: the same from the acceptance of the kind's sub-protocol (`K13.claimCombinationBlock`) at any
    lens, so at the key file's, with what that acceptance says of the two states: the state behind
    holds the claim made of the row that the text has returned.

  **`holds_of_heardFrom`**: the premise on the list, from the form in which the honest side's own
    law on what a member's rounds sampled has it (`heardFrom_member`, `heardFrom_more`,
    Johnson/Desc/ProofFile/Honest/Thread/HeardLaw.lean), also for a list that is cut behind these
    rounds, as the list is that a later part is handed.

Limits. THE PREMISE ON THE LIST: that the challenges heard hold, from the number base on, the
challenges of just the rounds that the verifier's text is handed, is a premise of the ties.
`holds_of_heardFrom` brings it to the form of that law; the law's own premises (a thread that fits;
a member that has moved) and the number base are shown here of nothing. No value that was sent is
read. Nothing on any prover. Nothing on hiding follows from this file.


-/
import E2E.KeyEvalSays
import Johnson.Desc.K13.Law.AtM3
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K13 (batt oneDrawn oneRound heard claimCombinationBlock Lens Where St)
open VerifiableInference.Desc.K13.Law (batt_ok run_fields battB_ok bind_ok pure_ok)

/-- The reader by number, at a round that sampled one element. -/
theorem elemAt_one (l : List Fmt.Drawn) (i : Nat) (d : Fmt.Drawn) (u : UInt64 × UInt64 × UInt64)
    (h : l[i]? = some d) (hd : d.elems = [u]) : elemAt l i = E.ofTriple u := by
  unfold elemAt
  rw [h]
  simp [hd]

/-- The text's reader of the one element that a round has sampled. -/
theorem oneDrawn_one {name : String} {r : Fmt.RoundView} {x : E} (h : oneDrawn name r = .ok x) :
    ∃ u, r.drawn.elems = [u] ∧ x = E.ofTriple u := by
  unfold oneDrawn at h
  match he : r.drawn.elems with
  | [u] =>
    rw [he] at h
    exact ⟨u, rfl, (Except.ok.inj h).symm⟩
  | [] => rw [he] at h; cases h
  | _ :: _ :: _ => rw [he] at h; cases h

/-- The text's reader of a round in which elements are sent and one is sampled. -/
theorem oneRound_one {r : Fmt.RoundView} {q : List E × E} (h : oneRound r = .ok q) :
    ∃ u, r.drawn.elems = [u] ∧ q.2 = E.ofTriple u := by
  simp only [oneRound, bind_ok, pure_ok] at h
  obtain ⟨_, -, x, hx, rfl⟩ := h
  exact oneDrawn_one hx

/-- The text's reader of the sumcheck's further rounds, round by round. -/
theorem rounds_one : ∀ (l : List Fmt.RoundView) (inX : List (List E × E)), l.mapM oneRound = .ok inX →
    inX.length = l.length ∧ ∀ (i : Nat) (r : Fmt.RoundView), l[i]? = some r →
      ∃ u, r.drawn.elems = [u] ∧ (inX.map (·.2))[i]? = some (E.ofTriple u)
  | [], inX, h => by
    rw [List.mapM_nil, pure_ok] at h
    subst h
    exact ⟨rfl, fun i r hr => absurd hr (by simp)⟩
  | r₀ :: l, inX, h => by
    rw [List.mapM_cons] at h
    simp only [bind_ok, pure_ok] at h
    obtain ⟨q, h0, qs, hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := rounds_one l qs hl
    refine ⟨by rw [List.length_cons, List.length_cons, h1], fun i r hr => ?_⟩
    cases i with
    | zero =>
      obtain rfl : r₀ = r := Option.some.inj hr
      obtain ⟨u, hu, hq⟩ := oneRound_one h0
      exact ⟨u, hu, by simp [hq]⟩
    | succ i => exact h2 i r hr

/-- What the text hears in the sumcheck's rounds. -/
theorem heard_one {rs : List Fmt.RoundView} {hd : Psc.Heard} (h : heard rs = .ok hd) :
    ∃ r₀ rest, rs = r₀ :: rest ∧ (∃ u, r₀.drawn.elems = [u] ∧ hd.eps = E.ofTriple u) ∧
      rest.mapM oneRound = .ok hd.rounds := by
  cases rs with
  | nil => cases h
  | cons r₀ rest =>
    simp only [heard, bind_ok, pure_ok] at h
    obtain ⟨a, ha, _, -, inX, hin, rfl⟩ := h
    exact ⟨r₀, rest, rfl, oneRound_one ha, hin⟩

/-- **The three ties, AT LETTERS**: r, rs', x, hd, o are those of the library's `batt_ok`, under its
own clauses: so whoever holds that law's letters holds the ties of the same letters. -/
theorem ties_at {k : Nat} {pile : List TensorRow} {fresh : List Slot} {r : Fmt.RoundView}
    {rs' : List Fmt.RoundView} {x : E} {hd : Psc.Heard} {o : Psc.Out} (hf : Batt.fits k pile = true)
    (hx : oneDrawn "K13.sigma-one-drawn" r = .ok x) (hh : heard rs' = .ok hd)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh hd = some o)
    (l : List Fmt.Drawn) (base : Nat)
    (hl : ∀ (i : Nat) (q : Fmt.RoundView), (r :: rs')[i]? = some q → l[base + i]? = some q.drawn) :
    x = elemAt l base ∧ hd.eps = elemAt l (base + 1) ∧
      o.point = (List.range k).map fun i => elemAt l (base + 2 + i) := by
  obtain ⟨hlen, -, -, hpt, -, -, -⟩ := run_fields hf hr
  obtain ⟨r₀, rest, rfl, ⟨u₀, hu₀, he⟩, hq⟩ := heard_one hh
  obtain ⟨g1, g2⟩ := rounds_one rest hd.rounds hq
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := oneDrawn_one hx
    exact (elemAt_one l base r.drawn u (by simpa using hl 0 r rfl) hu).symm
  · rw [he]
    exact (elemAt_one l (base + 1) r₀.drawn u₀ (hl 1 r₀ rfl) hu₀).symm
  · rw [hpt]
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < k
    · have hi' : i < rest.length := by
        rw [← g1, hlen]
        exact hi
      obtain ⟨u, hu, hv⟩ := g2 i rest[i] (List.getElem?_eq_getElem hi')
      have hat : l[base + 2 + i]? = some rest[i].drawn := by
        have h3 := hl (i + 2) rest[i] (by simp [List.getElem?_eq_getElem hi'])
        rwa [show base + (i + 2) = base + 2 + i by omega] at h3
      rw [hv, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        elemAt_one l (base + 2 + i) rest[i].drawn u hat hu]
    · rw [List.getElem?_eq_none (by rw [List.length_map, hlen]; exact Nat.le_of_not_lt hi),
        List.getElem?_eq_none
          (by rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt hi)]

/-- **What the text's acceptance holds, with the ties.** EIGHT OF THE TEN CLAUSES OF THE LIBRARY's
`batt_ok` ARE HANDED ON (not: that no count of rows waits, so the letter owed is read by no field;
not: a coefficient a row): which round sampled x; which mask entries were taken, so what fresh is;
what was heard; the sumcheck's return; the row and the state that the text returns. -/
structure BattTies (owed : Johnson.Desc.First.ForkGround.RowsOwed) (k n : Nat)
    (pile : List TensorRow) (ledger : Nat) (d : St) (rs : List Fmt.RoundView) (out : TensorRow × St)
    (l : List Fmt.Drawn) (base : Nat) (r : Fmt.RoundView) (rs' : List Fmt.RoundView) (x : E)
    (t : List Nat × St) (hd : Psc.Heard) (o : Psc.Out) : Prop where
  rounds : rs = r :: rs'
  fits : Batt.fits k pile = true
  sampled : oneDrawn "K13.sigma-one-drawn" r = .ok x
  count : pile.length = n
  taken : VerifiableInference.Desc.Ground.takeMasksP d ledger (Batt.masksOf k) = some t
  heard : heard rs' = .ok hd
  run : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩) hd =
    some o
  out : out = (Batt.rowOf pile o, t.2)
  x_is : x = elemAt l base
  eps_is : hd.eps = elemAt l (base + 1)
  point_is : o.point = (List.range k).map fun i => elemAt l (base + 2 + i)

/-- **What the verifier's text of the batching reads off its rounds is what W's job reads off the
challenges heard.** -/
theorem ties_of_batt {owed : Johnson.Desc.First.ForkGround.RowsOwed} {k n : Nat}
    {pile : List TensorRow} {ledger : Nat} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}
    (hb : batt owed k n pile ledger d rs = .ok out) (l : List Fmt.Drawn) (base : Nat)
    (hl : ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r → l[base + i]? = some r.drawn) :
    ∃ r rs' x t hd o, BattTies owed k n pile ledger d rs out l base r rs' x t hd o := by
  obtain ⟨r, rs', x, t, hd, o, rfl, -, hf, hx, hn, ht, hh, hr, -, ho⟩ := batt_ok hb
  obtain ⟨e1, e2, e3⟩ := ties_at hf hx hh hr l base hl
  exact ⟨r, rs', x, t, hd, o, rfl, hf, hx, hn, ht, hh, hr, ho, e1, e2, e3⟩

/-- `HeardIs` of these letters, from its first tie. -/
theorem BattTies.heardIs {one : OneTime} {points : List Fmt.Drawn → Nat → Nat → List E}
    {owed : Johnson.Desc.First.ForkGround.RowsOwed} {n : Nat} {pile : List TensorRow}
    {ledger : Nat} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St} {l : List Fmt.Drawn}
    {base : Nat} {r : Fmt.RoundView} {rs' : List Fmt.RoundView} {x : E} {t : List Nat × St} {hd : Psc.Heard}
    {o : Psc.Out}
    (h : BattTies owed (Wf.matrixOf one.lin).kCol n pile ledger d rs out l base r rs' x t hd o)
    (hp : pile.map (fun r => (r.g, r.psi)) =
      (pileOf (Wf.matrixOf one.lin) one.ranges.lookups (points l)).map fun r => (r.g, r.psi)) :
    HeardIs one points ⟨base, base + 1, base + 2⟩ pile x hd o l :=
  ⟨hp, h.x_is, h.eps_is, h.point_is⟩

/-- **The same from the acceptance of the kind's sub-protocol, at any lens**, with what that
acceptance says of the two states: the part in front, and that the state behind holds the claim
made of the row that the text has returned. -/
theorem ties_of_battB {T Cl : Type} (Xl : Lens T) (p : Where) {t₀ t₁ : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (claimCombinationBlock (Cl := Cl) Xl p).decide t₀ rs gs = .ok t₁) (l : List Fmt.Drawn) (base : Nat)
    (hl : ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r → l[base + i]? = some r.drawn) :
    ∃ (q : VerifiableInference.Desc.K13.Part) (out : TensorRow × St), Xl.get? t₀ = some q ∧
      batt q.owed p.lin.kCol p.rows q.pile q.indexMasks q.d rs = .ok out ∧
      t₁ = Xl.set t₀
        { q with owed := none, lin := some { claim := memberClaim out.1 }, d := out.2 } ∧
      ∃ r rs' x t h o,
        BattTies q.owed p.lin.kCol p.rows q.pile q.indexMasks q.d rs out l base r rs' x t h o := by
  obtain ⟨q, out, hq, hb, ht⟩ := battB_ok Xl p hd
  exact ⟨q, out, hq, hb, ht, ties_of_batt hb l base hl⟩

/-- **The premise on the list, from the form in which the honest side's own law has it**
(`heardFrom_member`, `heardFrom_more`, Johnson/Desc/ProofFile/Honest/Thread/HeardLaw.lean): where
the entries of what a state has heard, from the number base on, are the challenges of the rounds rs,
the list cut at any length m behind them holds these challenges from base on. -/
theorem holds_of_heardFrom {W X : Type} (t : ProofFile.Honest.State W X) (base : Nat) (rs : List Fmt.RoundView)
    (h : ProofFile.Honest.heardFrom t base rs.length = rs.map (·.drawn)) (m : Nat)
    (hm : base + rs.length ≤ m) :
    ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r → (t.heard.take m)[base + i]? = some r.drawn := by
  intro i r hr
  have hi : i < rs.length := (List.getElem?_eq_some_iff.1 hr).1
  have e : (ProofFile.Honest.heardFrom t base rs.length)[i]? = some r.drawn := by
    rw [h, List.getElem?_map, hr]
    rfl
  unfold ProofFile.Honest.heardFrom at e
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop] at e
  rw [List.getElem?_take_of_lt (by omega)]
  exact e

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.elemAt_one
#print axioms AtPublicFiles.Key.oneDrawn_one
#print axioms AtPublicFiles.Key.oneRound_one
#print axioms AtPublicFiles.Key.rounds_one
#print axioms AtPublicFiles.Key.heard_one
#print axioms AtPublicFiles.Key.ties_at
#print axioms AtPublicFiles.Key.ties_of_batt
#print axioms AtPublicFiles.Key.BattTies.heardIs
#print axioms AtPublicFiles.Key.ties_of_battB
#print axioms AtPublicFiles.Key.holds_of_heardFrom
