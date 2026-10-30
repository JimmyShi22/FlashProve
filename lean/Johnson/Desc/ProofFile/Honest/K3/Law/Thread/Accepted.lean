-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/Accepted.lean: the honest side of the kind "lookup"
(K3). Conditional: the frame's sentence "it is accepted" (`Accepted`, Honest/Thread/Pays.lean) at a
member of the first chain at whose place a lookup's seated row stands. General in the first chain's
letters, and in the letter fall, of which nothing is assumed. One definition; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number. The join is the statement `JoinedAt`
(Honest/K3/Law/Joined.lean).

What is shown.
  `JoinsAt`: the hypothesis: from the thread in front, at all coins that the row can be lent, the
    join holds at the member itself.
  `accepted_look`: `Accepted L.thread fall b`.
  `stepped_look`: under the same hypotheses: whatever the member's step has left, it is the state of
    which the join speaks.

Hypotheses that remain.
  `hS`: `SeatedAt` (Honest/K3/Law/Thread/Plays.lean): the lookup's seated row stands at the member's
    place.
  `hJ`: `JoinsAt`. It can be had from the join at the description's own member
    (Honest/K3/Law/MemberSite.lean, which is conditional) and the state in front
    (Honest/K3/Law/Thread/AtBorder.lean). The same sentence, for any thread, is the field joins of
    `K3Seated` (Honest/K3/Law/Thread/AtThread.lean); `seated_of_atSite`
    (Honest/K3/Law/Thread/AtThreadSite.lean) shows that field from the description's return and
    `K3AtSite`.
  `hb`, `hA`, `hd`, `hSt`: (in `stepped_look`) blk is member number b; the thread holds in front;
    the challenges are such as the member's rounds can draw; the member's step has been taken.

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/SiteThr.lean and Honest/K3/Law/Thread/ToyLetters.lean
[not in this library] call `accepted_look`; Honest/K3/Law/Thread/LeftThr.lean calls `stepped_look`;
Honest/K3/Law/Thread/AtThread.lean imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`Accepted` is a form of a hypothesis of the frame's. The acceptance is said at any summands: it says
nothing on values.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **From the thread in front the join holds at the member itself**, at all coins that the row can
be lent. Here first is the ledger's count in front, a letter; fork is the seat's reader of the
ledger: the hearing begins at the ledger that the state itself holds; Q is what is said of the state
that the member's step leaves. The chain's number and the number of its first own tree are the
thread's own. The tables at hand are set to none: a lookup's rounds read no column, so the join's
clause on columns depends on none of the four. -/
def JoinsAt (b : Nat) (a : At) (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj) (first : Nat)
    (fork : FS → Option Fork) (Q : FS → FS → HeardV → Fork → Prop) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ (k : Coins Bk) (s : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo) (E : Env)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit a).parts),
    Thr L.thread b k s m E → drawsFit blk.rounds ds = true →
    ∃ F, fork s = some F ∧ JoinedAt blk a J wit (L.thread.φ.sees m.st.input) m ds c first s F
      L.thread.chain
      L.thread.ft (fun _ _ => none) (fun _ => none) (Q s)

variable {L}

/-- **Whatever the member's step has left is the state of which the join speaks**: from the thread
in front and the member's step: the columns are none; the state behind has the challenges heard, the
rounds laid behind, and its field `opened` as it stood in front; the coins c are those that the book
lent the row; F is the ledger that the state in front holds; `hearV` has returned on the played
rounds from F; Q holds; and so does what stands behind the hearing's acceptance, at these coins and
at the letter first. Conditional on `SeatedAt` and `JoinsAt`. No instance of these hypotheses is
exhibited in this file. -/
theorem stepped_look {b : Nat} {a : At} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj}
    {es : List Fmt.Entry} {first : Nat} {fork : FS → Option Fork}
      {Q : FS → FS → HeardV → Fork → Prop}
    (hS : SeatedAt L b a J wit es) (hJ : JoinsAt L b a J wit first fork Q) {blk : Block FS Cl}
    (hb : L.bs[b]? = some blk) {k : Coins Bk}
    {s s' : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn} (hA : Thr L.thread b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hSt : L.thread.Stepped blk k s m E ds y cols s') :
    cols = [] ∧
      y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds,
        m.seen ++ roundsOf y.1, m.opened⟩ ∧
      ∃ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr)
        (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit a).parts)
        (F : Fork) (g : HeardV) (G : Fork),
        lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) blk.place
          (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit a).parts 0 =
            .ok c ∧
        fork s = some F ∧ hearV a.face F (roundsOf y.1) = some (g, G) ∧ Q s s' g G ∧
          BehindYes a J first wit m ds c g G := by
  obtain ⟨⟨⟨l, hl, hy⟩, hc⟩, hstep⟩ := hSt
  obtain ⟨_, _, c, hlend, rfl⟩ := chainSteps_one Bk _ _ _ blk L.hs _ (hS.half blk hb) l hl
  obtain ⟨F, hFk, y', t, g, G, hy', hy2, _, _, hstep', hh, hQ, hB⟩ := hJ blk hb k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    rw [hS.rounds blk hb, readsOf_plain] at hc
    exact (Except.ok.inj hc).symm
  subst hc0
  have e : (t, 0) = (s', ([] : List OpenedColumn).length) := Except.ok.inj (hstep'.symm.trans hstep)
  obtain rfl : t = s' := congrArg Prod.fst e
  exact ⟨rfl, hy2, c, F, g, G, hlend, hFk, hh, hQ, hB⟩

/-- **It is accepted**: the frame's sentence at member number b of the first chain, at every letter
fall: from the thread in front and the prover's side of the step, the member's own step accepts.
Conditional on `SeatedAt` and `JoinsAt`. No instance of these hypotheses is exhibited in this file.
-/
theorem accepted_look {b : Nat} {a : At} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj}
    {es : List Fmt.Entry} {first : Nat} {fork : FS → Option Fork}
      {Q : FS → FS → HeardV → Fork → Prop}
    (hS : SeatedAt L b a J wit es) (hJ : JoinsAt L b a J wit first fork Q)
    (fall : Nat → FS → List Fmt.Drawn → Option String) :
    Accepted L.thread fall b := by
  intro blk hb k s m E ds y cols hA hd _ _ hM
  have hb' : L.bs[b]? = some blk := hb
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl' := hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk L.hs _ (hS.half blk hb') l hl
  obtain ⟨F, _, y', t, g, G, hy', _, _, _, hstep, _⟩ := hJ blk hb' k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    have hc' := hc
    rw [hS.rounds blk hb', readsOf_plain] at hc'
    exact (Except.ok.inj hc').symm
  subst hc0
  exact ⟨t, ⟨⟨_, hl', hy⟩, hc⟩, hstep⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.stepped_look
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_look
