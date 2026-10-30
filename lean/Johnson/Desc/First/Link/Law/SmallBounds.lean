--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/SmallBounds.lean: THE SMALL BOUNDS THAT `hlen_layers` AND `hlen_head`
(K9LensAskLaw.lean) TAKE AS PREMISES: each run's own number of claims against its closed number.
Statements and proofs: unfoldings and calls.

  `pickLen_le`: the lookups' `pickLen hd lm jLK n q` (Johnson/Top/H/Keep/RunsPlain.lean: "planes" at
    n = 3, "join" at n = 1) is at most n: by its text.
  `ends_rows`: (endsOf h lm jLK rs).rows.length = Forest.lins h where FoNums.ok h: the lookups' two
    landed lemmas (`Fo.ends_rows_len`, `lins_rows`) and a subtraction.
  `objLen_le`: **the lookups' `objLen hd lm jLK q` ("objects") is at most Forest.lins sh**, under
    their promise on the fixed part (`K3Ok`) and "what was heard has the shape sh".
  `lenFront_le`: **lenFront p4 (·.own) q ≤ frontB y g**, where the seat's lookup states its own runs
    (p4.k3Runs = true), p4.g = g, and what the fixed part holds as the segment's own has the layout
    y.
  `lenK6_le`: **lenStill (fsK6 h iU3 p kap name) q ≤ lenK6 name** (29, 4, 2; 0 at any other name):
    the head's house's `lens_K6`. NO PREMISE.
  `lenJoin_le`: **lenStill (fsJoin h iU3 p kap) q ≤ 1.** NO PREMISE.
Limits. `K3Ok`, the heard shape and the layout are premises. No soundness statement.

-/
import Johnson.Desc.First.Link.K9LensAsk
import Johnson.Desc.First.Link.Law.LensAtFront
import Johnson.Top.H.Keep.RunsPlain
import OnBytes.Tie.Pv.Lookup.Forest.FoOutLen
import OnBytes.Tie.Pv.Tail.LinsRows
import Johnson.Desc.Kinds.Law.RunsFixed
import Johnson.Desc.Kinds.Law.JoinRunAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Run (lenFront)
open VerifiableInference.Desc.K9Asks (frontB)
open VerifiableInference.OnPublicFiles (K3Ok Stood pick pick_spec objLen pickLen)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {α : Type}

/-- "planes" and "join". -/
theorem pickLen_le (hd : α → Option Forest.Heard) (lm jLK n : ℕ) (q : α × Option Pub9) :
    pickLen hd lm jLK n q ≤ n := by
  unfold pickLen
  cases pick hd lm jLK q with
  | none => exact Nat.zero_le _
  | some _ => exact Nat.le_refl _

/-- The number of flat rows is the planners' number. -/
theorem ends_rows {K : Type} [CommRing K] (h : Forest.Shape) (H : FoNums.ok h = true)
    (lm jLK : ℕ) (rs : TwV.Rounds K) :
    (_root_.Fo.endsOf h lm jLK rs).rows.length = Forest.lins h := by
  have a := _root_.Fo.ends_rows_len h lm jLK rs
  have b := OnBytes.Tie.Pv.Tail.lins_rows h H
  omega

/-- **"objects".** -/
theorem objLen_le (hd : α → Option Forest.Heard) (lm jLK : ℕ) {q : α × Option Pub9}
    (K : K3Ok hd lm jLK q) {sh : Forest.Shape} (hs : ∀ g, hd q.1 = some g → g.shape = sh) :
    objLen hd lm jLK q ≤ Forest.lins sh := by
  unfold objLen
  cases e : pick hd lm jLK q with
  | none => exact Nat.zero_le _
  | some x =>
    obtain ⟨h1, F0, u, h2, _⟩ := pick_spec hd lm jLK e
    obtain ⟨_, ok, _⟩ := K x.1 u h1 h2
    show (_root_.Fo.endsOf x.1.shape lm jLK x.2).rows.length ≤ _
    rw [ends_rows x.1.shape ok, hs x.1 h1]

/-- **The layers' run "front".** -/
theorem lenFront_le {β : Type} (p4 : OnBytes.Desc.First.K4.Par) {q : Q β} {y : Layer.Lay}
    {g : ℕ} (hk : p4.k3Runs = true) (hg : p4.g = g)
    (ho : ∀ o, q.1.own = some o → o.v.y = y) : lenFront p4 (·.own) q ≤ frontB y g := by
  unfold lenFront
  show (match q.1.own with
    | some o => OnBytes.Desc.First.K4.frontLen (!p4.k3Runs) p4.g o
    | none => 0) ≤ frontB y g
  cases e : q.1.own with
  | none => exact Nat.zero_le _
  | some o =>
    show OnBytes.Desc.First.K4.frontLen (!p4.k3Runs) p4.g o ≤ _
    rw [hk, hg]
    unfold OnBytes.Desc.First.K4.frontLen frontB
    rw [ho o e]
    exact Nat.le_refl _

variable (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (kap : α → Option Seen)

/-- **The head's three runs.** -/
theorem lenK6_le (name : String) (q : α × Option Pub9) :
    lenStill (fsK6 h iU3 p kap name) q ≤ lenK6 name := by
  unfold lenStill
  cases e : fsK6 h iU3 p kap name q with
  | none => exact Nat.zero_le _
  | some l =>
    show l.length ≤ _
    unfold fsK6 at e
    split at e
    · rename_i z u _ _
      have e' : formsOf h iU3 p name z u.F = some l := e
      unfold formsOf at e'
      obtain ⟨v, _, lk⟩ := Option.bind_eq_some_iff.mp e'
      letI := v.1
      letI := v.2.1
      letI := v.2.2
      exact Nat.le_of_eq (lens_K6 name l lk)
    · exact nomatch e

/-- **The head's join.** -/
theorem lenJoin_le (q : α × Option Pub9) : lenStill (fsJoin h iU3 p kap) q ≤ 1 := by
  unfold lenStill
  cases e : fsJoin h iU3 p kap q with
  | none => exact Nat.zero_le _
  | some l =>
    show l.length ≤ _
    unfold fsJoin at e
    split at e
    · rename_i z u _ _
      obtain ⟨v, _, hm⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨g, _, rfl⟩ := Option.map_eq_some_iff.mp hm
      exact Nat.le_refl _
    · exact nomatch e

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pickLen_le
#print axioms VerifiableInference.Desc.LinkJoin.ends_rows
#print axioms VerifiableInference.Desc.LinkJoin.objLen_le
#print axioms VerifiableInference.Desc.LinkJoin.lenFront_le
#print axioms VerifiableInference.Desc.LinkJoin.lenK6_le
#print axioms VerifiableInference.Desc.LinkJoin.lenJoin_le
