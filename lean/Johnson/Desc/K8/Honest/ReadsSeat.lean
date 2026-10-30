-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/ReadsSeat.lean: THE SMALLNESS TEST: THE MEMBER RIGHT IN FRONT OF THE DRAW, AS
THE PROOF FILE's DESCRIPTION SEATS IT (`IM.k1Reads`, Johnson/IMR/K1Seat.lean: the sending of the
reads with the quiet step joined behind it; laid alone: `IM.LaidAlone`, Johnson/IMR/SeatForm.lean),
AT A LAYERS' SEGMENT AND AT THE OUTPUT HEAD: EVERY YES OF IT LAYS THE PLAN's DATA OF THE TEST,
CLOSED; at the head, besides, with a list of the place's shapes. Lemmas on the verifier's own text;
no prover, no message, no coin in them; none of the library's goals.

  `LaysClosed tl0 c`   behind every yes of c the test's data are tl0, closed, with some list of
                   tables: the first half of the library's `Ready.ClosesFrom`
                   (Johnson/Desc/First/K8/LawReadyText.lean): it asks nothing of the state in front.
                   `.behind`: it passes to the step joined behind ANY block (the closing step runs
                   last) · `.under`: and along `Block.Under` · `.keep`, `.closed`: so the library's
                   two readings behind such a yes
  `k1Quiet_layers`, `k1Quiet_head`   WHICH BLOCK THE LOT JOINS: at a link of kind 0 whose group has
                   the plan hp: `ReadsQuiet.layers` at hp.tl; at a link of kind 2: `ReadsQuiet.head`
                   at the public files' own numbers, layout and plan
  `reads_under_layers`, `reads_under_head`   so the seated member is under that step joined behind
                   the sending
  **`reads_closed_layers`**, **`reads_closed_head`**   LaysClosed hp.tl b · LaysClosed G.W.H.tl b
  **`reads_tabs_head`**   at the head every yes of b lays a list of the shapes `tabs p`, at a place
                   with the three facts (Johnson/Desc/K8/Honest/HeadShapes.lean: `head_tabs_under`)
Limits. That a chain's member is so laid is the library's `IM.k1_reads_of`
(Johnson/IMR/K1Scope.lean), in its scope: not called here. The attention segment's quiet step closes
the state's own data: not looked at. At a layers' segment nothing on the list's shapes. ALL HANG ON
A YES THAT IS EVALUATED NOWHERE HERE.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.IMR.K1Seat
import Johnson.Desc.First.K8.LawReadyText
import Johnson.Desc.K8.Honest.HeadShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par tabs)
open VerifiableInference.Desc.First.K8.Ready (ClosesFrom keep closedAt layers_closesFrom
  head_closesFrom)
open VerifiableInference.Desc.K8 (ReadsQuiet.layers ReadsQuiet.head ReadsQuiet.behind
  ReadsQuiet.bind_ok)

/-- Behind every yes of c the test's data are tl0, closed, with some list of tables. -/
def LaysClosed {Cl : Type} (tl0 : HTailF2) (c : Block S Cl) : Prop :=
  ∀ s rs gs s', c.decide s rs gs = .ok s' →
    ∃ funs, s'.tl? = some { tl0 with funClosed := true, funs := funs }

theorem LaysClosed.of_closesFrom {Cl : Type} {tl0 : HTailF2} {c : Block S Cl}
    (h : ClosesFrom tl0 c) : LaysClosed tl0 c := fun s rs gs s' hd => (h s rs gs s' hd).1

/-- Joined behind any block: the closing step runs last. -/
theorem LaysClosed.behind {Cl : Type} {tl0 : HTailF2} {q : Block S Cl} (h : LaysClosed tl0 q)
    (own : Block S Cl) (name : String) : LaysClosed tl0 (Block.andThen name own q) := by
  intro s rs gs s' H
  have H' : (own.decide s (rs.take own.rounds.length) (gs.take own.openings)).bind (fun t =>
      q.decide t (rs.drop own.rounds.length) (gs.drop own.openings)) = .ok s' := H
  obtain ⟨t, _, H'⟩ := ReadsQuiet.bind_ok H'
  exact h _ _ _ _ H'

theorem LaysClosed.under {Cl Cl' : Type} {tl0 : HTailF2} {c : Block S Cl'} {b : Block S Cl}
    (h : LaysClosed tl0 b) (u : c.Under b) : LaysClosed tl0 c :=
  fun s rs gs s' hd => h s rs gs s' (u s rs gs s' hd)

theorem LaysClosed.keep {Cl : Type} {tl0 : HTailF2} {c : Block S Cl} (h : LaysClosed tl0 c)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : c.decide s rs gs = .ok s') :
    keep s' = some (tl0.NM, tl0.mats, tl0.tau, tl0.cfF, tl0.foldDrawn) := by
  obtain ⟨funs, ht⟩ := h s rs gs s' hd
  unfold Ready.keep
  rw [ht]
  rfl

theorem LaysClosed.closed {Cl : Type} {tl0 : HTailF2} {c : Block S Cl} (h : LaysClosed tl0 c)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : c.decide s rs gs = .ok s') : closedAt s' = some true := by
  obtain ⟨funs, ht⟩ := h s rs gs s' hd
  unfold Ready.closedAt
  rw [ht]
  rfl

/-- The link's entry in the list of kinds. -/
theorem kinds_entry {G : ProofFile.Ground} {l : Nat} {X : LinkH} (hX : G.built[l]? = some X) :
    (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (X.kind, X.g) := by
  rw [List.getElem?_map, Array.getElem?_toList, hX]
  rfl

/-- **Which block the lot joins at a layers' segment.** -/
theorem k1Quiet_layers {G : ProofFile.Ground} {l : Nat} {X : LinkH} {hp : Layer.HPlan2}
    (hX : G.built[l]? = some X) (hk : X.kind = 0) (hg : G.W.G[X.g]? = some hp) :
    IM.k1Quiet G l X = ReadsQuiet.layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩ := by
  unfold IM.k1Quiet ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
  rw [kinds_entry hX]
  simp [hk, hg, ProofFile.orLoud]

/-- **Which block the lot joins at the output head.** -/
theorem k1Quiet_head {G : ProofFile.Ground} {l : Nat} {X : LinkH} (hX : G.built[l]? = some X)
    (hk : X.kind = 2) :
    IM.k1Quiet G l X = ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ := by
  unfold IM.k1Quiet ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
  rw [kinds_entry hX]
  simp [hk, ProofFile.orLoud]

/-- The seated member is under the lot's own block. -/
theorem reads_under {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place}
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a) :
    b.Under (IM.k1Reads Z G l X pr reads) :=
  fun s rs gs s' hd => (IM.alone_underR la).2 s rs gs s' hd

theorem reads_under_layers {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place} {hp : Layer.HPlan2}
    (hX : G.built[l]? = some X) (hk : X.kind = 0) (hg : G.W.G[X.g]? = some hp)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a) :
    b.Under (ReadsQuiet.behind
      (VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
        reads)
      (ReadsQuiet.layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩)) := by
  have u := reads_under la
  unfold IM.k1Reads at u
  rw [k1Quiet_layers hX hk hg] at u
  exact u

theorem reads_under_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place}
    (hX : G.built[l]? = some X) (hk : X.kind = 2)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a) :
    b.Under (ReadsQuiet.behind
      (VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
        reads)
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩)) := by
  have u := reads_under la
  unfold IM.k1Reads at u
  rw [k1Quiet_head hX hk] at u
  exact u

/-- **At a layers' segment every yes of the member lays the plan's data, closed.** -/
theorem reads_closed_layers {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place} {hp : Layer.HPlan2}
    (hX : G.built[l]? = some X) (hk : X.kind = 0) (hg : G.W.G[X.g]? = some hp)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a) :
    LaysClosed hp.tl b :=
  ((LaysClosed.of_closesFrom (layers_closesFrom ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩)).behind _ _).under
    (reads_under_layers hX hk hg la)

/-- **At the output head every yes of the member lays the plan's data, closed.** -/
theorem reads_closed_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place}
    (hX : G.built[l]? = some X) (hk : X.kind = 2)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a) :
    LaysClosed G.W.H.tl b :=
  ((LaysClosed.of_closesFrom
    (head_closesFrom ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩)).behind _ _).under
    (reads_under_head hX hk la)

/-- **And a list of the place's shapes.** -/
theorem reads_tabs_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S ProofFile.Cl} {a : Place} (p : Par)
    (hX : G.built[l]? = some X) (hk : X.kind = 2)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a)
    (ha : p.asks = Asks.head G.W.hS) (hks : G.W.H.tl.mats.toList.map (·.k) = p.ks)
    (hms : G.W.H.tl.mats.toList.map (·.m) = p.ms) :
    ∀ s rs gs s', b.decide s rs gs = .ok s' → ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p :=
  fun _ _ _ _ hd =>
    head_tabs_under ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ p ha hks hms _ b
      (reads_under_head hX hk la) hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed.of_closesFrom
#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed.under
#print axioms VerifiableInference.Desc.First.K8.Honest.kinds_entry
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_under
#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed.behind
#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed.keep
#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed.closed
#print axioms VerifiableInference.Desc.First.K8.Honest.k1Quiet_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.k1Quiet_head
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_under_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_under_head
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_closed_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_closed_head
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_tabs_head
#print axioms VerifiableInference.Desc.First.K8.Honest.LaysClosed
