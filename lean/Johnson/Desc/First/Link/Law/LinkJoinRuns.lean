-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkJoinRuns.lean: THE LAW OF A LINK ON THE ROAD OF MOVES, AT THE
DRIVER's SEGMENT, FROM ONE DUTY A RUN. One structure of premises and one theorem, over
Johnson/Desc/First/Link/Law/LinkJoinAt.lean and JoinAtBlocks.lean.

Why. `LinkJoin.JoinAsks` takes five clauses on blocks and moves: `hb₁`, `hb₂`, `quiet`, `hms`,
`hkd`. At a segment that the driver makes of a record H whose batching at the segment's place is the
batching kind's own block (`K9.batch atS p`), they are paid here: the batching's block is a draw
with ONE move, «add what the link's own gatherer returns»; the frame's block behind it is ONE quiet
move; and each of the two owes what its runs owe.

What is said.
  `SegAt l sub L`: what the laws spend of «L is the segment number l, of the sort sub»: its two
    orders and the number of its hearing blocks; `segAt_of_linkAt`: a segment that the driver makes
    has them.
  `moves₁ L rl`, `moves₂ L`: the two lists of moves, each of one move, with their terms: those of
    the runs rl in a row; none.
  `RunsAsk`: what is left of `JoinAsks`: hb₁: the segment's batching is a draw with one move behind
    it, the link's own gatherer (it starts from a yes: a block behind a guard that only adds
    refusals meets it); hrl: rl's runs ARE the runs that the link's order names, off its hearing
    blocks' own lists; **hrun, hrund: one `RunOk` and one door's duty for each run of the order;
    hquiet, hquietd: one `QuietOk` and one door's duty for each run behind the batching**; and
    `JoinAsks`' other clauses, to the letter. `batchB_drawMoves`: hb₁ at a record whose batching at
    the place is the bare `K9.batch atS p`.
  `head_is_equation`: **`hb₃` and the guard**: where what the record holds at ⟨1, l, n + 3, K9⟩ has
    the one equation's rounds and decision, the head of the segment's closing has NO ROUND, and a
    yes of its step is a yes of the one equation's.
  `joinAsks_of_runs`: `RunsAsk` gives `JoinAsks` at the segment's own two blocks and their moves.
  `link_row_runs`: **under `RunsAsk` the three pieces at n + 1, n + 2, n + 3 are good in a row**
    between `onJ` and `relJ`.
  `pieces_at`: **where the three stand**: in a list ps that holds one piece for each block of the
    segment's flat list, the pieces at the numbers n + 1, n + 2, n + 3 hold the batching, the
    frame's block behind it and the head of the closing: `RunsAsk`'s hpb, hpq, hpe follow from the
    list. `link_row_at`: **the two joined**: `pieces_at` and `link_row_runs`, at j := i + (n + 1), i
    being where the segment's row begins in the chain's.

Limits. AN IMPLICATION: `RunsAsk` is shown of no record of the protocol. `batchB_drawMoves` and
`head_is_equation` pay hb₁ and hb₃ at a record that holds the BARE blocks; a record that lays them
behind a guard owes the two from «a guarded block's yes is the block's yes». Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkJoinAt
import Johnson.Desc.First.Link.Law.JoinAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {α W : Type} {F : Frame}

/-- What the laws spend of «L is the segment number l, of the sort sub»: its two orders and the
number of its hearing blocks. A segment that the driver makes has them, and so has that segment
behind a guard which leaves the orders and the number of blocks. -/
structure SegAt {T Cl : Type} (l : ℕ) (sub : First.ModelPart) (L : Link T Cl) : Prop where
  order : L.order = First.orderOf sub
  orderAfter : L.orderAfter = First.orderAfterOf sub
  hear : L.hear.length = (First.kindsBeforeBatching sub (l == 0)).length

theorem segAt_of_linkAt {T Cl : Type} {H : First.Blocks T Cl} {l : ℕ} {sub : First.ModelPart}
    {L : Link T Cl} (h : First.linkAt H l sub = some L) : SegAt l sub L :=
  ⟨(Shape.linkAt_shape h).2.2.2.2.1, (Shape.linkAt_shape h).2.2.2.2.2.1, Shape.linkAt_length h⟩

/-- The batching's one move: add what the link's own gatherer returns; its terms: the runs' in a
row. -/
def moves₁ (L : Link S Claim) (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) :
    List (Termed S (α × Option Pub9) Cb.Gl.E) :=
  [⟨.add (claimsInBy L.each L.hear L.order), fun n q y => termsRuns q y rl n,
    fun q => lenRuns q rl⟩]

/-- The one move of the frame's block behind the batching; it has no term. -/
def moves₂ (L : Link S Claim) : List (Termed S (α × Option Pub9) Cb.Gl.E) :=
  [⟨.quiet L.runBehind, fun _ _ _ => [], fun _ => 0⟩]

/-- What is left of JoinAsks at the driver's segment. -/
structure RunsAsk (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
    (ctx : S × F.E.Str → W → Prop) : Prop where
  /-- the segment's batching is a draw with one move behind it: add what the link's own gatherer
  returns. It starts from a yes: so a block behind a guard that only adds refusals meets it. At a
  record that holds the batching kind's bare block: `batchB_drawMoves` -/
  hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  /-- rl's runs are the runs that the link's order names, off its hearing blocks' own lists -/
  hrl : rl.map (·.run) = runsIn L.hear L.order
  /-- ONE DUTY A RUN OF THE ORDER -/
  hrun : ∀ r ∈ rl, RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) r.run.2 r.tm r.len
  hrund : ∀ r ∈ rl, ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) → KeepsDoor atS e e₁
  /-- ONE DUTY A RUN BEHIND THE BATCHING -/
  hquiet : ∀ o ∈ L.orderAfter, ∀ run,
    ((L.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run →
    QuietOk atS (O9 (K := Cb.Gl.E) φ Ok Fu) (Fx9 φ Ok) run
  hquietd : ∀ o ∈ L.orderAfter, ∀ run,
    ((L.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run →
    ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁
  hφ : ∀ s a, φ (atS.set s a) = φ s
  hd : d ≤ 2 ^ 60
  hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x
  hend : ∀ s s' cls, good9 s →
    MovesYes atS ((moves₁ L rl ++ moves₂ (α := α) L).map (·.move)) s s' cls → good9 s' ∧ Fu s'
  hok : ∀ s y, k9OnA s = true ∧ Ok (fixed9 φ s) →
    Desc.TermsOk Cb.Gl.E (termsOf (fixed9 φ s) y (moves₁ L rl ++ moves₂ (α := α) L) 0) d
  hpb : pb.b = below L.batchB
  hpq : pq.b = below L.behindB
  hpe : pe.b = below b₃
  hextb : ∀ a τ w, pb.ext a τ w = w
  hextq : ∀ a τ w, pq.ext a τ w = w
  hexte : ∀ a τ w, pe.ext a τ w = w
  hds : pb.ds = [k9Round p]
  hbk : pb.back = []
  hcap : pb.err = Err.cap 128 (uLT (ckP .two) pb.ds)
  hready : ∀ a, on0 a → k9OnA a.1 = true ∧ Ok (fixed9 φ a.1)
  h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b'
  h12 : ∀ b τ c, on1 b → pq.ior.red.out b τ = some c → on2 c
  hon3 : ∀ c τ e, on2 c → pe.ior.red.out c τ = some e → on3 e
  hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true
  hpin : ∀ a w w', on0 a → ctx a w → ctx a w' → tabOf a w = tabOf a w'
  hcb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w
  hcq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → ctx b' w → ctx a w
  hce : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → ctx b' w → ctx a w
  htabb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  htabq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  htab : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  hN : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  inside : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
    reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl

/-- The driver's batching, where the record holds the batching kind's own block, is a draw with the
one move. -/
theorem batchB_drawMoves {H : First.Blocks S Claim} {l : ℕ} {sub : First.ModelPart} {L : Link S Claim}
    (h : First.linkAt H l sub = some L) (p : Where)
    (hK : H.batch ⟨1, some l, (First.kindsBeforeBatching sub (l == 0)).length + 1, .K9⟩ =
      some (K9.batch atS p)) :
    DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB := by
  obtain ⟨batch, hb, hL⟩ := (Shape.linkAt_shape h).2.2.1
  obtain rfl : K9.batch atS p = batch := Option.some.inj (hK.symm.trans hb)
  intro ft s rs cols s' k hs
  unfold Link.batchB at hs
  rw [hL] at hs
  exact batch_drawMoves atS p (claimsInBy L.each L.hear L.order) ft s rs cols s' k hs

/-- **hb₃ AND THE GUARD, AT A RECORD THAT HOLDS THE ONE EQUATION IN A DRESS**: where what the record
holds at the place ⟨1, l, n + 3, K9⟩ has the one equation's rounds and decision (its name, its place
and its test on the plan are free: so the batching kind's closeOf lays it), the head of the
segment's closing has no round, and a yes of its step is a yes of the one equation's. -/
theorem head_is_equation {Cl : Type} {H : First.Blocks S Cl} {l : ℕ} {sub : First.ModelPart}
    {L : Link S Cl} (h : First.linkAt H l sub = some L) (pw : Where) (e : Block S Cl)
    (hE : H.block ⟨1, some l, (First.kindsBeforeBatching sub (l == 0)).length + 3, .K9⟩ = some e)
    (hr : e.rounds = (K9.oneEquation (Cl := Cl) atS pw).rounds)
    (hd : e.decide = (K9.oneEquation (Cl := Cl) atS pw).decide) :
    ∃ b₃, L.close.head? = some b₃ ∧ b₃.rounds = [] ∧
      ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
        (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x := by
  refine ⟨{ e with place := ⟨1, some l, (First.kindsBeforeBatching sub (l == 0)).length + 3, .K9⟩ }, ?_, hr,
    fun ft s rs cols x hx => ?_⟩
  · rw [close_head h]
    unfold First.blockAt
    rw [hE]
    rfl
  · unfold Block.step at hx ⊢
    rw [← hr, ← hd]
    exact hx

/-- **RunsAsk GIVES JoinAsks** at the segment's own two blocks and their moves. -/
theorem joinAsks_of_runs {L : Link S Claim} {φ : S → α} {Ok : α × Option Pub9 → Prop}
    {Fu : S → Prop} {p pw : Where}
    {rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)} {d N : ℕ} {b₃ : Block S Claim}
    {pb pq pe : Piece (ckP .two) F S Claim W} {on0 on1 on2 on3 : S × F.E.Str → Prop}
    {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}
    (A : RunsAsk L φ Ok Fu p pw rl d N b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    JoinAsks φ Ok Fu p pw (moves₁ L rl) (moves₂ L) d N L.batchB L.behindB b₃ pb pq pe on0 on1 on2
      on3 tabOf ctx := by
  have HF := fitsM_atS (K := Cb.Gl.E) φ A.hφ Ok Fu p
  refine
    { hφ := A.hφ, hd := A.hd, hms := ?_, hkd := ?_, quiet := ?_
      hb₁ := A.hb₁, hb₂ := behind_isMoves atS L, hb₃ := A.hb₃
      hend := A.hend, hok := A.hok, hpb := A.hpb, hpq := A.hpq, hpe := A.hpe
      hextb := A.hextb, hextq := A.hextq, hexte := A.hexte, hds := A.hds, hbk := A.hbk
      hcap := A.hcap, hready := A.hready, h01 := A.h01, h12 := A.h12, hon3 := A.hon3
      hs1 := A.hs1, hpin := A.hpin, hcb := A.hcb
      hcq := A.hcq, hce := A.hce, htabb := A.htabb, htabq := A.htabq, htab := A.htab
      hN := A.hN, inside := A.inside }
  · intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain rfl := List.mem_singleton.1 hm
      exact claimsInBy_addOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF L.each L.hear L.order rl
        A.hrl A.hrun
    · obtain rfl := List.mem_singleton.1 hm
      exact ⟨runBehind_quietOk atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF L A.hquiet, fun _ _ _ => rfl,
        fun _ => rfl⟩
  · intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain rfl := List.mem_singleton.1 hm
      refine claimsInBy_door atS L.each L.hear L.order fun r hr => ?_
      rw [← A.hrl] at hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      exact A.hrund r' hr'
    · obtain rfl := List.mem_singleton.1 hm
      exact runBehind_door atS L A.hquietd
  · intro m hm
    obtain rfl := List.mem_singleton.1 hm
    exact ⟨_, rfl⟩

/-- **THE LAW OF A LINK, FROM ONE DUTY A RUN.** -/
theorem link_row_runs (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where) (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) (d N j : ℕ)
    (b₃ : Block S Claim) (pb pq pe : Piece (ckP .two) F S Claim W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (A : RunsAsk L φ Ok Fu p pw rl d N b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    EachGoodIn (onJ on0 on1 on2 on3 j)
      (relJ (O9 φ Ok Fu) (moves₁ L rl) (moves₂ L) N tabOf ctx j) j [pb, pq, pe] :=
  K9L.inMoves α W Claim F φ Ok Fu p pw (moves₁ L rl) (moves₂ L) d N j L.batchB L.behindB b₃
    pb pq pe on0 on1 on2 on3 tabOf ctx (joinAsks_of_runs A)

/-- **Where the three stand**: in a list ps that holds one piece for each block of the segment's
flat list, the pieces at the numbers n + 1, n + 2, n + 3 hold the batching, the frame's block behind
it and the head of the closing: the three ties (RunsAsk's hpb, hpq, hpe) follow from the list. -/
theorem pieces_at {l : ℕ} {sub : First.ModelPart} {L : Link S Claim}
    (h : SegAt l sub L) (ps : List (Piece (ckP .two) F S Claim W))
    (hps : ps.map (·.b) = L.blocksInOrder.map below) (pb pq pe : Piece (ckP .two) F S Claim W)
    (b₃ : Block S Claim) (h3 : L.close.head? = some b₃)
    (h1 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 1]? = some pb)
    (h2 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 2]? = some pq)
    (h4 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 3]? = some pe) :
    pb.b = below L.batchB ∧ pq.b = below L.behindB ∧ pe.b = below b₃ := by
  have hn := h.hear
  have at_ : ∀ (k : ℕ) (p : Piece (ckP .two) F S Claim W), ps[k]? = some p →
      (L.blocksInOrder[k]?).map below = some p.b := by
    intro k p hk
    have e : (ps.map (·.b))[k]? = some p.b := by rw [List.getElem?_map, hk]; rfl
    rw [hps, List.getElem?_map] at e
    exact e
  obtain ⟨r, hr⟩ : ∃ r, L.close = b₃ :: r := by
    cases hc : L.close with
    | nil => rw [hc] at h3; exact nomatch h3
    | cons b r =>
      rw [hc] at h3
      exact ⟨r, by rw [Option.some.inj h3]⟩
  have hf : L.blocksInOrder =
      (L.laidB :: L.hear) ++ (L.batchB :: L.behindB :: b₃ :: (r ++ [L.clearedB])) := by
    rw [Link.flat_eq, hr]
    simp [Link.mid]
  have hlen : (L.laidB :: L.hear).length = (First.kindsBeforeBatching sub (l == 0)).length + 1 := by
    rw [List.length_cons, hn]
  refine ⟨?_, ?_, ?_⟩
  · have e := at_ _ pb h1
    rw [hf, ← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at e
    exact (Option.some.inj e).symm
  · have e := at_ _ pq h2
    rw [hf, show (First.kindsBeforeBatching sub (l == 0)).length + 2 = (L.laidB :: L.hear).length + 1 by
      rw [hlen], List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at e
    exact (Option.some.inj e).symm
  · have e := at_ _ pe h4
    rw [hf, show (First.kindsBeforeBatching sub (l == 0)).length + 3 = (L.laidB :: L.hear).length + 2 by
      rw [hlen], List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at e
    exact (Option.some.inj e).symm

/-- **THE LAW OF A LINK AT THE SEGMENT's OWN PLACES**: pieces_at and link_row_runs joined. b₃: the
head of the segment's closing; ps holds one piece for each block of the segment's flat list; i:
where the segment's row begins in the chain's. Whoever shows RunsAsk may take the three ties as
given. -/
theorem link_row_at (l : ℕ) (sub : First.ModelPart) (L : Link S Claim)
    (h : SegAt l sub L) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where) (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) (d N i : ℕ)
    (b₃ : Block S Claim) (h3 : L.close.head? = some b₃)
    (ps : List (Piece (ckP .two) F S Claim W)) (hps : ps.map (·.b) = L.blocksInOrder.map below)
    (pb pq pe : Piece (ckP .two) F S Claim W)
    (h1 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 1]? = some pb)
    (h2 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 2]? = some pq)
    (h4 : ps[(First.kindsBeforeBatching sub (l == 0)).length + 3]? = some pe)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (A : pb.b = below L.batchB → pq.b = below L.behindB → pe.b = below b₃ →
      RunsAsk L φ Ok Fu p pw rl d N b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    EachGoodIn (onJ on0 on1 on2 on3 (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)))
      (relJ (O9 φ Ok Fu) (moves₁ L rl) (moves₂ L) N tabOf ctx
        (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)))
      (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)) [pb, pq, pe] := by
  obtain ⟨t1, t2, t3⟩ := pieces_at h ps hps pb pq pe b₃ h3 h1 h2 h4
  exact link_row_runs L φ Ok Fu p pw rl d N _ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx
    (A t1 t2 t3)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.batchB_drawMoves
#print axioms VerifiableInference.Desc.LinkJoin.head_is_equation
#print axioms VerifiableInference.Desc.LinkJoin.segAt_of_linkAt
#print axioms VerifiableInference.Desc.LinkJoin.joinAsks_of_runs
#print axioms VerifiableInference.Desc.LinkJoin.link_row_runs
#print axioms VerifiableInference.Desc.LinkJoin.pieces_at
#print axioms VerifiableInference.Desc.LinkJoin.link_row_at
