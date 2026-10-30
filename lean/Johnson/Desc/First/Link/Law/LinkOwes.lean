-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkOwes.lean: WHAT IS LEFT OF THE LAW OF A LINK AT A SEGMENT: ONE
STRUCTURE, A FIELD A DEBT, EACH WITH THE ROLE THAT OWES IT IN ITS DOCSTRING; and one theorem:
whoever has them all has the three pieces good in a row at the segment's own places.

Why. `link_row_at` (Johnson/Desc/First/Link/Law/LinkJoinRuns.lean) and the tools of LinkJoinPay.lean
pay, of `LinkJoin.JoinAsks`' clauses, all that follows from the driver's own text: the frame's block
behind the batching is a move; the pieces' ties; the list of runs. What is left is owed elsewhere.
This file is the list: each field's docstring begins «OWES ‹a role›:», so that a program can print
it. Every field on a block or a run starts from a yes: so a record that lays its blocks and runs
behind guards which only add refusals can meet them.

What is said.
  `OwesBlocks`, `OwesPieces`, `OwesCaller`, `OwesRuns`, `OwesNumbers`, `OwesFull`, `OwesConds`,
    `OwesLetters`: EIGHT LISTS OF DEBTS, A LIST A SORT OF DEBTOR: so that whoever pays a list hands
    one term, and what is left is the other lists. `LinkOwes sub L …`: the eight together.
    `runsAsk_of_owes`: it gives `RunsAsk` at the list of runs that the link itself makes.
    `link_law_owes`: **`LinkOwes` gives `EachGoodIn (onJ …) (relJ …) j [pb, pq, pe]`**, with the
    moves `moves₁ L (rlOf L tmOf lenOf)` and `moves₂ L`.

What ties the pieces to the link: two equations on L's own blocks (hpb, hpq): the first two pieces'
blocks are L's batching and the frame's block behind it, each with the test on the words in front.
THE THIRD BLOCK b₃ IS A LETTER: the law knows of it that a yes of its step is the one equation's
(hb₃) and that the third piece holds it (hpe). That b₃ is the head of L's closing is a fact on the
description at hand, shown and spent where the pieces' numbers meet the blocks; no proof here would
spend it. NOTHING HERE TIES THE NUMBERS j, j + 1, j + 2 IN A ROW TO L's PLACE IN A CHAIN: that is
the cut's. Where a list holds one piece for each block of L's flat list, `pieces_at`
(LinkJoinRuns.lean) pays hpb, hpq, hpe at the head of L's closing.

Limits. AN IMPLICATION: `LinkOwes` is shown of no record of the protocol (a toy has all eight lists,
33 fields: MemberOwes.lean). The letters φ, Ok, Fu, tabOf, ctx, on0, on1, on2, on3 are free here:
they are to be chosen once for all kinds. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkJoinPay

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

/-- **THE DEBTS ON THE RECORD OF BLOCKS.** -/
structure OwesBlocks (L : Link S Claim) (p pw : Where) (b₃ : Block S Claim) :
    Prop where
  /-- OWES the record of blocks: the segment's batching is a draw with one move behind it: add what
  the link's own gatherer returns (from a yes: a block behind a guard meets it) -/
  hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  /-- OWES the record of blocks: a yes of b₃'s step is a yes of the one equation's -/
  hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x

/-- **THE DEBTS ON THE THREE PIECES.** -/
structure OwesPieces (L : Link S Claim) (p : Where) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) :
    Prop where
  /-- OWES the maker of the pieces: the first piece's block is the segment's batching, with the test
  on the words in front -/
  hpb : pb.b = below L.batchB
  /-- OWES the maker of the pieces: the second's is the frame's block behind the batching -/
  hpq : pq.b = below L.behindB
  /-- OWES the maker of the pieces: the third's is b₃ -/
  hpe : pe.b = below b₃
  /-- OWES the maker of the pieces: the first piece's one round -/
  hds : pb.ds = [k9Round p]
  /-- OWES the maker of the pieces: nothing is put back -/
  hbk : pb.back = []

/-- **THE DEBTS ON THE FAMILY THAT THE RULE OF COMPOSITION IS CALLED AT.** -/
structure OwesCaller (pb pq pe : Piece (ckP .two) F S Claim W) :
    Prop where
  /-- OWES the caller of the rule of composition: the first piece's extractor is the identity -/
  hextb : ∀ a τ w, pb.ext a τ w = w
  /-- OWES the caller of the rule of composition: the second's -/
  hextq : ∀ a τ w, pq.ext a τ w = w
  /-- OWES the caller of the rule of composition: the third's -/
  hexte : ∀ a τ w, pe.ext a τ w = w
  /-- OWES the caller of the rule of composition: its error is the cap at 128 -/
  hcap : pb.err = Err.cap 128 (uLT (ckP .two) pb.ds)

/-- **THE DEBTS ON THE RUNS, AN ENTRY OF THE ORDERS AT A TIME, AND ON φ.** -/
structure OwesRuns (sub : First.ModelPart) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) :
    Prop where
  /-- OWES the choice of φ: φ does not see what the batching's lens
  writes -/
  hφ : ∀ s a, φ (atS.set s a) = φ s
  /-- OWES each kind's law, an entry of the order at a time: RunOk of the run that stands there -/
  hpay : ∀ o ∈ First.orderOf sub, ∀ run, At L o run →
    RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) run (tmOf o) (lenOf o)
  /-- OWES each kind's law, an entry of the order at a time: the run keeps the door -/
  hpayd : ∀ o ∈ First.orderOf sub, ∀ run, At L o run →
    ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁
  /-- OWES each kind's law, an entry of the order behind the batching at a time: QuietOk -/
  hquiet : ∀ o ∈ First.orderAfterOf sub, ∀ run, AtAfter L o run →
    QuietOk atS (O9 (K := Cb.Gl.E) φ Ok Fu) (Fx9 φ Ok) run
  /-- OWES each kind's law, an entry of the order behind the batching at a time: the door -/
  hquietd : ∀ o ∈ First.orderAfterOf sub, ∀ run, AtAfter L o run →
    ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁

/-- **THE DEBTS ON THE NUMBERS.** -/
structure OwesNumbers (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d : ℕ) :
    Prop where
  /-- OWES the batching kind's law: the bound on the degree is below the field's count -/
  hd : d ≤ 2 ^ 60
  /-- OWES the assembly of the kinds' laws: the exponents of all the runs' terms in a row are apart
  and below d: from each kind's «my terms' exponents are n .. n + len - 1» and the batching kind's
  d -/
  hok : ∀ s y, k9OnA s = true ∧ Ok (fixed9 φ s) →
    Desc.TermsOk Cb.Gl.E
      (termsOf (fixed9 φ s) y (moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L) 0) d

/-- **THE DEBTS ON THE STATE BEHIND THE LAST MOVE.** -/
structure OwesFull (L : Link S Claim) (Fu : S → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) :
    Prop where
  /-- OWES the smallness test's law: behind the last move the state is
  good and FULL -/
  hend : ∀ s s' cls, good9 s →
    MovesYes atS ((moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L).map (·.move)) s s' cls →
    good9 s' ∧ Fu s'

/-- **THE DEBTS ON THE CONDITIONS AT THE FOUR BOUNDARIES.** -/
structure OwesConds (φ : S → α) (Ok : α × Option Pub9 → Prop) (N : ℕ)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop) :
    Prop where
  /-- OWES the table of conditions between blocks: in front of the batching the book-keeping holds
  and Ok holds of the snapshot. EVERY KIND's DEMAND ON THE SNAPSHOT COMES DUE HERE: that the slots
  which its forms name, and those under which its readers look, are filled in it -/
  hready : ∀ a, on0 a → k9OnA a.1 = true ∧ Ok (fixed9 φ a.1)
  /-- OWES the choice of the conditions on1 and on2, with the batching kind's law: the condition
  behind the batching follows from the one in front and the batching's yes -/
  h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b'
  /-- OWES the choice of the conditions on1 and on2, with the batching kind's law: the like over the
  frame's block -/
  h12 : ∀ b τ c, on1 b → pq.ior.red.out b τ = some c → on2 c
  /-- OWES the choice of the conditions on1 and on2, with the batching kind's law: behind the
  batching a part is there -/
  hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true
  /-- OWES the table of conditions between blocks: at most N oracle messages -/
  hN : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  /-- OWES the table of conditions between blocks: every block of a required
  array lies inside it -/
  inside : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
    reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl
  /-- OWES the batching kind's law with the table of conditions: what the three hand on is what the
  closing kind's law asks in front of itself -/
  hon3 : ∀ c τ x, on2 c → pe.ior.red.out c τ = some x → on3 x

/-- **THE DEBTS ON THE FILE's LETTERS.** -/
structure OwesLetters (pb pq pe : Piece (ckP .two) F S Claim W)
    (on0 on1 on2 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
    (ctx : S × F.E.Str → W → Prop) :
    Prop where
  /-- OWES the choice of the file's letters: two witnesses with ctx name one table -/
  hpin : ∀ a w w', on0 a → ctx a w → ctx a w' → tabOf a w = tabOf a w'
  /-- OWES the choice of the file's letters: ctx rides backward over the first piece -/
  hcb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w
  /-- OWES the choice of the file's letters: over the second -/
  hcq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → ctx b' w → ctx a w
  /-- OWES the choice of the file's letters: over the third -/
  hce : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → ctx b' w → ctx a w
  /-- OWES the choice of the file's letters: the tables stay over the first piece -/
  htabb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  /-- OWES the choice of the file's letters: over the second -/
  htabq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  /-- OWES the choice of the file's letters: over the third -/
  htab : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w

/-- **WHAT IS LEFT OF THE LAW OF A LINK**: eight lists of debts, a list a sort of debtor. -/
structure LinkOwes (sub : First.ModelPart) (L : Link S Claim)
    (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
    (ctx : S × F.E.Str → W → Prop) : Prop where
  blocks : OwesBlocks L p pw b₃
  pieces : OwesPieces L p b₃ pb pq pe
  caller : OwesCaller pb pq pe
  runs : OwesRuns sub L φ Ok Fu tmOf lenOf
  numbers : OwesNumbers L φ Ok tmOf lenOf d
  full : OwesFull L Fu tmOf lenOf
  conds : OwesConds φ Ok N pb pq pe on0 on1 on2 on3
  letters : OwesLetters pb pq pe on0 on1 on2 tabOf ctx

/-- **LinkOwes GIVES RunsAsk**, at the list of runs that the link itself makes. -/
theorem runsAsk_of_owes {l : ℕ} {sub : First.ModelPart} {L : Link S Claim}
    (h : SegAt l sub L) {φ : S → α} {Ok : α × Option Pub9 → Prop} {Fu : S → Prop}
    {p pw : Where}
    {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {lenOf : ℕ × String → α × Option Pub9 → ℕ} {d N : ℕ} {b₃ : Block S Claim}
    {pb pq pe : Piece (ckP .two) F S Claim W}
    {on0 on1 on2 on3 : S × F.E.Str → Prop}
    {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}
    (A : LinkOwes sub L φ Ok Fu p pw tmOf lenOf d N b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    RunsAsk L φ Ok Fu p pw (rlOf L tmOf lenOf) d N b₃ pb pq pe on0 on1 on2 on3 tabOf
      ctx := by
  obtain ⟨eo, ea⟩ := order_at h
  exact
    { hb₁ := A.blocks.hb₁, hrl := rlOf_runs L tmOf lenOf
      hrun := rlOf_runOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) L tmOf lenOf
        (by rw [eo]; exact A.runs.hpay)
      hrund := rlOf_door atS L tmOf lenOf (by rw [eo]; exact A.runs.hpayd)
      hquiet := by rw [ea]; exact A.runs.hquiet
      hquietd := by rw [ea]; exact A.runs.hquietd
      hφ := A.runs.hφ, hd := A.numbers.hd, hb₃ := A.blocks.hb₃, hend := A.full.hend
      hok := A.numbers.hok, hpb := A.pieces.hpb, hpq := A.pieces.hpq, hpe := A.pieces.hpe
      hextb := A.caller.hextb, hextq := A.caller.hextq, hexte := A.caller.hexte
      hds := A.pieces.hds, hbk := A.pieces.hbk, hcap := A.caller.hcap
      hready := A.conds.hready, h01 := A.conds.h01, h12 := A.conds.h12, hon3 := A.conds.hon3
      hs1 := A.conds.hs1, hpin := A.letters.hpin, hcb := A.letters.hcb, hcq := A.letters.hcq
      hce := A.letters.hce, htabb := A.letters.htabb, htabq := A.letters.htabq
      htab := A.letters.htab, hN := A.conds.hN, inside := A.conds.inside }

/-- **THE LAW OF A LINK, FROM WHAT IS LEFT OF IT.** j: the first piece's number in its row. -/
theorem link_law_owes (l : ℕ) (sub : First.ModelPart) (L : Link S Claim)
    (h : SegAt l sub L) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N j : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (A : LinkOwes sub L φ Ok Fu p pw tmOf lenOf d N b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    EachGoodIn (onJ on0 on1 on2 on3 j)
      (relJ (O9 φ Ok Fu) (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) N tabOf ctx j) j [pb, pq, pe] :=
  link_row_runs L φ Ok Fu p pw (rlOf L tmOf lenOf) d N j b₃ pb pq pe on0 on1 on2 on3 tabOf
    ctx (runsAsk_of_owes h A)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.runsAsk_of_owes
#print axioms VerifiableInference.Desc.LinkJoin.link_law_owes
