-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/SendRan.lean: where the Lean verifier's sending block ends well on a view, it
has taken two rounds off the view: the round of the seed, which holds no item, and the round of
the answers, which holds the answers and nothing else.

A sub-proof's later oracle messages (the reads of a smallness test, then its digits) are received by
sendVerify (OnBytes/Iop/Send.lean), with a round of its own for the answers. The laws on its calls
are the library's (OnBytes/Slice/BlkSendRun.lean, OnBytes/Iop/GroundLaws.lean); the two loops over
the answers are followed on a view in OnBytes/Tie/Pv/Switch/LocView.lean, for the code switch, whose
first half is the same sending. Here they are put together for the sending by itself. Then, as in
OnBytes/Tie/Pv/Tail/RngView.lean: if the rounds not yet begun are the view that is made of a written
transcript (rvT, OnBytes/Maker/Trees.lean), the seeds are cut out of the elements among the typed
values of the first written verifier message, and the answers are the items of the second written
prover's message. Statements and proofs.

Main names:
  `SendTook c notices ids c' r₁ r₂ shapes seeds ans`: what a run has taken: the two rounds; the
    numbers of the new oracle messages; the shapes of those that are sampled; the seeds that were
    cut out of what the first round drew, by the numbers of bits and of answers that follow from
    these shapes, none with the factor 0; the answers that the second round held, as many as the
    shapes say.
  `sendVerify_view`: a run from a context without an open message has such a record, and ends in a
    context without an open message.
  `sendVerify_rvT`: on the view of a written transcript: the same, with the two rounds named: what
    the first drew is the record that the kit with hash blocks makes of the first written verifier
    message; the second's items are those of the second written prover's message; the rounds not
    yet begun are the view of the rest.
  `seed_elems`: the elements out of which the seeds are cut, read in the library's field, are the
    elements among the typed values of the first written verifier message.

Limits: nothing on a dry run or on a run that fails. The roots of the oracle messages are no items
of a view's round: the channel counts them; which words stand behind a root is not said here.
Which answer is which sample row's target is not followed here. That a run reaches the block with
just these rounds not yet begun, and that the file's accept has passed the rounds' tests of work,
is for whoever cuts the file's run. No map to a typed round is laid here.
-/
import OnBytes.Tie.Pv.Switch.LocView
import OnBytes.Tie.Pv.Tail.BatRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Switch

/-- What a run of the sending block has taken off a view. -/
structure SendTook (c : Ctx) (notices : Array OracleNotice) (ids : Array Nat) (c' : Ctx)
    (r₁ r₂ : Fmt.RoundView) (shapes : List OracleShape) (seeds : List SampleSeed) (ans : List E) :
    Prop where
  /-- the two rounds, and what is left -/
  left   : c.ch.left = r₁ :: r₂ :: c'.ch.left
  clean  : PscRun.Clean c'
  /-- the new oracle messages are numbered behind the old ones -/
  idsAre : ids = (Array.range notices.size).map (· + c.st.oracles.size)
  /-- the shapes of those that are sampled, in the order of sending -/
  shaped : (todoOf (stSent c.st notices) ids).mapM
    (fun o => ((stSent c.st notices).oracles[o]?).map (·.shape)) = some shapes
  /-- the round of the seed holds no item -/
  none₁  : r₁.vals = []
  /-- the seeds are cut out of the elements that it drew, by the shapes' own numbers -/
  cut    : Send.seedsOf
    (shapes.foldl (fun b s => max b (Send.cube (stSent c.st notices).codes s).bits) 0)
    (shapes.foldl (fun a s => max a s.answers) 0) (r₁.drawn.elems.map E.ofTriple) = some seeds
  factor : (seeds.all fun s => !isZeroE s.beta) = true
  /-- the round of the answers holds the answers and nothing else -/
  vals₂  : r₂.vals = ans.map fun x => Fmt.ItemValue.answer x.triple
  count  : ans.length =
    (((todoOf (stSent c.st notices) ids).zip shapes).map fun x => x.2.answers).sum

/-- A run of the sending block, with a round of its own for the answers, on a view. -/
theorem sendVerify_view (notices : Array OracleNotice) (ids : Array Nat) (c c' : Ctx)
    (hc : PscRun.Clean c) (h : (sendVerify notices true).Yields c ids c') :
    ∃ r₁ r₂ shapes seeds ans, SendTook c notices ids c' r₁ r₂ shapes seeds ans := by
  obtain ⟨c1, h1, h2⟩ := sendVerify_inv _ _ _ _ _ h
  obtain ⟨lay, -, -, hids, e1⟩ := receiveOracles_inv _ _ _ _ hc.1 h1
  have p0 : c1.ch.pending = c.ch.pending := by rw [e1]; rfl
  have d0 : c1.ch.dry = false := by rw [e1]; exact hc.1
  have st0 : c1.st = stSent c.st notices := by rw [e1]
  obtain ⟨shapes, drawn, seeds, c2, c3, hsh, hseed, hcut, hnz, hloop, hlast⟩ :=
    verify_inv _ _ _ _ d0 h2
  rw [st0] at hsh hcut hloop
  obtain ⟨_, _, r₁, rest, _, _, _, s1, s2, s3, _, _, _, s4, _, _, _, _, _, s5, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ d0 hseed
  obtain ⟨ans, la, ta, dA⟩ := sampleSteps_view _ _ _ _ _ s5 hloop
  have hlast' : (Blk.closeEmpty "SEND answer").Yields c3 () c' := by simpa using hlast
  unfold Blk.closeEmpty at hlast'
  obtain ⟨d2, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 hlast'
  obtain ⟨-, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a4
  obtain ⟨r, t, _, t1, t2, -, -, -, hcl, hl⟩ :=
    PscRun.close_view _ _ _ _ _ _ dA ((Blk.yields_iff _ _ _ _).1 h4)
  have t1' : c3.ch.pending = r :: t := t1
  have hpc : c.ch.pending = c.ch.left := by
    unfold Chan.pending
    rw [hc.2]
  rw [s4] at ta
  rw [p0, hpc] at s1
  rw [s3] at hcut
  rcases ta with ⟨rfl, e⟩ | ⟨r', t', gs, a1, a2, a3⟩
  · rw [t1'] at e
    exact ⟨r₁, r, shapes, seeds, [], by rw [s1, ← e, hl], hcl, hids, hsh, s2, hcut, hnz, t2, la⟩
  · rw [t1'] at a3
    obtain ⟨e1', e2'⟩ := List.cons.inj a3
    have g0 : gs = [] := by
      have := congrArg Fmt.RoundView.vals e1'
      rw [t2] at this
      exact this.symm
    rw [g0, List.append_nil] at a2
    exact ⟨r₁, r', shapes, seeds, ans, by rw [s1, a1, ← e2', hl], hcl, hids, hsh, s2, hcut, hnz,
      a2, la⟩

/-- The elements out of which the seeds are cut, read in the library's field. -/
theorem seed_elems (d : RDT) (w : (roundT (Run.ckP .two) d).up.Chal) :
    (((Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) w)).elems.map
      E.ofTriple).map Reading.gl.val = elemsV _ (valsOf (rdOf d) w) := elems_read d w

/-- The sending block on the view of a written transcript. -/
theorem sendVerify_rvT (notices : Array OracleNotice) (ids : Array Nat) (x x' : Ctx)
    (hc : PscRun.Clean x) (h : (sendVerify notices true).Yields x ids x') (d₁ d₂ : RDT)
    (ds : List RDT) (m₁ : (roundT (Run.ckP .two) d₁).up.Msg)
    (w₁ : (roundT (Run.ckP .two) d₁).up.Chal) (m₂ : (roundT (Run.ckP .two) d₂).up.Msg)
    (w₂ : (roundT (Run.ckP .two) d₂).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds))
    (hl : x.ch.left = rvT (Run.ckP .two) (d₁ :: d₂ :: ds)
      ((m₁, w₁, m₂, w₂, τ) : Tr (uLT (Run.ckP .two) (d₁ :: d₂ :: ds)))) :
    ∃ shapes seeds ans,
      SendTook x notices ids x'
        ⟨Run.PQ.PlainOf.gots d₁.items (GPlain.old (b := d₁.entry.work) m₁.2),
          (Run.ckP .two).dr d₁.entry d₁.kind (GChal.old (b := d₁.entry.work) w₁)⟩
        ⟨Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2),
          (Run.ckP .two).dr d₂.entry d₂.kind (GChal.old (b := d₂.entry.work) w₂)⟩
        shapes seeds ans ∧
      x'.ch.left = rvT (Run.ckP .two) ds τ := by
  obtain ⟨r₁, r₂, shapes, seeds, ans, T⟩ := sendVerify_view notices ids x x' hc h
  obtain ⟨rfl, e⟩ := List.cons.inj (hl.symm.trans T.left)
  obtain ⟨rfl, e'⟩ := List.cons.inj e
  exact ⟨shapes, seeds, ans, T, e'.symm⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.sendVerify_view
#print axioms OnBytes.Tie.Pv.Tail.seed_elems
#print axioms OnBytes.Tie.Pv.Tail.sendVerify_rvT
