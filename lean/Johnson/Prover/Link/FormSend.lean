-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSend.lean: a sending of one sampled oracle message with one answer, with
others in the same prover's message that are not sampled (`sendP` over `groundG`,
Johnson/Desc/Ground/Calls.lean), returns a value, from its guards: general in the state, the notices
and the two rounds.

Main names (namespace `Johnson.Prover.Link`).
  `recv_yes`, `admit_yes`   the ground's two functions return their effects where their named
      clauses hold and the trees, or the pad's places, can be made
  `seeds_one`   the drawn elements are cut into one seed where just one stands behind the point
  `sendOne_yes`   the sending returns the messages' numbers, the elements drawn, the answer, "one
      item taken" and the state behind it, written out in the soundness side's terms (`stSent`,
      `admitted`, `bookSentP`)

The converse of `sendOne_ok` (Johnson/Desc/K12/Law/SwUnfold.lean).

Limits. Asked: the clauses of `recvL` and `admitL`; that the trees, the sample row's left side and
the pad's places can be made; the first round shows no item and draws no position and no matrix
entry; behind the point's coordinates it draws one element, whose words are not all 0; the second
round's first item is the answer. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open H2K.Sw
open _root_.Desc.Plain (DState GPar sendP sampleLoop rowsFor answersOf)

/-- The ground's receiving returns its effect. -/
theorem recv_yes (ft : Nat) (d : DState Unit) (sent : Array OracleNotice) (lay : TreeLay)
    (hok : Ground.ok (Ground.recvL d.st d.book sent) = true)
    (hl : Own.treesMade d.st.codes sent = some lay) :
    Ground.recvP ft d sent = some ((Array.range sent.size).map (· + d.st.oracles.size),
      { d with st := stSent d.st sent, book := bookSentP ft d.roots d.st d.book sent lay
               roots := d.roots + lay.shapes.size }) := by
  unfold Ground.recvP
  rw [if_pos hok, hl]
  rfl

/-- The ground's admitting returns its effect. -/
theorem admit_yes (d : DState Unit) (o : Nat) (rows : Array Row) (x : OnBytes.Oracle)
    (places : List PadPlace) (hok : Ground.ok (Ground.admitL d.st o rows) = true)
    (hx : d.st.oracles[o]? = some x) (hp : Own.padMade d.st.codes x.shape = some places) :
    Ground.admitP d o rows = some { d with st := admitted d.st o x.shape places rows } := by
  unfold Ground.admitP
  rw [if_pos hok, hx]
  simp only [hp, bind, Option.bind]

/-- One seed. -/
theorem seeds_one (bits : Nat) (l : List E) (beta : E) (h : l.drop bits = [beta]) :
    Own.seedsMade bits 1 l = some [⟨l.take bits, beta⟩] := by
  show (match l.drop bits with
    | [] => none
    | beta :: rest =>
      (Own.seedsMade bits 0 rest).map fun t => (⟨l.take bits, beta⟩ : SampleSeed) :: t) = _
  rw [h]
  rfl

/-- **The sending returns a value.** -/
theorem sendOne_yes (p : GPar) (d : DState Unit) (N : OracleNotice) (others : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (lay : TreeLay) (beta alpha : E) (row : Row) (places : List PadPlace)
    (vs : List Fmt.ItemValue) (h1 : N.shape.answers = 1) (ho : ∀ n ∈ others, n.shape.answers = 0)
    (hrecv : Ground.ok (Ground.recvL d.st d.book (#[N] ++ others)) = true)
    (htrees : Own.treesMade d.st.codes (#[N] ++ others) = some lay)
    (hv₁ : r₁.vals = []) (hp₁ : r₁.drawn.poss = []) (ht₁ : r₁.drawn.trits = [])
    (hseed : (r₁.drawn.elems.map E.ofTriple).drop (Send.cube d.st.codes N.shape).bits = [beta])
    (hnz : Own.allZero beta = false)
    (hform : Own.formMade d.st.codes N.shape d.st.oracles.size
      ⟨(r₁.drawn.elems.map E.ofTriple).take (Send.cube d.st.codes N.shape).bits, beta⟩ 0 = some row)
    (hpad : Own.padMade d.st.codes N.shape = some places)
    (hv₂ : r₂.vals = .answer alpha.triple :: vs)
    (hadmit : Ground.ok (Ground.admitL (stSent d.st (#[N] ++ others)) d.st.oracles.size
      #[{ row with target := alpha }]) = true) :
    sendP Ground.groundG p false d (#[N] ++ others) r₁ r₂ =
      some ((Array.range (#[N] ++ others).size).map (· + d.st.oracles.size),
        r₁.drawn.elems.map E.ofTriple, [alpha], 1,
        { d with
          st := admitted (stSent d.st (#[N] ++ others)) d.st.oracles.size N.shape places
            #[{ row with target := alpha }]
          book := bookSentP p.firstTree d.roots d.st d.book (#[N] ++ others) lay
          roots := d.roots + lay.shapes.size }) := by
  have htodo := todo_one d.st N others (by omega) ho
  unfold todoOf at htodo
  have hlen : (r₁.drawn.elems.map E.ofTriple).length =
      (Send.cube d.st.codes N.shape).bits + 1 := by
    have := congrArg List.length hseed
    rw [List.length_drop] at this
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hcodes : (stSent d.st (#[N] ++ others)).codes = d.st.codes := rfl
  have had := admit_yes
    { d with st := stSent d.st (#[N] ++ others)
             book := bookSentP p.firstTree d.roots d.st d.book (#[N] ++ others) lay
             roots := d.roots + lay.shapes.size }
    d.st.oracles.size #[{ row with target := alpha }] { shape := N.shape } places hadmit
    (sent_first d.st N others) hpad
  have had' : Ground.admitP
      { d with st := stSent d.st (#[N] ++ others)
               book := bookSentP p.firstTree d.roots d.st d.book (#[N] ++ others) lay
               roots := d.roots + lay.shapes.size }
      d.st.oracles.size ((#[] : Array Row).push { row with target := alpha }) = _ := had
  unfold sendP
  simp only [Ground.groundG, recv_yes p.firstTree d (#[N] ++ others) lay hrecv htrees, bind,
    Option.bind, htodo, List.mapM_cons, List.mapM_nil, sent_first, Option.map_some, pure,
    List.foldl_cons, List.foldl_nil, h1, Nat.zero_max, Nat.zero_add, hcodes,
    seeds_one _ _ beta hseed, answersOf, hv₂, List.take_succ_cons, List.take_zero,
    E.ofTriple_triple, hv₁, hp₁, ht₁, hlen, hnz, Own.rising, List.isEmpty_nil, List.isEmpty_cons,
    List.all_cons, List.all_nil, List.length_cons, List.length_nil, Option.getD_some,
    Bool.not_false, Bool.and_true, Bool.true_and, Bool.true_or,
    Nat.mul_one, beq_self_eq_true, if_true, List.zip_cons_cons, List.zip_nil_left, sampleLoop,
    show List.range 1 = [0] from rfl, rowsFor, List.getElem?_cons_zero, hform, had']

end Johnson.Prover.Link
