--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/MarginalLaw.lean: of each of the eight parts of the sub-protocol
"the output head's own rounds" (kind K6), played alone: EACH PART's MARGINAL LAW, OVER SPENT RUNS TAKEN
AS FRESH, IS THE SAME AT EVERY STATE of the prover's run before the part. The law is taken over the runs of
coins that the part spends, drawn uniformly; the part's challenges are fixed, and are such as its
rounds can draw.

NO NEW LAW. It is a corollary of `ExactMember` and of "the simulators read their own coins alone". IT IS
THE ONE-TIME PAD's FACT: TRUE OF ANY MASKED PART, WHATEVER IT MASKS, right or wrong. IT IS NOT THE LAW OF
THE VIEW: in a run later parts (the segment's closing, the next code switch) carry the same 173 coins,
and by the format's pages (not by Lean) what K6 shows then meets the verifier's equations. It does NOT
say that K6 hides the weights.

How. `ExactMember` (Honest/Small/Field.lean: the field `exact` without its premise on the opened
columns, which is more than the field; K6 has it by `head_exact_all`, Honest/K6/Law/GoodRowSum.lean)
says that the part's law at a state is its simulator's law there; K6's
simulators read their own coins alone; and at every state there is a front at which it is asked,
because K6's rounds read no table. The general lemma and the law's definition (`shownLaw`) stand in
Honest/K6/Term/ShownLaw.lean.

WHAT IT IS NOT.
  * NOT zero knowledge and NOT hiding of the protocol or of the prover. ONE PART AT A TIME, PLAYED ALONE,
    everything else fixed before the coins. NO JOINT LAW of the eight parts or with any other kind.
  * THE SPENT RUNS ARE TAKEN AS UNIFORM AND INDEPENDENT OF THE STATE. In a run of the prover they are
    entries of the segment's mask row: their owner, another kind's sender, has shown columns of that
    row's encoding before, and later parts carry the same entries. That this does no harm is the
    owner's `fresh`, the carriers' `exact` and the frame's rule: none is here.
  * It holds at every job, right or wrong: it says nothing on whether what is sent is the protocol's.
  * A masked sumcheck sends each end value plus a challenge times a mask entry. The round that draws
    that challenge ("PSC Y") draws it by the rule that never gives 0, and `drawsFit` asks that rule
    (`drawsMarkedNonzeroHaveNonzeroWords`, Honest/Frame.lean: `drawFit`). At 0 the end values would be sent bare: nothing is said
    there.

  `head_marginal_law_same_at_all_states`   the statement, under the structure `HeadSeated`
  `head_marginal_law_at_maker`   the same at what the honest prover's maker returns
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.NothingStops
import Johnson.Desc.ProofFile.Honest.K6.Term.ShownLaw
import Johnson.Desc.ProofFile.Honest.K6.Term.SimulatorShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Chain Oracle)
open VerifiableInference.Desc.Kinds
open ProofFile.Honest.Small

variable {S Cl X W₀ Rc Tr X₀ : Type}

/-- CONDITIONAL: the structure `HeadSeated`. **EACH PART's MARGINAL LAW, OVER SPENT RUNS TAKEN AS FRESH, IS
ONE AT ALL STATES**; not the law of a run's view: over uniform spent runs, at fixed challenges that its
rounds can draw and at positions within the row's bud. m, m': any two states of the prover's run
before the part, each with its own input (true of any masked part, whatever it masks). ca, ca': the
carried runs, of which K6 has none. -/
theorem head_marginal_law_same_at_all_states (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (hu : u ∈ σ.members) (ca ca' : CsAll u.part.carries) (m m' : Mid (Local W₀ Rc Inst Tr) X)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) (hb : headBud u.number ds asks) :
    shownLaw φ σ u ca m ds asks = shownLaw φ σ u ca' m' ds asks := by
  have hq : (u.part, u.sim) ∈ headSided (X := X) wit p at_ := by
    rw [← h.row]
    exact pair_of_membersOf σ.row 0 _ u hu
  have hstop := headSided_cases wit p at_
    (Q := fun q => (∀ loc ds, q.1.bad loc ds = none) ∧ ∀ v loc ds, q.1.hid v loc ds = none)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩) _ hq
  have htell := headSided_cases wit p at_
    (Q := fun q => ∀ pub pub' front front' ds ds' asks asks' c,
      q.2.tell pub front ds asks c = q.2.tell pub' front' ds' asks' c)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) _ hq
  have hreads : ∀ d ∈ u.rounds.map (·.1), d.stored = [] ∧ d.opens = [] := by
    intro d hd'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd'
    have hz := (List.of_mem_zip (mem_rounds_of_member hu hr)).1
    rw [h.rounds] at hz
    exact head_reads_nothing p _ hz
  exact shownLaw_same (head_exact_all φ h 0 0 (fun _ _ _ _ => True) headBud u hu) htell hreads
    (K5.stopAt_none u.part hstop.1 hstop.2) ca ca' m m' ds asks hd hb

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h; the maker returns. **The same at what the honest prover's maker
returns**: at each row of the lot, at its side over the returned description's first chain, at each
of its members. General in the filling. -/
theorem head_marginal_law_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights) :
    ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows A.Z A.G,
    ∀ (falls : List (Fall A.F.S₁)) σ, Side.seated A.F.first.blocksInOrder r.place r.row falls = some σ →
    ∀ u ∈ σ.members, ∀ (ca ca' : CsAll u.part.carries) (m m' : Mid (Local W₀ Rc Inst Cells) X)
      (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
      drawsFit (u.rounds.map (·.1)) ds = true → r.bud u.number ds asks →
      shownLaw .own σ u ca m ds asks = shownLaw .own σ u ca' m' ds asks := by
  have hG₀ := (atPure_ok hA).2.1
  obtain ⟨G, B, H, rd, rw', rfl⟩ := atPure_is h.laid hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := hG₀
  intro r hr falls σ hσ u hu ca ca' m m' ds asks hd hb
  obtain ⟨σ₀, hσ₀, hS⟩ := head_lot_seated (Rc := Rc) (X := X) (head_lotSeatB_under_head h hG) id
    (weights Zp) falls r hr
  obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
  obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
  exact head_marginal_law_same_at_all_states .own hS u hu ca ca' m m' ds asks hd hb

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_marginal_law_same_at_all_states
#print axioms ProofFile.Honest.K6.head_marginal_law_at_maker
