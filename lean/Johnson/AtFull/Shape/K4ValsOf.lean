-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K4ValsOf.lean: THE LAYERS' OWN ROUNDS (kind K4; the twelve members 28 g + 4 of
the proof file's own first chain): THE MEMBER's TEST ON VALUES k4ValsV (K4Fit.lean) FROM ITS THREE
CLAUSES, WITH THE FIRST PAID AT EVERY STATE REACHED FROM A START WHOSE REQUEST PASSES ITS TEST.
Under the head P5J.AtMgA. A joining of laws; nothing is evaluated.

The three clauses. (1) tokensFit: in the first group the request has T tokens, each below the
vocabulary's size: it reads the request's words alone. (2) every call's point ends as the lookup's
own (mergedB): it compares points with points. (3) coinB: the one round behind the norms' rows draws
no element that is 0: it hangs on the draws.

  `tokensFit_of_reqOk`: GENERAL: the state's own test on the request at T and V gives tokensFit at
    every record of the layers' numbers whose count of tokens is T and whose vocabulary's size is V.
  `k4ValsV_of`: GENERAL: the three clauses give the Bool.
  `layers_nums_at`: under the head: the layers' count of tokens and vocabulary's size, in the
    maker's ground, are the public part's own (P5J.vocab_in_scope, Johnson/P5J/VocabAtHead.lean).
  **`k4ValsV_reach`**: under the head, with Bs what ProofFile.baseOf returns at the public part: at every
    state that the chain reaches from its own start (Reach, Johnson/Top/H0/Walk/Reach.lean: the raw
    family), at an instance whose request passes the start's test, at every record p of the kind's
    numbers with p.P the ground's layers: clauses (2) and (3) give k4ValsV p.
  **`tab_k4_vals`**: the table's own test at 28 g + 4 (g < 12) is k4ValsV at such a record.
  **`vals_k4_reach`**: so, at such a reached state, clauses (2) and (3) at the ground's record give
    the table's own test at 28 g + 4.

Limits. CLAUSES (2) AND (3) ARE HYPOTHESES. (3) can fail at an honest play: it is a matter for the
rule's letter "fall": no law from a fall's silence to coinB is called here. (2) is meant as an
invariant of the verifier's state: not shown. That anything is reached is not said. That the head
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.TableFramesV
import Johnson.AtFull.Shape.ReqReplyReach
import Johnson.P5J.VocabAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par entries)
open OnBytes.Desc.First.K4.Rt (coinB)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The state's own test on the request gives the tokens' test.** -/
theorem tokensFit_of_reqOk {P : Layer.Pub} {s : S} {T V : Nat} (hq : s.reqOk T V = true)
    (hT : P.y.T = T) (hV : P.V = V) (g : Nat) : tokensFit { P with tokv := s.tokv } g = true := by
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨q1, q2⟩, -⟩ := hq
  have hs : s.tokv.size = T := by
    unfold S.tokv S.reqT
    simp only [Array.size_map, Array.size_extract]
    omega
  unfold tokensFit
  show (g != 0 || (s.tokv.size == P.y.T && s.tokv.all fun t => decide (t < P.V))) = true
  rw [hT, hV, q2, hs]
  simp

/-- The three clauses give the Bool. -/
theorem k4ValsV_of {p : Par} {s : S} {rs : List Fmt.RoundView}
    (a1 : tokensFit { p.P with tokv := s.tokv } p.g = true)
    (a2 : (s.look?.all fun fo => mergedB p.P fo) = true)
    (a3 : coinB p.P p.g (paired rs (entries p.P p.hp p.g)) = true) : k4ValsV p s rs = true := by
  unfold k4ValsV
  rw [a1, a2, a3]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- The layers' two numbers in the maker's ground are the public part's own. -/
theorem layers_nums_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Bs.G₀.W.layers.y.T = Zp.p.X.T ∧ Bs.G₀.W.layers.V = Zp.p.X.P.h.V := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  have hp := O.public
  rw [O.W] at hp
  obtain ⟨v1, -, v3⟩ := P5J.vocab_in_scope h.scope h.reads hp
  rw [O.W]
  exact ⟨rfl, v3.trans v1.symm⟩

/-- **At every reached state the first clause is paid.** -/
theorem k4ValsV_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {k : Nat}
    {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
    (hq : (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (p : Par) (hp : p.P = Bs.G₀.W.layers) (rs : List Fmt.RoundView)
    (a2 : (a.2.look?.all fun fo => mergedB p.P fo) = true)
    (a3 : coinB p.P p.g (paired rs (entries p.P p.hp p.g)) = true) : k4ValsV p a.2 rs = true := by
  obtain ⟨hT, hV⟩ := layers_nums_at h hB
  exact k4ValsV_of (tokensFit_of_reqOk (reqOk_reach h hr hq) (by rw [hp]; exact hT)
    (by rw [hp]; exact hV) p.g) a2 a3

/-- **The table's own test at 28 g + 4.** -/
theorem tab_k4_vals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (g : Nat) (hg : g < 12) :
    ∃ hp : Layer.HPlan2, Bs.G₀.W.G[g]? = some hp ∧ ∀ s rs gs,
      Tab.vals Zp Bs.G₀ (28 * g + 4) s rs gs =
        k4ValsV ⟨"", 0, 3, [], true, Bs.G₀.W.layers, hp, g⟩ s rs := by
  obtain ⟨B', y, e1, -, -, -, e5, -⟩ := k4_frame_fit h g hg
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (28 * g + 4) = Tab.k4 Bs.G₀ g := by
    rw [cells_link Zp Bs.G₀ (2 * g) 3 (by omega) (by omega) (by omega)]
    show (if (2 * g) % 2 == 0 then Tab.k4 Bs.G₀ (2 * g / 2) else Tab.k5 Zp (2 * g / 2)) = _
    rw [if_pos (beq_iff_eq.2 (by omega)), show 2 * g / 2 = g from by omega]
  unfold Tab.k4 at hc
  rw [e5] at hc
  exact ⟨_, e5, fun s rs gs => by rw [cell_v hc]⟩

/-- **At every reached state: clauses (2) and (3) give the table's own test at 28 g + 4.** -/
theorem vals_k4_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (g : Nat) (hg : g < 12) :
    ∃ hp : Layer.HPlan2, Bs.G₀.W.G[g]? = some hp ∧ ∀ {k : Nat} {a : ProofFile.InstPub × S},
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a →
      (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true →
      ∀ rs gs, (a.2.look?.all fun fo => mergedB Bs.G₀.W.layers fo) = true →
      coinB Bs.G₀.W.layers g (paired rs (entries Bs.G₀.W.layers hp g)) = true →
      Tab.vals Zp Bs.G₀ (28 * g + 4) a.2 rs gs = true := by
  obtain ⟨hp, e, hv⟩ := tab_k4_vals h hB g hg
  refine ⟨hp, e, fun hr hq rs gs a2 a3 => ?_⟩
  rw [hv]
  exact k4ValsV_reach h hB hr hq ⟨"", 0, 3, [], true, Bs.G₀.W.layers, hp, g⟩ rfl rs a2 a3

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tokensFit_of_reqOk
#print axioms Johnson.AtFull.Shape.k4ValsV_of
#print axioms Johnson.AtFull.Shape.layers_nums_at
#print axioms Johnson.AtFull.Shape.k4ValsV_reach
#print axioms Johnson.AtFull.Shape.tab_k4_vals
#print axioms Johnson.AtFull.Shape.vals_k4_reach
