-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LayersTieHead.lean: for the callers of the lookup on the
calls of a layers' link: a text for what that lookup returns, made of the public shape and of the
challenges heard alone; and, under the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean):
what the fold's state right behind that lookup's member holds as the returned structure agrees with
that text in the eleven fields of `OpenSame` (Honest/K3/HeardWhole.lean). Two definitions; theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: group g of layers stands at link 2 g. The fold is
`foldBlocks` (Johnson/Desc/Block.lean) over the first members of the first chain's flat list.
`lookHeardAt` (Honest/K3/HeardWhole.lean) is the structure that a shape, a base and a list of
challenges make. `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the border in
front of link l's lookup; d is false for the lookup on the calls. The number of rounds of the first
j members is written out: `((c.blocksInOrder.take j).flatMap (·.rounds)).length`.

What is shown.
  `callsShape Z g`: the shape of the site on the calls at link 2 g; the default shape where the list
    of sites has none.
  `lookOfK3 Z c`: the text, as a function of the group's number g, an instance (not read) and the
    chain's challenges from its first round on: `lookHeardAt` at that shape and at the number of
    rounds of the first 28 g + 3 members.
  `fold_rest`: what a returning fold leaves of the rounds: all but its members' own; and there were
    that many.
  `border_even`: the border in front of the lookup on the calls of link 2 g, g < 12, has the number
    28 g + 3.
  `calls_site_found`: under `P5J.AtMgA` the list of sites has a site on the calls at link 2 g, and
    `callsShape` is its shape.
  `layers_tie_head`: the tie, in all eleven fields, from every first state.
  `htie_head`: the field zk alone, from the description's own first state, in the form in which
    another kind's theorem asks it. It is `layers_tie_head` at the description's own first state,
    with ten of the eleven fields dropped: whoever wants theta, alpha, zx, zy, e, zb0 or zb1 takes
    `layers_tie_head`.

Hypotheses that remain.
  `h`, `hg`: the library's hypothesis `P5J.AtMgA`; g is below 12. No public test is assumed.
  `hfold`, `hy`, `hfo`: (in `layers_tie_head`) a fold over the first 28 g + 4 members returns; the
    state behind stands in a layers' link; its own part holds fo as the lookup's structure.
  Inside `htie_head`: the same from the description's own first state, and "no mark". "No mark" is
    among the hypotheses for the sake of the form; the proof does not use it.

How the proof goes. The theorems call `site_calls_head` (Honest/K3/Law/Thread/SiteThereHead.lean),
`site_hub` (Honest/K3/Law/Thread/AtLink.lean), `member_at_link`
(Honest/K3/Law/Thread/AtLinkThere.lean), `calls_here` (Honest/K3/Law/Thread/StateHere.lean),
`site_facts` (Honest/K3/Law/MemberSite.lean) and `heardWhole_of_hearVia`
(Honest/K3/Law/HeardWholeLaw.lean), and the library's `IM.fold_last` (Johnson/IMR/SendsFold.lean)
and `foldBlocks_cons` (Johnson/Desc/K15/FoldInv.lean).

Users. Honest/K3/Law/Thread/HeadCallsTie.lean calls `fold_rest`; its `head_calls_tie` follows
`layers_tie_head`.

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`.
This file shows of no rounds that a fold returns. No instance of these hypotheses is exhibited in
this file.
What the text is not. The eight other fields of the structure are blank in it (see the head of
Honest/K3/HeardWhole.lean): a caller must not read them off it. It computes the fields tT and
leavesA, which are costly to compute: a lighter value for a run is another term. It is evaluated at
no data in this file. That a prover's half is laid over this very text is for whoever lays that half
to show: it is not shown in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLinkThere
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateHere
import Johnson.Desc.ProofFile.Honest.K3.Law.HeardWholeLaw
import Johnson.IMR.SendsFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks foldBlocks_cons)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The shape of the site on the calls at link 2 g. Where the list of sites has none it is the
default shape, without a warning: under `P5J.AtMgA` that does not happen (`calls_site_found`). -/
def callsShape (Z : Pub) (g : Nat) : OnBytes.Model.Forest.Shape :=
  (((lookSites Z).find? fun s => s.link == 2 * g && !s.digits).map (·.shape)).getD default

/-- **The text**: what the lookup on the calls of link 2 g returns, as far as it depends on the
public shape and the challenges alone. The instance is not read. -/
def lookOfK3 (Z : Pub) (c : Chain FS ProofFile.Cl) :
    Nat → ProofFile.Inst → List Fmt.Drawn → OnBytes.Model.Forest.Heard :=
  fun g _ hd =>
    lookHeardAt (callsShape Z g) ((c.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length hd

/-- **What a returning fold leaves of the rounds.** -/
theorem fold_rest {S Cl : Type} (ft : Nat) : ∀ (l : List (Block S Cl)) (s t : S)
    (rs r : List Fmt.RoundView) (cols c : List OpenedColumn), foldBlocks ft l s rs cols = .ok (t, r, c) →
    r = rs.drop (l.flatMap (·.rounds)).length ∧ (l.flatMap (·.rounds)).length ≤ rs.length
  | [], s, t, rs, r, cols, c, h => by
    unfold foldBlocks at h
    have e : (s, rs, cols) = (t, r, c) := Except.ok.inj h
    have e2 : rs = r := (Prod.mk.inj (Prod.mk.inj e).2).1
    subst e2
    simp
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨s', k, hl, _, h'⟩ := foldBlocks_cons ft b l s rs cols _ h
    obtain ⟨e1, e2⟩ := fold_rest ft l s' t _ r _ c h'
    have hn : b.rounds.length ≤ rs.length := by
      rw [List.length_take] at hl
      omega
    rw [List.length_drop] at e2
    rw [List.flatMap_cons, List.length_append]
    refine ⟨?_, by omega⟩
    rw [e1, List.drop_drop]

/-- The number of the border in front of the lookup on the calls of link 2 g. -/
theorem border_even (g : Nat) (hg : g < 12) : borderOf (2 * g) false = 28 * g + 3 := by
  unfold borderOf ixOf
  have h24 : ¬ (2 * g = 24) := by omega
  rw [if_neg h24]
  simp
  omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under `P5J.AtMgA` the list of sites has a site on the calls at link 2 g, and `callsShape` is its
shape. -/
theorem calls_site_found (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ s ∈ lookSites Zp, s.link = 2 * g ∧ s.digits = false ∧ callsShape Zp g = s.shape := by
  obtain ⟨s₀, hs₀, e1, e2, _, _⟩ := site_calls_head h (2 * g) (by omega)
  cases hf : (lookSites Zp).find? fun s => s.link == 2 * g && !s.digits with
  | none =>
    have h0 := List.find?_eq_none.1 hf s₀ hs₀
    rw [e1, e2] at h0
    simp at h0
  | some s =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    refine ⟨s, List.mem_of_find?_eq_some hf, hp.1, hp.2, ?_⟩
    unfold callsShape
    rw [hf]
    rfl

/-- **The tie, in all eleven fields, from every first state.** Conditional on `P5J.AtMgA` and g <
12. No instance of these hypotheses is exhibited in this file. -/
theorem layers_tie_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    (s₀ : TS) (ξ : ProofFile.Inst) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (sj : TS) (rr : List Fmt.RoundView)
    (c : List OpenedColumn) (y : VerifiableInference.Desc.First.LayOwn) (fo : OnBytes.Model.Forest.Heard)
    (hfold : foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) s₀ rs cols = .ok (sj, rr, c))
    (hy : sj.here = .lay y) (hfo : y.fo = some fo) :
    OpenSame fo (lookOfK3 Zp cF g ξ
      ((rs.take ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length).map (·.drawn))) := by
  obtain ⟨s, hs, e1, e2, eS⟩ := calls_site_found h g hg
  have hl : s.link < 25 := by omega
  obtain ⟨blk, hblk, _⟩ := member_at_link h (2 * g) (by omega) false
  rw [border_even g hg] at hblk
  obtain ⟨t, rs', cols', n, hfront, hstep⟩ := IM.fold_last hblk hfold
  obtain ⟨er, hle⟩ := fold_rest 0 _ _ _ _ _ _ _ hfront
  obtain ⟨Fd, Bs, base, A, B, lot, O, hlot, hbs, hm⟩ := site_hub h s hs hl
  have hb' : cF.blocksInOrder[borderOf s.link s.digits]? = some blk := by
    rw [e1, e2, border_even g hg]
    exact hblk
  obtain ⟨m1, m2, m3⟩ := hm blk hb'
  obtain ⟨F, H, G, _, _, hv, hC, _⟩ := calls_here _ _ _ _ Fd Zp Bs base cF A B O s hs e2 lot blk
    hlot hbs m1 m2 m3 0 t sj n _ cols' hstep
  have eH : fo = H := by
    rcases hC with ⟨q, _, e⟩ | ⟨q, _, e⟩ | ⟨q, _, _, e⟩
    · rw [e] at hy
      injection hy with hy'
      rw [← hy'] at hfo
      exact (Option.some.inj hfo).symm
    · rw [e] at hy
      cases hy
    · rw [e] at hy
      cases hy
  have hsh : s.p.shape = some s.shape := by
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs'
    exact (site_facts _ _ a s hsa).2.1
  have W := heardWhole_of_hearVia s.p s.shape hsh F G _ H
    ((rs.take ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length).map (·.drawn)) [] hv
  have eL : ((rs.take ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length).map
      (·.drawn)).length = ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length := by
    rw [List.length_map, List.length_take]
    exact Nat.min_eq_left hle
  have eA : ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length =
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length + blk.rounds.length := by
    rw [show 28 * g + 4 = 28 * g + 3 + 1 from rfl, List.take_add_one, hblk]
    simp
  rw [eL, er, List.append_nil, ← List.map_append, ← List.take_add, ← eA] at W
  rw [eH]
  unfold lookOfK3
  rw [eS]
  exact W

/-- **The field zk, from the description's own first state.** Conditional on `P5J.AtMgA`.
No instance of these hypotheses is exhibited in this file. -/
theorem htie_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ g < 12, ∀ (ξ : ProofFile.Inst) rs cols sj c y fo,
      foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) (ProofFile.startS Zp ξ.pub) rs cols =
        .ok (sj, rs.drop ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length, c) →
      sj.failed = none → sj.here = .lay y → y.fo = some fo →
      (lookOfK3 Zp cF g ξ
        ((rs.take ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length).map (·.drawn))).zk =
          fo.zk :=
  fun g hg ξ rs cols sj c y fo hfold _ hy hfo =>
    (layers_tie_head h g hg _ ξ rs cols sj _ c y fo hfold hy hfo).zk.symm

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.fold_rest
#print axioms ProofFile.Honest.K3.Law.AtThr.border_even
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_site_found
#print axioms ProofFile.Honest.K3.Law.AtThr.layers_tie_head
#print axioms ProofFile.Honest.K3.Law.AtThr.htie_head
