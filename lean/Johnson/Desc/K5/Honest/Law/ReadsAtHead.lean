-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsAtHead.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the sub-protocol that stands in the first chain just
behind the block of an attention segment's own rounds (the sending of the array of the segment's
tables, with the quiet step joined that makes the tables and closes the list) says yes at the state
behind that block's lay, IF THE SENDING'S OWN DECISION SAYS YES THERE and the smallness test's guard
of order says yes behind it.

It is `seated_reads_yes` and `reads_after` (Johnson/Desc/K5/Honest/Law/ReadsAfter.lean) at the
head's letters: which sub-protocol stands there is the library's `IM.k1_reads_of`
(Johnson/IMR/K1Scope.lean); that the points' and the tables' functions return at the state behind
the lay is `runs_at_head` (Johnson/Desc/K5/Honest/Law/DoorAtHead.lean).

Main names:
  `inAt_parts`: what a return of the claims' reading holds: the returns of the points' and of the
    tables' functions.
  `ReadsMember`: the ties that fix the letters of which the statements speak: the maker's ground at
    the blank request, its link, that link's numbers, the sub-protocol. `ReadsMember.one`: they fix
    them.
  `member_at_head`: there are such letters: the sub-protocol at number 14 (2 g + 1) + 5 of the first
    chain's flat list: one behind the block of the own rounds, which stands at 14 (2 g + 1) + 4.
  `reads_of_member`: **its yes**, the letters free under the ties.
  `reads_at_head`: the same with the letters drawn from the head, their ties handed out.
  `reads_at_border`: `reads_of_member` at the border's own number, ho and hshp paid from the head
    and the reached state.

WHAT IS NOT HAD HERE, EACH A PREMISE OF `reads_at_border`:
  h1: the sending's own yes, at its share of the rounds and the groups: a matter of the sending's
    honest side;
  hord: the guard of order says yes at the link's context and the statement behind the sending
    (`K8.Order.orderOk att.tl L' m.st = true`): the smallness test's own guard, at what the sending
    lays.
`reads_of_member` and `reads_at_head`, at any number k of the reached state, keep two premises
more: ho (`att.tl.funClosed = false`) and hshp (`att.tl.shp.size = att.tl.NM`).
Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front of the block of the own rounds is not shown here. At the function
`OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DoorAtHead
import Johnson.Desc.K5.Honest.Law.ReadsAfter
import Johnson.Desc.K5.Honest.Law.TlOpen
import Johnson.Desc.K5.Honest.Law.PlanShp
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (behind hear Heard)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.K1 (laterAt gpOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- What a return of the claims' reading holds, as far as the quiet step reads it. (The library's
`K5Law.inAt_parts`, Johnson/Desc/First/Att/Claims/HeardPlain.lean, says more, in other letters.) -/
theorem inAt_parts {c : Att.P.ParC} {g : Forest.Heard} {hh : Heard} {U : Fork}
    {i : Att.P.Runs.In} {K : ℕ} (h : K5Law.inAt c g hh U = some (i, K)) :
    Att.P.ptsFrom c.geo g.zk hh U = some i.p ∧
      Att.P.tablesP c.geo c.mats c.nW (Att.P.lookOfO c.geo.lmb g) i.p = some i.t := by
  unfold K5Law.inAt at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨p, hp, t, ht, K', _, e, _⟩ := h
  subst e
  exact ⟨hp, ht⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **What ties the letters of the sub-protocol just behind the block of the own rounds of group
g.** G₀: the ground that the library's maker lays at the blank request; Xl: its link number
2 g + 1; pd, reads, digits: that link's numbers by the sending's own rule; b: the sub-protocol. Each
letter is fixed by an equation from the public input Zp and the chain cF (`ReadsMember.one`). -/
structure ReadsMember (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (g : ℕ) (G₀ : ProofFile.Ground)
    (Xl : Stages.LinkH) (pd : ℕ) (reads digits : Option (List ℕ)) (b : Block S ProofFile.Cl) :
    Prop where
  /-- the ground is the maker's at the blank request -/
  blank : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀
  /-- its public parameters are the public input's -/
  pubW : G₀.W = P5J.At.X Zp
  /-- the link -/
  built : G₀.built[2 * g + 1]? = some Xl
  /-- the link's numbers: the sending of the tables stands at piece 4 -/
  numbers : VerifiableInference.Desc.K1.linkNumbers G₀ Xl = some (4, pd, reads, digits)
  /-- the link is of the attention sort, of group g -/
  kind : Xl.kind = 1
  group : Xl.g = g
  /-- where the sub-protocol stands in the flat list -/
  flat : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b
  /-- what it is -/
  is : b = IM.seatedAs ProofFile.sameReply (IM.k1Reads Zp G₀ (2 * g + 1) Xl 4 reads).retype b.name
    ⟨1, some (2 * g + 1), 4, .K1⟩

/-- The letters are fixed: two lists of letters that meet the ties are one. No premise beside. -/
theorem ReadsMember.one {g : ℕ} {G₀ G₁ : ProofFile.Ground} {Xl X₁ : Stages.LinkH} {pd p₁ : ℕ}
    {reads r₁ digits d₁ : Option (List ℕ)} {b b₁ : Block S ProofFile.Cl}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b)
    (M' : ReadsMember Zp cF g G₁ X₁ p₁ r₁ d₁ b₁) :
    G₀ = G₁ ∧ Xl = X₁ ∧ pd = p₁ ∧ reads = r₁ ∧ digits = d₁ ∧ b = b₁ := by
  obtain rfl : G₀ = G₁ := Option.some.inj (M.blank.symm.trans M'.blank)
  obtain rfl : Xl = X₁ := Option.some.inj (M.built.symm.trans M'.built)
  have e := Option.some.inj (M.numbers.symm.trans M'.numbers)
  simp only [Prod.mk.injEq, true_and] at e
  exact ⟨rfl, rfl, e.1, e.2.1, e.2.2, Option.some.inj (M.flat.symm.trans M'.flat)⟩

include h in
/-- **Which sub-protocol stands just behind the block of the own rounds.** Conditional: the head;
hg. -/
theorem member_at_head {g : ℕ} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : Stages.LinkH) (pd : ℕ) (reads digits : Option (List ℕ))
      (b : Block S ProofFile.Cl), ReadsMember Zp cF g G₀ Xl pd reads digits b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, eX, hn, hla⟩ :=
    IM.k1_reads_of h.scope h.reads O (2 * g + 1) (by omega)
  have e3 : IM.k1Ix (2 * g + 1) false = 3 := by
    show 3 + (if 2 * g + 1 = 24 then 1 else 0) = 3
    rw [if_neg (by omega)]
  obtain ⟨_, X', _, _, _, _, eX', hk, hgX, _⟩ :=
    (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : X' = Xl := Option.some.inj (eX'.symm.trans eX)
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) (IM.k1Ix (2 * g + 1) false),
    e3, show 14 * (2 * g + 1) + 2 + 3 = 14 * (2 * g + 1) + 5 by omega] at hfl
  rw [e3] at hn
  refine ⟨Bs.G₀, X', pd, reads, digits, b, O.blank, O.W, eX, hn, hk, hgX, hfl, ?_⟩
  have hla' : b = IM.seatedAs ProofFile.sameReply
      (IM.k1Reads Zp Bs.G₀ (2 * g + 1) X' (IM.k1Ix (2 * g + 1) false + 1) reads).retype b.name
      (IM.k1PlaceL (2 * g + 1) false) := hla
  unfold IM.k1PlaceL at hla'
  rw [e3] at hla'
  exact hla'

/-- **The yes of the sub-protocol just behind the block of the own rounds, at the state behind
that block's lay.** G₀, Xl, pd, reads, digits, b: LETTERS, under the ties M. Conditional: M; as
`runs_at_head`, two of whose premises are paid inside from the head; hgL: what the lookup returned
is laid in the open segment; ho, hshp: two named premises on the smallness test's part of the state
in front. Under these: for whatever rounds and groups at which the sending's own decision says yes
(h1) and the guard of order says yes behind it (hord), the whole sub-protocol says yes, and the
state behind is the sending's with the tables laid and the list closed. The tables are those of the
claims' reading (i, K) at the state behind the lay. -/
theorem reads_of_member {G₀ : ProofFile.Ground} {Xl : Stages.LinkH} {pd : ℕ}
    {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl} {g : ℕ}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) {gL : Forest.Heard}
    (hgL : att.g = some gL) (ho : att.tl.funClosed = false)
    (hshp : att.tl.shp.size = att.tl.NM) :
    ∃ (i : Att.P.Runs.In) (K : ℕ),
      Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (behind s att hd G) =
        some (i, K) ∧
      ∀ (rs' : List Fmt.RoundView) (gs' : List (List (ℕ × List UInt64))) (m : S),
        (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).decide
          (behind s att hd G)
          (rs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).rounds.length)
          (gs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).openings) =
            .ok m →
        (∀ L', m.link? = some L' → K8.Order.orderOk att.tl L' m.st = true) →
        ∃ a₁, m.here = .att a₁ ∧
          b.decide (behind s att hd G) rs' gs' = .ok (behindReads m a₁ i.t) := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := lookC_all h hg
  obtain ⟨i, K, _, _, _, _, _, _, hin0, _⟩ :=
    runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  refine ⟨i, K, hin0, fun rs' gs' m h1 hord => ?_⟩
  have hin := hin0
  rw [K5Law.inOf_isAt (a := { att with F := G, heard5 := some hd }) rfl] at hin
  have hin' : K5Law.inAt (Att.P.parCOf a) gL hd G = some (i, K) := by
    have := hin
    simp only [hgL] at this
    exact this
  obtain ⟨hp, ht⟩ := inAt_parts hin'
  obtain ⟨a₁, hm, h2, hf, hout⟩ := reads_after (Cl := Unit) a
    (s := behind s att hd G) (a₀ := { att with F := G, heard5 := some hd }) rfl rfl hgL ho hp ht
    hshp h1 hord
  refine ⟨a₁, hm, ?_⟩
  rw [M.is]
  exact seated_reads_yes Zp G₀ (2 * g + 1) Xl reads b.name M.kind
    (by rw [M.pubW, M.group]; exact ea) h1 h2 (hf.trans hu) hout

/-- **The same with the letters drawn from the head, AND THEIR TIES HANDED OUT.** Conditional: as
`reads_of_member`, without M. -/
theorem reads_at_head {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) {gL : Forest.Heard}
    (hgL : att.g = some gL) (ho : att.tl.funClosed = false)
    (hshp : att.tl.shp.size = att.tl.NM) :
    ∃ (G₀ : ProofFile.Ground) (Xl : Stages.LinkH) (pd : ℕ) (reads digits : Option (List ℕ))
        (b : Block S ProofFile.Cl) (i : Att.P.Runs.In) (K : ℕ),
      ReadsMember Zp cF g G₀ Xl pd reads digits b ∧
      Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (behind s att hd G) =
        some (i, K) ∧
      ∀ (rs' : List Fmt.RoundView) (gs' : List (List (ℕ × List UInt64))) (m : S),
        (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).decide
          (behind s att hd G)
          (rs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).rounds.length)
          (gs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).openings) =
            .ok m →
        (∀ L', m.link? = some L' → K8.Order.orderOk att.tl L' m.st = true) →
        ∃ a₁, m.here = .att a₁ ∧
          b.decide (behind s att hd G) rs' gs' = .ok (behindReads m a₁ i.t) := by
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  obtain ⟨i, K, hin, H⟩ := reads_of_member h M hg ea Mg hpub hpubP O Q Oq hr hu hon e hh hgL ho
    hshp
  exact ⟨G₀, Xl, pd, reads, digits, b, i, K, M, hin, H⟩

/-- **The same at the border's own number, with the two premises on the smallness test's part of
the state in front PAID** (`tlOpen_head`, Johnson/Desc/K5/Honest/Law/TlOpen.lean: the list of tables
is open there, the shapes and the number of matrices are the plan's; `hplan_at_head`,
Johnson/Desc/K5/Honest/Law/PlanShp.lean: there is one shape a matrix at the plan). Conditional: as
`reads_of_member`, with hr at 14 (2 g + 1) + 4, without ho and hshp. -/
theorem reads_at_border {G₀ : ProofFile.Ground} {Xl : Stages.LinkH} {pd : ℕ}
    {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl} {g : ℕ}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) {gL : Forest.Heard}
    (hgL : att.g = some gL) :
    ∃ (i : Att.P.Runs.In) (K : ℕ),
      Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (behind s att hd G) =
        some (i, K) ∧
      ∀ (rs' : List Fmt.RoundView) (gs' : List (List (ℕ × List UInt64))) (m : S),
        (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).decide
          (behind s att hd G)
          (rs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).rounds.length)
          (gs'.take (laterAt (Cl := Unit) G₀.first (gpOf Zp) (2 * g + 1) 4 1 reads).openings) =
            .ok m →
        (∀ L', m.link? = some L' → K8.Order.orderOk att.tl L' m.st = true) →
        ∃ a₁, m.here = .att a₁ ∧
          b.decide (behind s att hd G) rs' gs' = .ok (behindReads m a₁ i.t) := by
  obtain ⟨ho, e1, e2⟩ := tlOpen_head h hg ea hr e
  exact reads_of_member h M hg ea Mg hpub hpubP O Q Oq hr hu hon e hh hgL ho
    (by rw [e1, e2]; exact hplan_at_head h ea)

end

end H2K5.Honest

#print axioms H2K5.Honest.inAt_parts
#print axioms H2K5.Honest.ReadsMember.one
#print axioms H2K5.Honest.member_at_head
#print axioms H2K5.Honest.reads_of_member
#print axioms H2K5.Honest.reads_at_head
#print axioms H2K5.Honest.reads_at_border
