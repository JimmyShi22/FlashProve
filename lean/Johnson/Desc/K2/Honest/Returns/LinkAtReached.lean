-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LinkAtReached.lean: THE LAW "THE KIND's OWN DECISION SAYS YES AT A
SEGMENT's FIRST PLACE" (`LinkPlain`, Returns/LinkSent.lean), WHOLE, AT A STATE THAT IS REACHED IN
FRONT OF THE SWITCH INTO A LATER GROUP, AT THE NUMBERS THAT THE PLAN's OWN MAKER LAYS FOR THE PLACE
AND AT THE FRAME's OWN SEGMENT, GROUP AND TWO CODES: FROM THE PREMISES IN FRONT, THREE NAMED TESTS
ON THE PUBLIC PART, TWO PREMISES ON THE ROUNDS' ENTRY, AND ONE STRUCTURE THAT HOLDS WHAT IS LEFT
(`LinkLeft`: sixteen fields). SO THE KIND's OWN DECISION RETURNS THERE. A join: every clause that
this folder's files pay at a reached state is laid into its field. Statements with their proofs:
calls.

  `readIn p s r₁ r₂ gs L Q` what the reading of the old rows is handed, as `LinkPlain.reads` spells
                    it: a short name
  `LinkLeft p s r₁ r₂ gs L Q c` WHAT IS LEFT, each field in the letters of the structure that asks
                    it: six on the two rounds and the columns (fits₁ · vals · answers · loc ·
                    noneLeft · groups) · `ReadFits.opens`, which reads the columns too, and
                    `ReadFits.own`, on the book · six on what the frame holds of the plan (plain ·
                    plan · trees · own · `FrontCore.groupCode` · copiesCode) · `FrontCore.inRange` ·
                    `TablesFit.claimMain`
  `link_plain_reached` FOR ALL L, Q, c₀, z₀ that are the frame's own (four look-ups: the segment,
                    the group, the two codes): `LinkLeft` at them gives `LinkPlain` at them. That
                    there are such four: `link_fields_reached`
  `link_returns_reached` and so the decision's yes, from three of the look-ups and `LinkLeft`

THE COUNT. `LinkPlain` laid open has 67 clauses. 51 are laid in here by payers, `entry` among them,
which is led from the premise he; 16 are `LinkLeft`'s. Of the 51, fifteen stand under the three
tests as typed here: the test on the target · mainVars · d0 · d1 · once · keptCode · bitsKept ·
reads · tables.stored · the six of Returns/PinPublic.lean; five under he and the rounds that fit.

WHO PAYS WHAT. `link_fields_reached` (Returns/LinkReached.lean): thirteen · `link_first_reached`,
`link_front_at`, `link_draws_own` (Returns/FirstReached.lean, Returns/PinReached.lean): first; the
five on the draws · `link_waits_reached` (Returns/WaitsReached.lean) · `link_lay_reached`
(Returns/ClosedReached.lean): eight of `ReadFits` · `link_members_reached`, `link_book_reached`
(Returns/MembersReached.lean): rows · named · claimKept · placed · stated · `link_stored_reached`
(Returns/StoredReached.lean) · `link_shape_reached`, `link_reads_paid`, `link_tables_paid`
(Returns/PinReached.lean): the test on the target · mainVars · d0 · d1 · once · keptCode · bitsKept
· reads · tables.stored · `link_public_reached` (Returns/PinPublic.lean): six · the library's
`sw_link` (Johnson/P1K2R/HstReached.lean): the entry's test is led from the plan's own list to the
front's notices · `stands` holds by unfolding.

Limits. THE PREMISES IN FRONT, THE THREE TESTS, THE TWO ON THE ENTRY AND `LinkLeft` ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. The three tests hy · hcut · hB read the public part alone; the
opening stands at the public files' own layout file. `mainVars`, `d0`, `d1` are taken from
Returns/PinReached.lean here though Returns/ClosedReached.lean has them with no test. Whether
`inRange` follows from `range`, `oldCode` and the library's laws on the positions drawn: not sought.
The links' places alone. The full size alone. "Reached" is: over the list of the wrapped
sub-protocols. This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.FirstReached
import Johnson.Desc.K2.Honest.Returns.WaitsReached
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.Desc.K2.Honest.Returns.PinPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat locOk behindArgs)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf sw_link)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- What the reading of the old rows is handed, as `LinkPlain.reads` spells it. -/
abbrev readIn (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) : _root_.Tw.K2.SwIn :=
  inFront (par9 p) (frontAt s L Q) s.book (sentOf p s L Q r₁ r₂) r₂ (flat p gs)

/-- **What is left of `LinkPlain` at a reached state.** c: the old main code. -/
structure LinkLeft (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) (c : Code) : Prop where
  plain : L.plain = 0
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p (frontAt s L Q)) = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p (frontAt s L Q)) r₂)).length =
    (sendingAt p (frontAt s L Q)).answers
  trees : ((layTrees (sendingAt p (frontAt s L Q)).codes
    (sendingAt p (frontAt s L Q)).sent).getD {}).shapes.size = (par9 p).eSeed.roots
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) c.logN =
    true
  readsOwn : ∀ t ∈ treesOf (readIn p s r₁ r₂ gs L Q), ∀ tree,
    (readIn p s r₁ r₂ gs L Q).book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf (readIn p s r₁ r₂ gs L Q)).toList
  readsOpens : AllOpen (readIn p s r₁ r₂ gs L Q).st (readIn p s r₁ r₂ gs L Q).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (readIn p s r₁ r₂ gs L Q).book
    (treesOf (readIn p s r₁ r₂ gs L Q)) (readIn p s r₁ r₂ gs L Q).opened
  inRange : ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
    v < 2 ^ ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logN
  groupCode : (frontAt s L Q).T.shape.code = s.check.frame.shape.code
  copiesCode : ∀ k ∈ (frontAt s L Q).T.kept.toList, k.shape.code = s.check.frame.shape.code
  claimMain : Own.formFits (frontAt s L Q).f.rows.c
    ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logEll = true
  own : ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
    ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
      (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
      (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
      (0 < m.life → 0 < n.shape.mainRows)
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (readIn p s r₁ r₂ gs L Q))
    (flat p gs) = []
  groups : gs.length = p.read.length

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **`LinkPlain`, whole, at a reached state, from what is left.** -/
theorem link_plain_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hz : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (E : LinkLeft (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀) :
    LinkPlain (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀ z₀ c₀ := by
  obtain ⟨L', Q', c', z', f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr a nm
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans f4)
  obtain rfl : Q = Q' := Option.some.inj (hQ.symm.trans f5)
  obtain rfl : c₀ = c' := Option.some.inj (hc.symm.trans f6)
  obtain rfl : z₀ = z' := Option.some.inj (hz.symm.trans f7)
  have hfirst := link_first_reached hS hR O h23 hr
  have hx := link_front_at hS hR O hF hpl h23 hP hn hr hfirst f4 f5
  obtain ⟨x', hx', d1, d2, d3, d4, d5⟩ :=
    link_draws_own hS hR O hF hpl h23 hP hn hr a nm r₁ r₂ he hrf
  obtain rfl : x' = frontAt s L Q := Except.ok.inj (hx'.symm.trans hx)
  have SH := link_shape_reached hS hR O hF hpl hy hcut hB h23 hr hx
  have PB := link_public_reached hS hR O hF hpl hy hcut hB h23 hr hx
  obtain ⟨m1, m2, m3⟩ := link_members_reached hS hR O h23 hr L Q
  obtain ⟨b1, b2⟩ := link_book_reached hS hR O h23 hr L Q (par9 (k2P Z a nm .link n))
    (sentOf (k2P Z a nm .link n) s L Q r₁ r₂) r₂ (flat (k2P Z a nm .link n) gs)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := (link_lay_reached hS hR O h23 hr L Q).reads
    (i := inFront (par9 (k2P Z a nm .link n)) (frontAt s L Q) s.book
      (sentOf (k2P Z a nm .link n) s L Q r₁ r₂) r₂ (flat (k2P Z a nm .link n) gs)) rfl rfl
  have hN := (sw_link hS hR O hF hpl h23 hP hn hr).2 _ hx
  exact
    { stands := rfl, range := d1, here := f1, due := f2
      waits := link_waits_reached hS hR O h23 hr, first := hfirst, later := f3, link := f4
      group := f5, code := f6, maskCode := f7, shorter := f8, plain := E.plain, number := f9
      entry := by rw [hN]; exact he
      fits₁ := E.fits₁, plan := E.plan, step := f10, draw := d2, vals := E.vals, poss := d3
      trits := d4, factor := d5, answers := E.answers, trees := E.trees, oldCode := f11
      loc := E.loc
      reads :=
        { masks := f12 _ _ _, challenges := l1, maskVars := l2, keptSize := l3, mainSize := l4
          maskSize := l5, placed := b1, stated := b2, own := E.readsOwn, opens := E.readsOpens
          fits := l6, keptRows := l7, fresh := l8 }
      front :=
        { check := SH.check, restMain := PB.restMain
          fits :=
            { mainVars := SH.mainVars, d0 := SH.d0, d1 := SH.d1, rows := m1, named := m2
              once := SH.once, keptCode := SH.keptCode
              stored := link_stored_reached hS hR O hF hpl h23 hP hn hr L Q }
          keptPos := f13, keptAnswers := PB.keptAnswers, lengths := PB.lengths, logC := PB.logC
          logZ := PB.logZ, inRange := E.inRange, groupCode := E.groupCode
          copiesCode := E.copiesCode
          tables :=
            { bitsG := PB.bitsG, bitsKept := SH.bitsKept, claimMain := E.claimMain
              claimKept := m3
              stored := link_tables_paid hS hR O hF hpl hy hcut hB h23 hr hx f13 }
          reads := link_reads_paid hS hR O hF hpl hy hcut hB h23 hr hx }
      own := E.own, noneLeft := E.noneLeft, groups := E.groups }

/-- **So the kind's own decision says yes there.** -/
theorem link_returns_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (hrf : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : LinkLeft (k2P Z a nm .link n) s r₁ r₂ gs L Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Z a nm .link n) s [r₁, r₂] gs = .ok s' := by
  obtain ⟨_, _, _, z₀, -, -, -, -, -, -, hz, -⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr a nm
  exact link_returns_sent
    (link_plain_reached hS hR O hF hpl hy hcut hB h23 hP hn hr a nm r₁ r₂ gs he hrf hL hQ hc hz E)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_plain_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_reached
