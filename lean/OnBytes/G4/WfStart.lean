-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfStart.lean: the context at which the lookups of a key's chain are called, if the steps
before them went through.

`Wf.rowsVerify` (OnBytes/Iop/Wf.lean) tests its parameters, receives and samples the oracle message
with the multiplicities, makes a group, lets the message join it, and calls the lookups. Here, by
inversion: if a run of `Wf.rowsVerify` on a view gave a value, what the context of that call is.

Main names:
  `startCheck_inv`: what the test of the parameters says, and that it leaves the context.
  `joinFacts_of_ok`: if the making of the group and the joining went through, `JoinFacts` holds.
  `AtCall`: the facts on the context behind SEND.
  `rowsVerify_inv`: a run of `Wf.rowsVerify` that gave a value has called the lookups at
  `withNewGroupOfMessage c1 x.messageId s.code s.maskCode`, with `AtCall`.
  `bitsOf`, `placeB`, `startLedger`, `padOf`: what the statement behind the joining says of the
  oracle message, as functions of the codes and the message's shape.
  `planesB`, `padB`, `ledgerB`: three tests on public data alone.
  `WfStartReady`: WHAT IS ASKED AT THE START OF THE BLOCK: twelve fields: two marks and one ledger
  of the context, the plan's next entries, the form of the view's next rounds, four public facts.
  `callReady_of_start`, `rowsVerify_callReady`: from these, `WfCallReady` (OnBytes/G4/WfCall.lean)
  for lookup number 0 at the context of the call.
Limits: inversions alone: nothing says that a run goes through. `WfStartReady` is a hypothesis: it
  is shown of no context here. No theorem shows an object at which the two premises of
  `rowsVerify_callReady` hold together, a run that gives a value and `WfStartReady`.

  The field `plan` is meant for plans that the planner makes: a run that gives a value does
  not force it (the blocks read neither an entry's work nor its number of message bytes). The fields
  `rounds` and `fits` lean on what the strict reader of the files guarantees of a view, not on
  anything that the program's blocks test (OnBytes/G4/WfCall.lean says what). That the context of
  `rowsVerify_callReady` is tied to the run is not shown here.
  Its public fields are not shown here to follow from `Wf.admitted`; `ledgerB` walks through all
  entries that the ledger can give, so that at full size it wants a proof and not an evaluation.
  Only lookup number 0 is treated.


-/
import OnBytes.G4.WfJoin
import OnBytes.G4.SendLeaves
import OnBytes.G4.WfRoom

set_option autoImplicit false

namespace OnBytes.G4

open Blk OnBytes.Params

/-- What the test at the start says; it leaves the context as it is. -/
theorem startCheck_inv {x : WfPublic} {m : Wf.Matrix} {indexMasksId : Nat} {u : Unit} {c c' : Ctx}
    (h : (Wf.startCheck x m indexMasksId) c = .ok (u, c')) :
    c' = c ∧ Wf.admitted c.st.codes x m = true ∧
      ∃ y, c.st.oracles[indexMasksId]? = some y ∧ y.sampled = true := by
  unfold Wf.startCheck at h
  obtain ⟨S, c1, h1, k1⟩ := bind_inv h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  obtain ⟨_, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨ha, rfl⟩ := must_inv h2
  obtain ⟨y, c3, h3, k3⟩ := bind_inv k2
  obtain ⟨hy, rfl⟩ := oracle_inv h3
  obtain ⟨_, c4, h4, k4⟩ := bind_inv k3
  obtain ⟨hs, rfl⟩ := must_inv h4
  obtain ⟨cc, c5, h5, k5⟩ := bind_inv k4
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h5)
  obtain ⟨-, rfl⟩ := must_inv k5
  simp only [Bool.and_eq_true] at hs
  exact ⟨rfl, ha, y, hy, hs.1⟩

/-- What `Wf.admitted` says, as far as it is used here. -/
theorem admitted_inv {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) :
    x.lookups ≠ [] ∧ x.message.shape.maskRows ≠ 0 ∧
      Wf.ownMasks x m ≤ Send.freeMaskEntries x.message.shape.maskRows
        (codes.mask.getD x.message.shape.maskCode default).ell x.message.shape.answers := by
  simp only [Wf.admitted, Wf.publicOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  have hp := h.1.1.1.1.1.1.1.1.1
  exact ⟨hp.1.1.1.1.1, hp.1.1.1.2, h.1.1.2⟩

theorem group_inv {g : Nat} {G : Group} {c c' : Ctx} (h : (Blk.group g) c = .ok (G, c')) :
    c.st.groups[g]? = some G ∧ c' = c := by
  obtain ⟨S, c1, h1, h2⟩ := bind_inv (x := Blk.statement)
    (f := fun S => Blk.get (S.groups[g]?)) h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  exact get_inv h2

/-- What the making of a group leaves. -/
theorem newGroup_inv {code maskCode g : Nat} {c c' : Ctx}
    (h : (Blk.newGroup code maskCode) c = .ok (g, c')) :
    g = c.st.groups.size ∧ c' = withGroups c (c.st.groups.push (emptyGroup code maskCode)) ∧
      ∃ a z, c.st.codes.base[code]? = some a ∧ c.st.codes.mask[maskCode]? = some z ∧
        z.logN ≤ a.logN := by
  unfold Blk.newGroup at h
  obtain ⟨S, c1, h1, k1⟩ := bind_inv h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  obtain ⟨a, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨ha, rfl⟩ := get_inv h2
  obtain ⟨z, c3, h3, k3⟩ := bind_inv k2
  obtain ⟨hz, rfl⟩ := get_inv h3
  obtain ⟨_, c4, h4, k4⟩ := bind_inv k3
  obtain ⟨hle, rfl⟩ := must_inv h4
  obtain ⟨_, c5, h5, k5⟩ := bind_inv k4
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h5)
  obtain ⟨rfl, rfl⟩ := pure_inv k5
  exact ⟨rfl, rfl, a, z, ha, hz, by simpa using hle⟩

/-- If the making of the group and the joining went through, what they test holds. -/
theorem joinFacts_of_ok {α : Type} {code maskCode o : Nat} {f : Nat → Blk α} {c c' : Ctx} {r : α}
    (h : ((Blk.newGroup code maskCode) >>= fun g => (Blk.join g o) >>= fun _ => f g) c =
      .ok (r, c')) : ∃ y, JoinFacts c o code maskCode y := by
  obtain ⟨g, c1, h1, k1⟩ := bind_inv h
  obtain ⟨rfl, rfl, hcodes⟩ := newGroup_inv h1
  obtain ⟨_, c2, h2, -⟩ := bind_inv k1
  unfold Blk.join at h2
  obtain ⟨G, d1, e1, j1⟩ := bind_inv h2
  obtain ⟨hG, rfl⟩ := group_inv e1
  obtain ⟨y, d2, e2, j2⟩ := bind_inv j1
  obtain ⟨hy, rfl⟩ := oracle_inv e2
  obtain ⟨_, d3, e3, j3⟩ := bind_inv j2
  obtain ⟨m1, rfl⟩ := must_inv e3
  obtain ⟨_, d4, e4, j4⟩ := bind_inv j3
  obtain ⟨m2, rfl⟩ := must_inv e4
  obtain ⟨_, d5, e5, -⟩ := bind_inv j4
  obtain ⟨m3, rfl⟩ := must_inv e5
  have eG : G = emptyGroup code maskCode := by
    have : (c.st.groups.push (emptyGroup code maskCode))[c.st.groups.size]? = some G := hG
    simpa using this.symm
  subst eG
  simp only [Bool.and_eq_true] at m1
  exact ⟨y, hy, m1.1, hcodes, m2, m3⟩

/-- The facts on the context c1 behind SEND, c0 being the context at which the block is called. -/
structure AtCall (c0 c1 : Ctx) (x : WfPublic) (m : Wf.Matrix) (indexMasksId : Nat) : Prop where
  /-- there is a lookup -/
  someLookup : x.lookups ≠ []
  /-- the oracle message has mask rows -/
  maskRows : x.message.shape.maskRows ≠ 0
  /-- the oracle message's ledger has room for what all lookups take of it -/
  ownRoom : Wf.ownMasks x m ≤ Send.freeMaskEntries x.message.shape.maskRows
    (c0.st.codes.mask.getD x.message.shape.maskCode default).ell x.message.shape.answers
  /-- the oracle message's number is the number of messages before it -/
  number : x.messageId = c0.st.oracles.size
  codes : c1.st.codes = c0.st.codes
  groups : c1.st.groups = c0.st.groups
  view : c1.ch.dry = false
  keepNotes : c1.keepNotes = c0.keepNotes
  closed : c1.ch.cur = none
  notAsked : c1.ch.askedRows = false
  /-- SEND has taken the plan's next two entries -/
  entries : ∃ e1 e2, c0.ch.entries = e1 :: e2 :: c1.ch.entries ∧ e1.name = "SEND seed" ∧
    e2.name = "SEND answer" ∧ c1.ch.last = some e2
  /-- SEND has taken exactly two rounds, if none was open -/
  rounds : c0.ch.cur = none → ∃ r1 r2, c0.ch.left = r1 :: r2 :: c1.ch.left
  /-- the index-mask message was there, was sampled, and is as it was -/
  indexMasks : ∃ y, c0.st.oracles[indexMasksId]? = some y ∧ y.sampled = true ∧
    c1.st.oracles[indexMasksId]? = some y
  /-- the oracle message is as `Send.admit` leaves it at its shape -/
  message : ∃ rows places, Send.pad c0.st.codes x.message.shape = some places ∧
    c1.st.oracles[x.messageId]? =
      some (admitAs c0.st.codes x.message.shape rows places { shape := x.message.shape })

theorem messageOf_head (x : WfPublic) : (Wf.messageOf x)[0]? = some x.message := by
  unfold Wf.messageOf
  split
  · split <;> rfl
  · rfl

/-- A run of `Wf.rowsVerify` on a view that gave a value has called the lookups at the context
`withNewGroupOfMessage c1 ..`, with the group's number and the codes as named, and `AtCall` holds of c1. -/
theorem rowsVerify_inv {x : WfPublic} {table : LinShape} {indexMasksId : Nat}
    {r : Wf.Output × Option Nat} {c0 c' : Ctx}
    (h : (Wf.rowsVerify x table indexMasksId) c0 = .ok (r, c')) (hv : c0.ch.dry = false) :
    ∃ c1 pending c2, AtCall c0 c1 x (Wf.matrixOf table) indexMasksId ∧
      (Wf.lookupsVerify x (Wf.matrixOf table) c0.st.codes c0.st.groups.size indexMasksId 0
          x.lookups [])
        (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) =
        .ok (pending, c2) := by
  unfold Wf.rowsVerify at h
  try dsimp only at h
  obtain ⟨_, a1, h1, k1⟩ := bind_inv h
  obtain ⟨rfl, hadm, y2, hy2, hs2⟩ := startCheck_inv h1
  obtain ⟨ids, c1, h2, k2⟩ := bind_inv k1
  obtain ⟨message, a3, h3, k3⟩ := bind_inv k2
  obtain ⟨hid, rfl⟩ := get_inv h3
  obtain ⟨_, a4, h4, k4⟩ := bind_inv k3
  obtain ⟨hmsg, rfl⟩ := must_inv h4
  have hmsg' : message = x.messageId := by simpa using hmsg
  subst hmsg'
  try dsimp only at k4
  obtain ⟨hids, hcodes, hgroups, -, hdry, hkeep, hold, hnew, hown⟩ := sendVerify_inv h2 hv
  obtain ⟨hent, -⟩ := sendVerify_flow h2 hv
  have hleft := sendVerify_rounds h2 hv
  obtain ⟨e, hlast, -, hcur, hask⟩ := hown rfl
  have hnum : x.messageId = a1.st.oracles.size := by
    have h0 := hid
    rw [hids, Array.getElem?_map] at h0
    obtain ⟨v, hv0, hv1⟩ := Option.map_eq_some_iff.1 h0
    obtain ⟨_, hval⟩ := Array.getElem?_eq_some_iff.1 hv0
    rw [Array.getElem_range] at hval
    omega
  obtain ⟨y, hJ⟩ := joinFacts_of_ok k4
  have hmess : ∃ rows places, Send.pad a1.st.codes x.message.shape = some places ∧
      a4.st.oracles[x.messageId]? =
        some (admitAs a1.st.codes x.message.shape rows places { shape := x.message.shape }) := by
    have hn := hnew 0 x.message (messageOf_head x)
    rw [Nat.add_zero, ← hnum] at hn
    rcases hn with e0 | e0
    · have ey := hJ.message
      rw [e0] at ey
      have hs := hJ.sampled
      rw [← Option.some.inj ey] at hs
      cases hs
    · exact e0
  have k5 := (join_val a4 x.messageId x.message.shape.code x.message.shape.maskCode y hJ
    (fun group st => (Wf.lookupsVerify x (Wf.matrixOf table) st.codes group indexMasksId 0
      x.lookups []) >>= fun pending =>
        (pure (({ pending := pending, message := x.messageId, group := group } : Wf.Output),
          if x.choice.masksRide = true then ids[1]? else none) :
          Blk (Wf.Output × Option Nat)))).symm.trans k4
  obtain ⟨pending, c2, hL, -⟩ := bind_inv k5
  obtain ⟨ad1, ad2, ad3⟩ := admitted_inv hadm
  refine ⟨a4, pending, c2, ⟨ad1, ad2, ad3, hnum, hcodes, hgroups, hdry, hkeep, hcur, hask, hent,
    hleft, ⟨y2, hy2, hs2, hold _ _ hy2 hs2⟩, hmess⟩, ?_⟩
  have e1 : (withNewGroupOfMessage a4 x.messageId x.message.shape.code x.message.shape.maskCode).st.codes =
      a1.st.codes := hcodes
  rw [e1, hgroups] at hL
  exact hL

/-! ## The statement behind the joining -/

theorem joined_self {c : Ctx} {o code maskCode : Nat} {y : Oracle}
    (h : c.st.oracles[o]? = some y) :
    (withNewGroupOfMessage c o code maskCode).st.oracles[o]? =
      some { y with groups := y.groups ++ [c.st.groups.size] } := by
  simp [withNewGroupOfMessage, Array.getElem?_modify, h]

theorem joined_other {c : Ctx} {o o' code maskCode : Nat} (h : o ≠ o') :
    (withNewGroupOfMessage c o code maskCode).st.oracles[o']? = c.st.oracles[o']? := by
  simp [withNewGroupOfMessage, Array.getElem?_modify, h]

theorem joined_group (c : Ctx) (o code maskCode : Nat) :
    (withNewGroupOfMessage c o code maskCode).st.groups[c.st.groups.size]? =
      some (oneGroup o code maskCode) := by
  simp [withNewGroupOfMessage]

/-! ## Public tests -/

/-- The number of index bits of a table of a message, from the codes and the message's shape. -/
def bitsOf (codes : Codes) (s : OracleShape) (part : Part) : Nat :=
  ceilLog2 (s.rows part) +
    (if s.rows part == 0 then 0
     else match part with
       | .main => (codes.base.getD s.code default).logEll
       | .mask => (codes.mask.getD s.maskCode default).logEll)

/-- `placeOk` for the one member of a group, from the codes and the member's shape. -/
def placeB (codes : Codes) (s : OracleShape) (part : Part) (vars index : Nat) : Bool :=
  decide (0 < s.rows part) && vars == bitsOf codes s part &&
    decide (index < 2 ^ bitsOf codes s part)

theorem tableBits_eq {S : Statement} {o : Nat} {y : Oracle} (h : S.oracles[o]? = some y)
    (part : Part) : S.tableBits o part = bitsOf S.codes y.shape part := by
  cases part <;> simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, bitsOf, h]

theorem placeOk_eq {S : Statement} {o code maskCode : Nat} {y : Oracle}
    (h : S.oracles[o]? = some y) (part : Part) (vars index : Nat) :
    placeOk S (oneGroup o code maskCode) o part vars index =
      placeB S.codes y.shape part vars index := by
  simp [placeOk, placeB, Statement.has, h, tableBits_eq h]

/-- The ledger that `Send.admit` gives a message with mask rows, from the codes and its shape. -/
def startLedger (codes : Codes) (s : OracleShape) : Ledger :=
  { next := 0,
    left := Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers,
    rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows }

/-- The entries that mask the answers to a sample, from the codes and the message's shape. -/
def padOf (codes : Codes) (s : OracleShape) : List (Part × Nat) :=
  ((Send.pad codes s).getD []).map fun p => (p.part, p.index)

/-- PUBLIC. The blocks of planes of lookup i lie in the main table of the oracle message. -/
def planesB (codes : Codes) (x : WfPublic) (i : Nat) : Bool :=
  ((Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == i)).all fun k =>
    decide (blockVars x codes i k ≤ 63) &&
      placeB codes x.message.shape .main (blockVars x codes i k) 0

/-- PUBLIC. No entry that masks an answer lies in the main table. -/
def padB (codes : Codes) (s : OracleShape) : Bool :=
  (padOf codes s).all fun p => !(Part.main == p.1)

/-- PUBLIC. Every entry that the ledger of the oracle message can give lies in the mask table and
masks no answer. -/
def ledgerB (codes : Codes) (s : OracleShape) : Bool :=
  (takesOf (startLedger codes s) (startLedger codes s).left).1.all fun i =>
    placeB codes s .mask (bitsOf codes s .mask) i &&
      (padOf codes s).all fun p => !(Part.mask == p.1 && i == p.2)

/-- WHAT IS ASKED AT THE START OF THE BLOCK, in the place of `WfCallReady` at the first lookup. c0:
the context at which `Wf.rowsVerify` is called. -/
structure WfStartReady (c0 : Ctx) (x : WfPublic) (m : Wf.Matrix) (indexMasksId work : Nat)
    (rs : List FlatRound) (es' tailEntries : List Fmt.Entry) (tailRounds : List Fmt.RoundView)
    (l2 : Ledger) : Prop where
  /-- The run keeps no intermediate values. -/
  noNotes : c0.keepNotes = false
  /-- No round is open. -/
  closed : c0.ch.cur = none
  /-- THE PLAN. Its next entries are two of SEND, the second without batched rows, then those of the
  first lookup, then es', then tailEntries. -/
  plan : ∃ e1 e2, c0.ch.entries = e1 :: e2 ::
      (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD 0 default)) work es' ++
        tailEntries) ∧ e2.rows = 0
  /-- THE VIEW. Behind two rounds come the plain rounds rs, then tailRounds. -/
  rounds : ∃ r1 r2, c0.ch.left = r1 :: r2 :: (rvs rs ++ tailRounds)
  /-- THE VIEW. The rounds rs fit the entries of the first lookup and es', one by one. -/
  fits : FitsAll rs (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD 0 default)) work es')
  /-- The index-mask message has the ledger l2. -/
  second : (c0.st.oracles[indexMasksId]?).bind Oracle.ledger = some l2
  /-- That ledger is open. -/
  secondOpen : l2.closed = false
  /-- That ledger has as many entries left as all lookups take of it. -/
  secondRoom : Wf.indexMasks x m ≤ l2.left
  /-- PUBLIC. Every lookup passes the program's test of form, and mu + d is at most 63. -/
  lookups : ∀ S ∈ Wf.lookupsOf x m, S.ok = true ∧ S.mu + S.d ≤ 63
  /-- PUBLIC. The blocks of planes of the first lookup lie in the main table. -/
  planes : planesB c0.st.codes x 0 = true
  /-- PUBLIC. No entry that masks an answer lies in the main table. -/
  pad : padB c0.st.codes x.message.shape = true
  /-- PUBLIC. What the oracle message's ledger can give lies in the mask table and masks no answer.
  -/
  ledger : ledgerB c0.st.codes x.message.shape = true

/-- FROM THE START OF THE BLOCK TO THE FIRST LOOKUP: what is asked at the start, with what the
steps before the lookups leave, gives `WfCallReady` for lookup number 0 at the context of the call.
-/
theorem callReady_of_start {c0 c1 : Ctx} {x : WfPublic} {m : Wf.Matrix}
    {indexMasksId work : Nat} {rs : List FlatRound} {es' tailEntries : List Fmt.Entry}
    {tailRounds : List Fmt.RoundView} {l2 : Ledger} (ha : AtCall c0 c1 x m indexMasksId)
    (hr : WfStartReady c0 x m indexMasksId work rs es' tailEntries tailRounds l2) :
    WfCallReady (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x m
      c0.st.codes 0 c0.st.groups.size indexMasksId work rs es' tailEntries tailRounds
      (startLedger c0.st.codes x.message.shape) l2
      (oneGroup x.messageId x.message.shape.code x.message.shape.maskCode) := by
  obtain ⟨rows, places, hpad, hmsg⟩ := ha.message
  obtain ⟨y2, hy2, hs2, hy2'⟩ := ha.indexMasks
  have hlk := ha.someLookup
  have hmask := ha.maskRows
  have hown := ha.ownRoom
  have hne : x.messageId ≠ indexMasksId := by
    have := (Array.getElem?_eq_some_iff.1 hy2).1
    have := ha.number
    omega
  have oJ := joined_self (code := x.message.shape.code) (maskCode := x.message.shape.maskCode) hmsg
  have o2 : (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode).st.oracles[
                     indexMasksId]? = some y2 := (joined_other hne).trans hy2'
  have gJ : (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode).st.groups[
                     c0.st.groups.size]? =
      some (oneGroup x.messageId x.message.shape.code x.message.shape.maskCode) := by
    rw [← ha.groups]
    exact joined_group c1 _ _ _
  have cJ : (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode).st.codes =
      c0.st.codes := ha.codes
  have hgo : ∀ i, (wfSeat (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x m
      c0.st.codes i c0.st.groups.size indexMasksId).groupOf =
      oneGroup x.messageId x.message.shape.code x.message.shape.maskCode := by
    intro i
    simp [Seat.groupOf, wfSeat, gJ]
  have hpo : ∀ i, (wfSeat (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x m
      c0.st.codes i c0.st.groups.size indexMasksId).padsOf x.messageId =
      padOf c0.st.codes x.message.shape := by
    intro i
    simp [Seat.padsOf, wfSeat, oJ, admitAs, padOf, hpad]
  have hpos : 0 < x.lookups.length := List.length_pos_iff.2 hlk
  have hmem : Wf.lookupOf x.messageId m (x.lookups.getD 0 default) ∈ Wf.lookupsOf x m := by
    rw [lookupOf_getD x m 0 hpos]
    exact List.getElem_mem _
  have hroom := room_at x m (fun S hS => (hr.lookups S hS).1) _ l2.left hown hr.secondRoom 0 hpos
  rw [takenOwn_zero, takenKey_zero, Nat.sub_zero, Nat.sub_zero] at hroom
  obtain ⟨e1, e2, hE, -, -, hlast⟩ := ha.entries
  obtain ⟨f1, f2, hF, hrows⟩ := hr.plan
  rw [hE] at hF
  have hF1 := (List.cons.inj hF).2
  have he2 : e2 = f2 := (List.cons.inj hF1).1
  have hent := (List.cons.inj hF1).2
  obtain ⟨r1, r2, hL⟩ := ha.rounds hr.closed
  obtain ⟨q1, q2, hQ⟩ := hr.rounds
  rw [hL] at hQ
  have hleft := (List.cons.inj (List.cons.inj hQ).2).2
  refine ⟨?_, ha.view, ha.keepNotes.trans hr.noNotes, ha.notAsked, ha.closed, ?_, ?_, ?_, gJ,
    ready_of_ok _ rfl (hr.lookups _ hmem).1 (hr.lookups _ hmem).2, ?_, ?_, hent, hleft, hr.fits⟩
  · unfold wfFacts
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨by simpa using hne, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [oJ]
      rfl
    · rw [o2]
      simpa using hs2
    · rw [gJ]
      rfl
    · rw [hgo]
      rfl
    · have hp := hr.planes
      unfold planesB at hp
      rw [List.all_eq_true] at hp ⊢
      intro k hk
      have h1 := hp k hk
      rw [hgo, placeOk_eq oJ, cJ]
      exact h1
    · rw [hgo]
      have hp := hr.pad
      unfold padB at hp
      simp only [oneGroup, Array.all_eq_true_iff_forall_mem]
      intro q hq
      have eq : q = x.messageId := by simpa using hq
      subst eq
      rw [hpo]
      rw [List.all_eq_true] at hp ⊢
      intro p hpm
      simpa using hp p hpm
  · intro e he
    have : c1.ch.last = some e := he
    rw [hlast] at this
    rw [← Option.some.inj this, he2]
    exact hrows
  · rw [oJ]
    simp [admitAs, startLedger, Nat.pos_of_ne_zero hmask]
  · rw [o2, ← hy2]
    exact hr.second
  · have hled : (wfSeat (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x m
        c0.st.codes 0 c0.st.groups.size indexMasksId).ledB x.messageId
        (startLedger c0.st.codes x.message.shape) = true := by
      have hp := hr.ledger
      unfold ledgerB at hp
      unfold Seat.ledB
      rw [Bool.and_eq_true]
      refine ⟨rfl, ?_⟩
      rw [List.all_eq_true] at hp ⊢
      intro i hi
      have h1 := hp i hi
      rw [Bool.and_eq_true] at h1
      unfold Seat.slotB
      rw [Bool.and_eq_true, hgo]
      refine ⟨?_, ?_⟩
      · show placeOk (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode).st
          (oneGroup x.messageId x.message.shape.code x.message.shape.maskCode) x.messageId .mask
          ((withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode).st.tableBits
            x.messageId .mask) i = true
        rw [placeOk_eq oJ, tableBits_eq oJ, cJ]
        exact h1.1
      · simp only [Array.all_eq_true_iff_forall_mem]
        intro q hq
        have eq : q = x.messageId := by simpa using hq
        subst eq
        rw [hpo]
        have h2 := h1.2
        rw [List.all_eq_true] at h2 ⊢
        intro p hpm
        simpa using h2 p hpm
    show _ ≤ if (wfSeat (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x m
        c0.st.codes 0 c0.st.groups.size indexMasksId).ledB x.messageId
        (startLedger c0.st.codes x.message.shape) = true
      then (startLedger c0.st.codes x.message.shape).left else 0
    rw [if_pos hled]
    exact hroom.1
  · show _ ≤ if l2.closed = true then 0 else l2.left
    rw [hr.secondOpen]
    exact hroom.2

/-- THE TWO TOGETHER: a run of `Wf.rowsVerify` on a view that gave a value, from a context at which
`WfStartReady` holds, has called the lookups at a context at which `WfCallReady` holds for lookup
number 0. -/
theorem rowsVerify_callReady {x : WfPublic} {table : LinShape} {indexMasksId work : Nat}
    {r : Wf.Output × Option Nat} {c0 c' : Ctx} {rs : List FlatRound}
    {es' tailEntries : List Fmt.Entry} {tailRounds : List Fmt.RoundView} {l2 : Ledger}
    (h : (Wf.rowsVerify x table indexMasksId) c0 = .ok (r, c')) (hv : c0.ch.dry = false)
    (hr : WfStartReady c0 x (Wf.matrixOf table) indexMasksId work rs es' tailEntries tailRounds
      l2) :
    ∃ c1 pending c2,
      (Wf.lookupsVerify x (Wf.matrixOf table) c0.st.codes c0.st.groups.size indexMasksId 0
          x.lookups [])
        (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) =
        .ok (pending, c2) ∧
      WfCallReady (withNewGroupOfMessage c1 x.messageId x.message.shape.code x.message.shape.maskCode) x
        (Wf.matrixOf table) c0.st.codes 0 c0.st.groups.size indexMasksId work rs es' tailEntries
        tailRounds (startLedger c0.st.codes x.message.shape) l2
        (oneGroup x.messageId x.message.shape.code x.message.shape.maskCode) := by
  obtain ⟨c1, pending, c2, ha, hL⟩ := rowsVerify_inv h hv
  exact ⟨c1, pending, c2, hL, callReady_of_start ha hr⟩

end OnBytes.G4

#print axioms OnBytes.G4.rowsVerify_callReady
#print axioms OnBytes.G4.rowsVerify_inv
#print axioms OnBytes.G4.callReady_of_start
