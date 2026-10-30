-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/SendOwnLaw.lean: THE TIE BETWEEN THE SEATED LINK AND THE LAWS' MIDDLE TERM, IN ONE
DIRECTION: where the seated text (Johnson/Desc/Link/LinkDesc.lean: the kind K1's own block at the
sending; its names bear the letter V) says yes, the text that the
laws speak of (Johnson/Desc/Link/LinkDescWithGroundSend.lean: the plain ground's sendP at the sending) says yes,
with the same record at the chain's end. So whatever is proved of a yes of descOf | linkDesc holds
of a yes of linkDescriptionAt | linkDescV.
  SendPOfDecide      A PROPOSITION, A PREMISE HERE, in the form of a theorem (K1/Law/SendP3.lean:
  sendP_of_decide, there of its own namespace's sendP; here of Desc.Plain.sendP: a yes of
  K1.decideSend, where the block's test on the plan passes, the plan's codes' lengths are in
                     order and the two rounds fit, is a yes of sendP with the same numbers and the
                     same record): its conclusion is taken weaker here (the three middle values are
                     left open)
  sendP_re           the plain ground's sending does not read the chain's own named values: general
  sendK1_send        K1's own block's decision at the link says yes  ==>  K15's send says yes with
  the same record
  sendK1_under       the same of the two blocks as steps
  foldBlocks_mono    general: block by block, a step's yes gives the other's: so the fold's
  planOk_alike       general: the tests on the plan read of a block its name, place, rounds,
  oracles, before and its own test
  descV_planOk · descV_runEnd · descV_run · linkDescV_run      the tie at the tests on the plan and
  at the decision
ONE DIRECTION ALONE. That a yes of the elder text gives a yes of the seated one is not stated (K1's
own block asks more). Nothing on soundness by itself, on an honest prover or on hiding.

-/
import Johnson.Desc.K15.K15Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {S Cl : Type}

/-- roundsFit does not read the sealed digest. -/
theorem roundsFit_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    simp only [List.map_cons]
    unfold roundsFit
    rw [roundsFit_noDigest ds rs]
    rfl

theorem roundsFit_two' (a b : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [a, b] rs = true) :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  match rs, h with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  | [], h => simp [roundsFit] at h
  | [_], h => simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [roundsFit] at h

/-- Two blocks with the same rounds: where, on rounds that fit, a yes of the one's decision gives
the other's with the same record, a yes of the one's step gives the other's. -/
theorem step_mono (ft : Nat) (b b' : Block S Cl) (hr : b.rounds = b'.rounds)
    (hd : ∀ s rs gs s', roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      b'.decide s (rs.map noDigest) gs = .ok s')
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × Nat) (h : b.step ft s rs cols = .ok out)
        :
    b'.step ft s rs cols = .ok out := by
  obtain ⟨s', k⟩ := out
  obtain ⟨h1, h2, h3, h4⟩ := step_inv ft b s s' rs cols k h
  subst h2
  have h4' := hd _ _ _ _ h1 h4
  unfold Block.step need
  rw [← hr]
  simp only [bind, Except.bind, pure, Except.pure, h1, if_true, h3, beq_self_eq_true, h4']

/-- One block stands under another for the fold. -/
def StepUnder (ft : Nat) (b b' : Block S Cl) : Prop :=
  b.rounds = b'.rounds ∧ ∀ s rs cols out, b.step ft s rs cols = .ok out → b'.step ft s rs cols = .ok
      out

theorem StepUnder.refl (ft : Nat) (b : Block S Cl) : StepUnder ft b b := ⟨rfl, fun _ _ _ _ h => h⟩

theorem foldBlocks_mono (ft : Nat) (l l' : List (Block S Cl))
    (hll : List.Forall₂ (StepUnder ft) l l') :
    ∀ s rs cols out, foldBlocks ft l s rs cols = .ok out → foldBlocks ft l' s rs cols = .ok out :=
        by
  induction hll with
  | nil => intro s rs cols out h; exact h
  | @cons b b' l l' hb _ ih =>
    intro s rs cols out h
    obtain ⟨s', k, h1, h2, h3⟩ := foldBlocks_cons ft b l s rs cols out h
    unfold foldBlocks
    simp only [List.splitAt_eq]
    rw [← hb.1]
    simp only [h1, ne_eq, not_true_eq_false, if_false, hb.2 _ _ _ _ h2]
    exact ih _ _ _ _ h3

/-! ## The tests on the plan -/

/-- What the tests on the plan read of a block, but for its own test. -/
def Alike (b b' : Block S Cl) : Prop :=
  b.name = b'.name ∧ b.place = b'.place ∧ b.rounds = b'.rounds ∧ b.oracles = b'.oracles ∧ b.before =
      b'.before ∧
    (b.planOk = true → b'.planOk = true)

theorem Alike.refl (b : Block S Cl) : Alike b b := ⟨rfl, rfl, rfl, rfl, rfl, id⟩

theorem alike_rounds (l l' : List (Block S Cl)) (h : List.Forall₂ Alike l l') :
    l.flatMap (·.rounds) = l'.flatMap (·.rounds) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.flatMap_cons, hb.2.2.1, ih]

theorem alike_places (l l' : List (Block S Cl)) (h : List.Forall₂ Alike l l') : placesOf l =
    placesOf l' := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold placesOf at ih ⊢
    simp only [List.map_cons, hb.1, hb.2.1, hb.2.2.1, ih]

theorem alike_sent (l l' : List (Block S Cl)) (h : List.Forall₂ Alike l l') : sentOf l = sentOf
    l' := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold sentOf at ih ⊢
    simp only [List.flatMap_cons, hb.2.2.2.1, ih]

theorem alike_oracles (l l' : List (Block S Cl)) (h : List.Forall₂ Alike l l') : oraclesOf l =
    oraclesOf l' := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold oraclesOf at ih ⊢
    simp only [List.flatMap_cons, hb.2.2.2.1, ih]

theorem alike_before (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) (l l' : List (Block S Cl))
    (h : List.Forall₂ Alike l l') : ∀ n, beforeAt D O c n l = beforeAt D O c n l' := by
  induction h with
  | nil => intro n; rfl
  | @cons b b' l l' hb _ ih =>
    intro n
    unfold beforeAt
    rw [hb.2.2.2.2.1, hb.2.2.1, ih]

theorem alike_blocksOk (l l' : List (Block S Cl)) (h : List.Forall₂ Alike l l')
    (hk : blocksOk l = true) :
    blocksOk l' = true := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold blocksOk at hk ih ⊢
    simp only [List.all_cons, Bool.and_eq_true] at hk ⊢
    refine ⟨⟨hb.2.2.2.2.2 hk.1.1, ?_⟩, ih hk.2⟩
    have : b'.shaped = b.shaped := by unfold Block.shaped; rw [hb.2.2.1, hb.2.2.2.1]
    rw [this]
    exact hk.1.2

variable {Xi : Type}

/-- **The tests on the plan read of a block its name, place, rounds, oracles, before and its own
test.** -/
theorem OneChainFileDescription.planOk_alike (F : OneChainFileDescription Xi) (c' : Chain F.S F.Cl)
    (h : List.Forall₂ Alike F.chain.blocksInOrder c'.blocksInOrder)
    (hp : F.planOk = true) : ({ F with chain := c' } : OneChainFileDescription Xi).planOk = true := by
  have hb : blocksOk F.chain.blocksInOrder = true := OneChainFileDescription.planOk_blocks F hp
  have hb' := alike_blocksOk _ _ h hb
  have e1 := alike_rounds _ _ h
  have e2 := alike_places _ _ h
  have e3 := alike_sent _ _ h
  have e4 := alike_oracles _ _ h
  have e5 := fun D O c n => alike_before D O c _ _ h n
  simp only [OneChainFileDescription.planOk, OneChainFileDescription.asFile, FileDescription.planOkCore, FileDescription.roundsDeclaredByBlocks, FileDescription.labelsOk,
      FileDescription.lastChainFirstTreeNumber,
    FileDescription.placesOk, FileDescription.places, FileDescription.beforeOk, FileDescription.treeSharingOk, FileDescription.roots,
        FileDescription.readsOk, FileDescription.sentFit,
    OneChainFileDescription.storedOk, OneChainFileDescription.roundsDeclaredByBlocks] at hp ⊢
  rw [← e1, ← e2, ← e3, ← e4, hb']
  simp only [← e5]
  rw [hb] at hp
  exact hp

end VerifiableInference.Desc

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block foldBlocks OneChainFileDescription OpenedColumn chainAt blocksOk roundsFit noDigest
    named Alike StepUnder)
open VerifiableInference.Desc.Ground (recvP admitP)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)
open VerifiableInference.Desc.K1 (decideSend planOkOwn)

/-- **The premise** (in the form of K1/Law/SendP3.lean's sendP_of_decide, at Desc.Plain's constants;
there the three middle values are named: the elements drawn, the answers, their number). -/
def SendPOfDecide : Prop :=
  ∀ (L : Type) (P : VerifiableInference.Desc.K1.Par) (owed : Option Nat) (d d' : DState L)
      (r₁ r₂ : Fmt.RoundView) (ids : Array Nat),
    planOkOwn P = true → P.codes.lengthsOk = true → roundsFit (VerifiableInference.Desc.K1.rounds P)
        [r₁, r₂] = true →
    decideSend P owed d [r₁, r₂] = .ok (ids, d') →
    ∃ sd an need, sendP groundG P.gp true d P.sent r₁ r₂ = some (ids, sd, an, need, d')

/-! ## The plain ground's sending does not read the chain's own named values -/

variable {L M : Type}

/-- The same record with other named values. -/
def reL (d : DState L) (m : M) : DState M :=
  { st := d.st, book := d.book, roots := d.roots, opened := d.opened, loc := m }

theorem recvP_re (ft : Nat) (d : DState L) (m : M) (sent : Array OracleNotice) :
    recvP ft (reL d m) sent = (recvP ft d sent).map fun x => (x.1, reL x.2 m) := by
  unfold recvP reL
  by_cases hk : VerifiableInference.Desc.Ground.ok (VerifiableInference.Desc.Ground.recvL d.st
      d.book sent) = true
  · simp only [hk, if_true]
    cases VerifiableInference.Desc.Own.treesMade d.st.codes sent <;> rfl
  · simp [hk]

theorem admitP_re (d : DState L) (m : M) (o : Nat) (rows : Array Row) :
    admitP (reL d m) o rows = (admitP d o rows).map (reL · m) := by
  unfold admitP reL
  by_cases hk : VerifiableInference.Desc.Ground.ok (VerifiableInference.Desc.Ground.admitL d.st o
      rows) = true
  · simp only [hk, if_true, Option.bind_eq_bind]
    cases d.st.oracles[o]? with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      cases VerifiableInference.Desc.Own.padMade d.st.codes x.shape <;> rfl
  · simp [hk]

theorem sampleLoop_re (p : GPar) (codes : Codes) (seeds : List SampleSeed) (m : M) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d : DState L),
      sampleLoop groundG p codes seeds l ys (reL d m) =
        (sampleLoop groundG p codes seeds l ys d).map fun x => (reL x.1 m, x.2)
  | [], _, _ => rfl
  | (o, s) :: l, ys, d => by
    unfold sampleLoop
    cases rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => rfl
    | some x =>
      obtain ⟨rows, ys'⟩ := x
      have ha : (groundG (L := M)).admit p (reL d m) o rows =
          ((groundG (L := L)).admit p d o rows).map (reL · m) := admitP_re d m o rows
      simp only [ha]
      cases (groundG (L := L)).admit p d o rows with
      | none => rfl
      | some d' =>
        simp only [Option.map_some]
        exact sampleLoop_re p codes seeds m l ys' d'

theorem bind_map_comm {α β γ : Type} (a : Option α) (f₁ : α → Option γ) (f₂ : α → Option β)
    (g : β → γ)
    (h : ∀ x, f₁ x = (f₂ x).map g) : a.bind f₁ = (a.bind f₂).map g := by
  cases a with
  | none => rfl
  | some x => exact h x

theorem ite_map_comm {β γ : Type} (c : Prop) [Decidable c] (a : Option γ) (b : Option β) (g : β → γ)
    (h : a = b.map g) : (if c then a else none) = (if c then b else none).map g := by
  split
  · exact h
  · rfl

theorem sendP_re (p : GPar) (own : Bool) (d : DState L) (m : M) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) :
    sendP groundG p own (reL d m) sent r₁ r₂ =
      (sendP groundG p own d sent r₁ r₂).map fun x =>
        (x.1, x.2.1, x.2.2.1, x.2.2.2.1, reL x.2.2.2.2 m) := by
  unfold sendP
  have hr : (groundG (L := M)).recv p (reL d m) sent =
      ((groundG (L := L)).recv p d sent).map fun x =>
        (x.1, reL x.2 m) := recvP_re p.firstTree d m sent
  simp only [Option.bind_eq_bind, hr]
  cases (groundG (L := L)).recv p d sent with
  | none => rfl
  | some x =>
    obtain ⟨ids, d₁⟩ := x
    have hst : (reL d₁ m).st = d₁.st := rfl
    simp only [Option.map_some, Option.bind_some, hst]
    refine bind_map_comm _ _ _ _ fun shapes => ?_
    refine bind_map_comm _ _ _ _ fun seeds => ?_
    refine bind_map_comm _ _ _ _ fun an => ?_
    refine ite_map_comm _ _ _ _ ?_
    rw [sampleLoop_re]
    cases sampleLoop groundG p d₁.st.codes seeds _ an d₁ with
    | none => rfl
    | some y =>
      obtain ⟨d₂, left⟩ := y
      simp only [Option.map_some, Option.bind_some]
      split <;> rfl

/-! ## The sending -/

theorem parK1_sent (P : P15) : (parK1 P).sent = linkMessage P.S P.set.samples := by
  simp [VerifiableInference.Desc.K1.Par.sent, parK1, sent]

/-- **K1's own block's decision at the link says yes: so does K15's send, with the same record.** -/
theorem sendK1_send (hSP : SendPOfDecide) (P : P15) (hl : P.codes.lengthsOk = true)
    (hpl : planOkOwn (parK1 P) = true)
    (d d' : St) (r2 r3 : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 P)) [r2, r3] = true)
    (h : (sendK1 P).decide d [r2, r3] gs = .ok d') : send P.par d [r2, r3] = some d' := by
  change ((decideSend (parK1 P) none (reL d (#[] : Array Nat)) [r2, r3]).map fun x =>
      ({ owed := none, held := { x.2 with loc := x.1 } } :
        VerifiableInference.Desc.K1.Owing (DState (Array Nat)))).bind
    (fun t => named "the sending's numbers are not those that the kind notes"
      (behind P.par { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                             opened := t.held.opened } t.held.loc)) = .ok d' at h
  cases hq : decideSend (parK1 P) none (reL d (#[] : Array Nat)) [r2, r3] with
  | error e => rw [hq] at h; cases h
  | ok x =>
    obtain ⟨ids, D'⟩ := x
    rw [hq] at h
    change named _ (behind P.par (reL D' d.loc) ids) = .ok d' at h
    obtain ⟨sd, an, need, hs⟩ := hSP _ (parK1 P) none _ D' r2 r3 ids hpl hl hfit hq
    rw [parK1_sent] at hs
    have hre : sendP groundG P.par.gp true d (linkMessage P.par.S P.par.samples) r2 r3 =
        some (ids, sd, an, need, reL D' d.loc) := by
      have := sendP_re P.par.gp true (reL d (#[] : Array Nat)) d.loc
          (linkMessage P.par.S P.par.samples) r2 r3
      rw [show sendP groundG P.par.gp true (reL d (#[] : Array Nat))
          (linkMessage P.par.S P.par.samples) r2 r3 =
        some (ids, sd, an, need, D') from hs] at this
      exact this
    unfold send
    simp only [hre, Option.bind_eq_bind, Option.bind_some]
    cases hb : behind P.par (reL D' d.loc) ids with
    | none => rw [hb] at h; cases h
    | some y => rw [hb] at h; injection h with h; rw [h]


/-! ## The two blocks as steps; the fold -/

theorem sendK1_under (hSP : SendPOfDecide) (P : P15) (hl : P.codes.lengthsOk = true)
    (hpl : planOkOwn (parK1 P) = true) : StepUnder 0 (sendK1 P) (bSend P (fiveOf P)) := by
  refine ⟨rfl, fun s rs cols out h =>
    VerifiableInference.Desc.step_mono 0 (sendK1 P) (bSend P (fiveOf P)) rfl ?_ s rs cols out h⟩
  intro s rs gs s' hf hd
  change roundsFit (VerifiableInference.Desc.K1.rounds (parK1 P)) rs = true at hf
  obtain ⟨r2, r3, rfl⟩ := VerifiableInference.Desc.roundsFit_two' _ _ rs hf
  have hf' : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 P)) [noDigest r2, noDigest r3] =
      true := by
    have := VerifiableInference.Desc.roundsFit_noDigest (VerifiableInference.Desc.K1.rounds
        (parK1 P)) [r2, r3]
    simp only [List.map_cons, List.map_nil] at this
    rw [this]
    exact hf
  simp only [List.map_cons, List.map_nil] at hd ⊢
  have := sendK1_send hSP P hl hpl s s' _ _ gs hf' hd
  change why [] (send P.par s [noDigest r2, noDigest r3]) = .ok s'
  rw [this]
  rfl

theorem blocksV_eq (P : P15) (es : List Fmt.Entry) (he : entries P = some es) :
    blocksOrV P = [bPoint P es, sendK1 P, bRec P es, bLink P es, bPhi P es] := by
  unfold blocksOrV linkBlocksBeforeTest
  simp only [he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some]
  rfl

theorem blocksV_none (P : P15) (he : entries P = none) : blocksOrV P = blocksOr P := by
  have hbad : blocksOr P =
      [{ VerifiableInference.Desc.roundlessBlock "the kind's rounds cannot be said" 1 none 1 .ok with
          planOk := false }] := by
    unfold blocksOr blocks
    simp [he]
  rw [hbad]
  unfold blocksOrV linkBlocksBeforeTest
  simp [he]

/-- The two texts declare the same rounds. -/
theorem roundsV (P : P15) :
    (blocksOrV P ++ [testBlock P]).flatMap (·.rounds) = (blocksOr P ++ [testBlock P]).flatMap
        (·.rounds) := by
  cases he : entries P with
  | none => rw [blocksV_none P he]
  | some es =>
    obtain ⟨_, _, rfl⟩ := entries_inv P es he
    rw [blocksV_eq P _ he, blocks_eq P _ he]
    rfl

/-- The seated chain's flat list (Chain.blocksInOrder's order: first · front · links · back · last). -/
theorem flatV_eq (P : P15) :
    (linkProtocolChain P).blocksInOrder = ((frontBlock P :: blocksOrV P) ++ tailOf P).map
      fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
  unfold VerifiableInference.Desc.Chain.blocksInOrder linkProtocolChain tailOf
  simp only [roundsV, List.map_nil, List.flatMap_nil, List.append_nil, List.nil_append,
    List.map_append, List.map_cons, List.cons_append, List.append_assoc]

/-- The elder chain's flat list. -/
theorem flatOf_eq (P : P15) :
    (chainOf P).blocksInOrder = ((frontBlock P :: blocksOr P) ++ tailOf P).map
      fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
  unfold VerifiableInference.Desc.Chain.blocksInOrder chainOf tailOf
  simp only [List.map_nil, List.flatMap_nil, List.append_nil, List.nil_append,
    List.map_append, List.map_cons, List.cons_append, List.append_assoc]

theorem flat_foldV (P : P15) (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    foldBlocks 0 (linkProtocolChain P).blocksInOrder s rs cols =
      foldBlocks 0 ((frontBlock P :: blocksOrV P) ++ tailOf P) s rs cols := by
  rw [flatV_eq, VerifiableInference.Desc.foldBlocks_planOk]

theorem forall₂_refl {α : Type} (R : α → α → Prop) (hR : ∀ a, R a a) : ∀ l : List α, List.Forall₂ R
    l l
  | [] => .nil
  | a :: l => .cons (hR a) (forall₂_refl R hR l)

/-- **The fold over the seated blocks says yes: so does the fold over the blocks that the laws speak
of, with the same end.** -/
theorem foldV (hSP : SendPOfDecide) (P : P15) (hl : P.codes.lengthsOk = true)
    (hpl : planOkOwn (parK1 P) = true)
    (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 ((frontBlock P :: blocksOrV P) ++ tailOf P) s rs cols = .ok out) :
    foldBlocks 0 ((frontBlock P :: blocksOr P) ++ tailOf P) s rs cols = .ok out := by
  cases he : entries P with
  | none => rw [blocksV_none P he] at h; exact h
  | some es =>
    obtain ⟨_, _, rfl⟩ := entries_inv P es he
    rw [blocksV_eq P _ he] at h
    rw [blocks_eq P _ he]
    refine VerifiableInference.Desc.foldBlocks_mono 0 _ _ ?_ s rs cols out h
    refine .cons (StepUnder.refl 0 _) (.cons (StepUnder.refl 0 _)
        (.cons (sendK1_under hSP P hl hpl) ?_))
    exact forall₂_refl _ (StepUnder.refl 0) _

theorem chainV_at (hSP : SendPOfDecide) (P : P15) (hl : P.codes.lengthsOk = true)
    (hpl : planOkOwn (parK1 P) = true)
    (s e : St) (v : Fmt.View) (h : chainAt "the chain" 0 (linkProtocolChain P).blocksInOrder s v = .ok e) :
    chainAt "the chain" 0 (chainOf P).blocksInOrder s v = .ok e := by
  unfold chainAt at h
  split at h
  · cases h
  · rw [flat_foldV] at h
    split at h
    · rename_i s' hfold
      injection h with h
      subst h
      have hO := foldV hSP P hl hpl _ _ _ _ hfold
      have hne : (chainOf P).blocksInOrder.isEmpty = false := rfl
      unfold chainAt
      rw [flat_fold, hO]
      simp [hne]
    · cases h
    · cases h

/-! ## The tests on the plan -/

theorem flat_alike (P : P15) : List.Forall₂ Alike (linkProtocolChain P).blocksInOrder (chainOf P).blocksInOrder := by
  cases he : entries P with
  | none =>
    rw [flatV_eq, flatOf_eq, blocksV_none P he]
    exact forall₂_refl _ Alike.refl _
  | some es =>
    obtain ⟨_, _, rfl⟩ := entries_inv P es he
    rw [flatV_eq, flatOf_eq, blocksV_eq P _ he, blocks_eq P _ he]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.map_append]
    refine .cons (Alike.refl _) (.cons (Alike.refl _) (.cons ⟨rfl, rfl, rfl, rfl, rfl, fun _ =>
      rfl⟩ ?_))
    exact forall₂_refl _ Alike.refl _

/-- **Where the seated text's tests on the plan pass, so do those of the text that the laws speak
of.** -/
theorem descV_planOk (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (linkDescriptionAt P plan ok).planOk = true) :
    (descOf P plan ok).planOk = true :=
  OneChainFileDescription.planOk_alike (linkDescriptionAt P plan ok) (chainOf P) (flat_alike P) h

/-- Where the seated text's tests on the plan pass, K1's own block's test on the plan has passed at
the link. -/
theorem descV_own (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (linkDescriptionAt P plan ok).planOk = true) :
    planOkOwn (parK1 P) = true := by
  obtain ⟨es, he⟩ := entries_of_planOk P plan ok (descV_planOk P plan ok h)
  have hb := OneChainFileDescription.planOk_blocks _ h
  change blocksOk (linkProtocolChain P).blocksInOrder = true at hb
  unfold blocksOk at hb
  rw [List.all_eq_true] at hb
  have hm : ({ sendK1 P with planOk := (sendK1 P).planOk && (sendK1 P).hasNoClaimsAndNothingAfter } : Block St Unit) ∈
      (linkProtocolChain P).blocksInOrder := by
    rw [flatV_eq, blocksV_eq P es he]
    simp
  have := hb _ hm
  simp only [Bool.and_eq_true] at this
  have h1 : (sendK1 P).planOk = true := this.1.1
  change (planOkOwn (parK1 P) && _ && _) = true at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

/-! ## The decision -/

/-- **THE TIE.** Where the seated text's decision ends well, the decision of the text that the laws
speak of ends well, at the same record. -/
theorem descV_runEnd (hSP : SendPOfDecide) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (x : TableKey × TableKey)
    (v : Fmt.View) (e : St) (h : (linkDescriptionAt P plan ok).runEnd x v = .ok e) : (descOf P plan ok).runEnd x
        v = .ok e := by
  unfold OneChainFileDescription.runEnd at h ⊢
  simp only [bind, Except.bind, pure, Except.pure, VerifiableInference.Desc.need] at h ⊢
  cases hw : (linkDescriptionAt P plan ok).planWord with
  | some w => simp [hw, throwThe, MonadExceptOf.throw] at h
  | none =>
    have hpV := OneChainFileDescription.planWord_none _ hw
    have hpO := descV_planOk P plan ok hpV
    have hl := (front_ok P plan ok hpO).1
    have hpl := descV_own P plan ok hpV
    have hwO : (descOf P plan ok).planWord = none := by
      unfold OneChainFileDescription.planWord
      simp [hpO]
    rw [hw] at h
    rw [hwO]
    simp only at h ⊢
    by_cases hx : (descOf P plan ok).okStart x = true
    · have hx' : (linkDescriptionAt P plan ok).okStart x = true := hx
      simp only [hx', if_true] at h
      simp only [hx, if_true]
      by_cases hv : VerifiableInference.Desc.viewWordsBelowPrime v = true
      · simp only [hv, if_true] at h ⊢
        cases hch : chainAt "the chain" 0 (linkDescriptionAt P plan ok).chain.blocksInOrder ((linkDescriptionAt P plan ok).start x) v
            with
        | error e' => rw [hch] at h; simp at h
        | ok dEnd =>
          rw [hch] at h
          have hO : chainAt "the chain" 0 (descOf P plan ok).chain.blocksInOrder ((descOf P plan ok).start x)
              v = .ok dEnd :=
            chainV_at hSP P hl hpl _ _ v hch
          rw [hO]
          exact h
      · simp [hv] at h
    · have hx' : ¬ (linkDescriptionAt P plan ok).okStart x = true := hx
      simp [hx'] at h

theorem descV_run (hSP : SendPOfDecide) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (x : TableKey × TableKey)
    (v : Fmt.View) (h : (linkDescriptionAt P plan ok).run x v = true) : (descOf P plan ok).run x v = true := by
  unfold OneChainFileDescription.run at h ⊢
  cases hr : (linkDescriptionAt P plan ok).runEnd x v with
  | error e => rw [hr] at h; simp [Except.isOk, Except.toBool] at h
  | ok e => rw [descV_runEnd hSP P plan ok x v e hr]; rfl

/-- **At the link's description.** -/
theorem linkDescV_run (hSP : SendPOfDecide) (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (x : TableKey × TableKey)
    (v : Fmt.View) (h : (linkDescV c plan).run x v = true) : (linkDesc c plan).run x v = true :=
  descV_run hSP (p15Of c) plan _ x v h

end Desc.K15

#print axioms VerifiableInference.Desc.foldBlocks_mono
#print axioms VerifiableInference.Desc.OneChainFileDescription.planOk_alike
#print axioms Desc.K15.sendP_re
#print axioms Desc.K15.sendK1_send
#print axioms Desc.K15.descV_planOk
#print axioms Desc.K15.descV_runEnd
#print axioms Desc.K15.linkDescV_run
