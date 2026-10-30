-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PubAtDoor.lean: wherever the eight sub-protocols of the shared
chain's linear claim return a state, from the chain's first state, that state's public part
(`pubSt`, FitShared.lean) is a term made from the plan alone. For every key, all rounds and all
columns. So the hypothesis of `pubOf_doorOf` (FitSharedLaw.lean) holds at the test on G_u.

  `pubG`, `PubGroup.enter`   a group without its rows; such a group with one member more
  `pubBehind`      the public part behind the eight, made from the plan
  `Mid`            the facts that are carried from sub-protocol to sub-protocol: the codes; there
                   are two groups, and what each is without its rows; the messages' shapes
  `mid_point`, `mid_send`, `mid_rec`, `mid_loc`, `mid_joined`, `mid_zeta`, `mid_split`
                   one step each
  `Behind`, `behind_eight`   the facts behind the eight, field by field, from the eight decisions
  `Behind.pub`     these facts give `pubSt d.st = pubBehind Q sentU`
  `behind_fold`    the same from the fold over the eight blocks (`foldBlocks`)
  `pub_at_U`       so the state on entry to the test on G_u has the public part
                   `(pubBehind Q sentU, 0)`
  `door_U`, `door_U_front` `pubOf (doorOf ..) = (pubBehind Q sentU, 0)` for every input and whatever
                   precedes the test, without a hypothesis on the run; the second with the chain's
                   front block before the eight
  `sent_jobU`, `sent_jobOmega`   the two sendings' lists of messages are `withU` and `withOmega`

By what. For each of the eight the library has a theorem that writes out the state behind a return,
field by field (Johnson/Desc/Key/Laid/: `laid_point`, `send_laid`, `laid_rec`, `laid_loc`,
`joined_joins`, `laid_zeta`, `laid_split`). From the fold to the decisions: `foldBlocks_cons_ok`
(Johnson/Desc/RunLaws.lean) and `step_decide` (Johnson/Desc/ChainEndFold.lean).

Limits. Two public premises on the plan: the shape splits the row over two codes
(`sharedSplitNeeded`), and the first fold's mask goes out with o_u (`masksAhead`). Other plans are
not treated. Statements of the form "where it returns": that the eight return at any input is not
shown here. The key and the columns decide whether they return, and what the open rows hold. The
test on G_omega is not treated here: PubNear.lean. `doorOf` returns its parameter `fall` where the
fold or `enter` fails, so `door_U` and `door_U_front` are also true of that fall-back: they do not
tell a fold that failed from one that returned, and they are no statement that the state on entry is
the verifier's. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitSharedLaw
import Johnson.Desc.Key.Laid.Laid2
import Johnson.Desc.Key.Laid.Draws
import Johnson.Desc.Key.Laid.Split
import Johnson.Desc.Key.Laid.AtBlocks
import Johnson.Desc.RunLaws
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Key (PointLaid RecLaid LocLaid Joined ZetaLaid SplitLaid entered noted
  laid_point laid_rec laid_loc joined_joins laid_zeta laid_split blocks_eight)
open VerifiableInference.Desc.Key.LaidW (SendLaid send_laid sendAt_yes inFrontOf)
open Desc.K14 (P14 St blocks first withU withOmega sendAt behindU behindOmega frontBlock)
open Desc.K14.Law (why_some parK1_sent split_one)
open ProofFile.Honest.K14 (jobU jobOmega)

/-! ## 1 On arrays -/

/-- Two arrays of messages with the same shape at every number have the same shapes. -/
theorem shapes_eq {A B : Array OnBytes.Oracle}
    (h : ∀ o : ℕ, (B[o]?).map (·.shape) = (A[o]?).map (·.shape)) :
    B.map (·.shape) = A.map (·.shape) :=
  Array.ext_getElem? fun o => by
    rw [Array.getElem?_map, Array.getElem?_map]
    exact h o

/-- A message that is turned by a function that leaves the shape keeps its shape. -/
theorem shape_turned {A B : Array OnBytes.Oracle} (hs : B.size = A.size) (o : ℕ)
    (f : OnBytes.Oracle → OnBytes.Oracle) (hf : ∀ x, (f x).shape = x.shape)
    (h : ∀ x, A[o]? = some x → B[o]? = some (f x)) :
    (B[o]?).map (·.shape) = (A[o]?).map (·.shape) := by
  cases hA : A[o]? with
  | some x =>
    rw [h x hA]
    exact congrArg some (hf x)
  | none =>
    have h1 : A.size ≤ o := Array.getElem?_eq_none_iff.1 hA
    rw [Array.getElem?_eq_none_iff.2 (hs ▸ h1)]

/-- The shapes behind a sending: the elder ones, then the notices'. -/
theorem shapes_sent {A B : Array OnBytes.Oracle} (sent : Array OracleNotice)
    (hs : B.size = A.size + sent.size) (ho : ∀ o, o < A.size → B[o]? = A[o]?)
    (hn : ∀ (i : ℕ) (n : OracleNotice), sent[i]? = some n →
      ∃ x : OnBytes.Oracle, B[A.size + i]? = some x ∧ x.shape = n.shape) :
    B.map (·.shape) = A.map (·.shape) ++ sent.map (·.shape) := by
  apply Array.ext_getElem?
  intro o
  rw [Array.getElem?_map, Array.getElem?_append, Array.size_map]
  by_cases h : o < A.size
  · rw [if_pos h, Array.getElem?_map, ho o h]
  · rw [if_neg h, Array.getElem?_map]
    obtain ⟨i, rfl⟩ : ∃ i, o = A.size + i := ⟨o - A.size, by omega⟩
    rw [Nat.add_sub_cancel_left]
    cases hi : sent[i]? with
    | some n =>
      obtain ⟨x, hx, e⟩ := hn i n hi
      rw [hx]
      exact congrArg some e
    | none =>
      have h1 : sent.size ≤ i := Array.getElem?_eq_none_iff.1 hi
      rw [Array.getElem?_eq_none_iff.2 (by omega : B.size ≤ A.size + i)]
      rfl

/-- An array of two entries, mapped. -/
theorem map_two {α β : Type} (f : α → β) (B : Array α) (a b : β) (hs : B.size = 2)
    (h0 : (B[0]?).map f = some a) (h1 : (B[1]?).map f = some b) : B.map f = #[a, b] := by
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_map]
  match i with
  | 0 => simpa using h0
  | 1 => simpa using h1
  | k + 2 =>
    rw [Array.getElem?_eq_none_iff.2 (by omega : B.size ≤ k + 2)]
    simp

/-- The numbers that a sending hands back. -/
theorem ids_at {ids : Array ℕ} {m k i j : ℕ} (h : ids = (Array.range m).map (· + k))
    (hi : ids[i]? = some j) : j = i + k := by
  subst h
  obtain ⟨hl, e⟩ := Array.getElem?_eq_some_iff.1 hi
  simp only [Array.getElem_map, Array.getElem_range] at e
  exact e.symm

/-! ## 2 A group without its rows -/

/-- A group without its rows. -/
def pubG (G : OnBytes.Group) : PubGroup := ⟨G.code, G.maskCode, G.members, G.kept⟩

/-- One member more, entered behind the smaller members: `entered`
(Johnson/Desc/Key/Laid/JoinedDef.lean) on a group without its rows. -/
def PubGroup.enter (X : PubGroup) (o : ℕ) (k : Bool) : PubGroup :=
  { X with
    members := X.members.insertIdxIfInBounds (X.members.filter (· < o)).size o
    kept := X.kept.insertIdxIfInBounds (X.members.filter (· < o)).size k }

theorem pubG_entered (G : OnBytes.Group) (o : ℕ) (k : Bool) :
    pubG (entered G o k) = (pubG G).enter o k := rfl

theorem enter_first (a b o : ℕ) :
    (⟨a, b, #[], #[]⟩ : PubGroup).enter o false = ⟨a, b, #[o], #[false]⟩ := by
  simp [PubGroup.enter]

theorem enter_second (a b o o' : ℕ) (h : o < o') :
    (⟨a, b, #[o], #[false]⟩ : PubGroup).enter o' false = ⟨a, b, #[o, o'], #[false, false]⟩ := by
  simp [PubGroup.enter, h]

/-- **The public part behind the eight sub-protocols**, made from the plan. sentU: what goes out
with o_u. -/
def pubBehind (Q : P14) (sentU : Array OracleNotice) : PubState :=
  ⟨Q.codes,
   #[⟨Q.S.fold.u.code, Q.S.sharedMaskCode, #[0, sentU.size + 1], #[false, false]⟩,
     ⟨Q.S.omega.code, Q.S.sharedMaskCode, #[sentU.size, sentU.size + 1], #[false, false]⟩],
   (sentU ++ withOmega Q.S).map (·.shape)⟩

/-! ## 3 What is carried, and the steps -/

/-- The codes; two groups, and what each is without its rows; the messages' shapes. -/
structure Mid (d : St) (c : Codes) (X0 X1 : PubGroup) (sh : Array OracleShape) : Prop where
  codes : d.st.codes = c
  groups : d.st.groups.size = 2
  g0 : (d.st.groups[0]?).map pubG = some X0
  g1 : (d.st.groups[1]?).map pubG = some X1
  shapes : d.st.oracles.map (·.shape) = sh

section Steps
variable {p : Desc.Plain.Par} {d d' : St} {c : Codes} {X0 X1 : PubGroup} {sh : Array OracleShape}

/-- Behind "LIN point", from the chain's first state. -/
theorem mid_point {key : TableKey} {r : Fmt.RoundView} (L : PointLaid p (first c key) d' r) :
    Mid d' c ⟨p.S.fold.u.code, p.S.sharedMaskCode, #[], #[]⟩
      ⟨p.S.omega.code, p.S.sharedMaskCode, #[], #[]⟩ #[] ∧ d'.loc.gU = 0 ∧ d'.loc.gOmega = 1 ∧
      d'.st.oracles.size = 0 :=
  ⟨⟨L.codes, by rw [L.groups]; rfl, by rw [L.groups]; rfl, by rw [L.groups]; rfl,
    by rw [L.oracles]; exact Array.map_empty⟩, by rw [L.loc]; rfl, by rw [L.loc]; rfl,
    by rw [L.oracles]; rfl⟩

/-- Behind a sending. -/
theorem mid_send {P : VerifiableInference.Desc.K1.Par} {x : Desc.Plain.DState (Array ℕ)}
    {ids : Array ℕ} (M : Mid d c X0 X1 sh) (L : SendLaid P (inFrontOf d) x ids)
    (e : d'.st = x.st) : Mid d' c X0 X1 (sh ++ P.sent.map (·.shape)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]
    exact L.codes.trans M.codes
  · rw [e, L.groups]
    exact M.groups
  · rw [e, L.groups]
    exact M.g0
  · rw [e, L.groups]
    exact M.g1
  · rw [e, ← M.shapes]
    exact shapes_sent P.sent L.size L.older fun i n hi => by
      obtain ⟨y, hy, hs, _⟩ := L.new i n hi
      exact ⟨y, hy, hs⟩

/-- Behind "(rec_gamma)". -/
theorem mid_rec {GU : OnBytes.Group} {rows : List OnBytes.Row} (M : Mid d c X0 X1 sh)
    (L : RecLaid p d d' GU rows) (hU : d.loc.gU = 0) :
    Mid d' c (X0.enter d.loc.oU.oracle false) X1 sh := by
  have a := L.gU'
  have b := L.gU
  rw [hU] at a b
  have m := M.g0
  rw [b] at m
  refine ⟨L.codes.trans M.codes, L.groups.trans M.groups, ?_, ?_, ?_⟩
  · rw [a, ← Option.some.inj m]
    rfl
  · rw [L.other 1 (by rw [hU]; decide)]
    exact M.g1
  · refine (shapes_eq fun o => ?_).trans M.shapes
    by_cases h : o = d.loc.oU.oracle
    · subst h
      exact shape_turned L.size _ (fun x => noted x [d.loc.gU]) (fun _ => rfl) L.u
    · rw [L.rest o h]

/-- Behind "LOC". -/
theorem mid_loc {r : Fmt.RoundView} {GU : OnBytes.Group} {rows : List OnBytes.Row}
    (M : Mid d c X0 X1 sh) (L : LocLaid p d d' r GU rows) (hU : d.loc.gU = 0) :
    Mid d' c X0 X1 sh := by
  have a := L.gU'
  have b := L.gU
  rw [hU] at a b
  have m := M.g0
  rw [b] at m
  refine ⟨L.codes.trans M.codes, L.groups.trans M.groups, ?_, ?_, ?_⟩
  · rw [a, ← Option.some.inj m]
    rfl
  · rw [L.other 1 (by rw [hU]; decide)]
    exact M.g1
  · rw [L.oracles]
    exact M.shapes

/-- Behind the joinings. -/
theorem mid_joined {GU GO : OnBytes.Group} (M : Mid d c X0 X1 sh) (L : Joined d d' GU GO)
    (hU : d.loc.gU = 0) (hO : d.loc.gOmega = 1) :
    Mid d' c (X0.enter d.loc.oSp false)
      ((X1.enter d.loc.oOmega false).enter d.loc.oSp false) sh := by
  have a := L.gU'
  have b := L.gU
  have a' := L.gO'
  have b' := L.gO
  rw [hU] at a b
  rw [hO] at a' b'
  have m := M.g0
  have m' := M.g1
  rw [b] at m
  rw [b'] at m'
  refine ⟨L.codes.trans M.codes, L.groups.trans M.groups, ?_, ?_, ?_⟩
  · rw [a, ← Option.some.inj m]
    rfl
  · rw [a', ← Option.some.inj m']
    rfl
  · refine (shapes_eq fun o => ?_).trans M.shapes
    by_cases h : o = d.loc.oOmega
    · subst h
      exact shape_turned L.size _ (fun x => noted x [d.loc.gOmega]) (fun _ => rfl) L.omega
    · by_cases h' : o = d.loc.oSp
      · subst h'
        exact shape_turned L.size _ (fun x => noted x [d.loc.gOmega, d.loc.gU]) (fun _ => rfl)
          L.sp
      · rw [L.rest o h h']

/-- Behind "LIN zeta". -/
theorem mid_zeta {r : Fmt.RoundView} (M : Mid d c X0 X1 sh) (L : ZetaLaid d d' r) :
    Mid d' c X0 X1 sh := by
  rw [L.is]
  exact ⟨M.codes, M.groups, M.g0, M.g1, M.shapes⟩

/-- Behind "SPLIT". -/
theorem mid_split {S : OnBytes.Params.LinShape} {GU GO : OnBytes.Group} {x : OnBytes.Oracle}
    {l : OnBytes.Ledger} {n : ℕ} {row : OnBytes.Row} {mu : OnBytes.E} (M : Mid d c X0 X1 sh)
    (L : SplitLaid S d d' GU GO x l n row mu) (hU : d.loc.gU = 0) (hO : d.loc.gOmega = 1) :
    Mid d' c X0 X1 sh := by
  have a := L.gU'
  have b := L.gU
  have a' := L.gO'
  have b' := L.gO
  rw [hU] at a b
  rw [hO] at a' b'
  have m := M.g0
  have m' := M.g1
  rw [b] at m
  rw [b'] at m'
  refine ⟨L.codes.trans M.codes, L.groups.trans M.groups, ?_, ?_, ?_⟩
  · rw [a, ← Option.some.inj m]
    rfl
  · rw [a', ← Option.some.inj m']
    rfl
  · refine (shapes_eq fun o => ?_).trans M.shapes
    by_cases h : o = d.loc.oSp
    · subst h
      rw [L.sp', L.sp]
      rfl
    · rw [L.msgs o h]

end Steps

/-! ## 4 The two sendings' decisions -/

/-- The sending's decision returns at two rounds alone. -/
theorem sent_two {L : Type} {Q : VerifiableInference.Desc.K1.Par} {owed : Option ℕ}
    {d d' : Desc.Plain.DState L} {rs : List Fmt.RoundView} {ids : Array ℕ}
    (h : VerifiableInference.Desc.K1.decideSend Q owed d rs = .ok (ids, d')) :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  unfold VerifiableInference.Desc.K1.decideSend at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- What a return of "send o_u" gives, where masks are sent ahead. -/
theorem sentU_facts (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List ℕ)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hM : P.par.S.masksAhead = true)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d rs gs = .ok d') :
    ∃ ids x i0 i1, SendLaid Q (inFrontOf d) x ids ∧ d'.st = x.st ∧ ids[0]? = some i0 ∧
      ids[1]? = some i1 ∧ d'.loc.gU = d.loc.gU ∧ d'.loc.gOmega = d.loc.gOmega ∧
      d'.loc.oU.oracle = i0 ∧ d'.loc.firstMask = some i1 := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨r₁, r₂, rfl⟩ := sent_two hx
  unfold behindU at hb
  rw [if_pos hM] at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq] at hb
  obtain ⟨m, ⟨i1, h1, rfl⟩, i0, h0, rfl⟩ := hb
  exact ⟨ids, x, i0, i1, send_laid _ _ _ _ _ _ _ hx, rfl, h0, h1, rfl, rfl, rfl, rfl⟩

/-- What a return of "send o_omega" gives, where the shape splits. -/
theorem sentO_facts (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List ℕ)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hS : P.par.S.sharedSplitNeeded = true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d rs gs = .ok d') :
    ∃ ids x i0 i1, SendLaid Q (inFrontOf d) x ids ∧ d'.st = x.st ∧ ids[0]? = some i0 ∧
      ids[1]? = some i1 ∧ d'.loc.gU = d.loc.gU ∧ d'.loc.gOmega = d.loc.gOmega ∧
      d'.loc.firstMask = d.loc.firstMask ∧ d'.loc.oOmega = i0 ∧ d'.loc.oSp = i1 := by
  obtain ⟨ids, x, hx, hb⟩ := sendAt_yes _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨r₁, r₂, rfl⟩ := sent_two hx
  unfold behindOmega at hb
  rw [if_pos hS] at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨i1, h1, i0, h0, rfl⟩ := hb
  exact ⟨ids, x, i0, i1, send_laid _ _ _ _ _ _ _ hx, rfl, h0, h1, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5 Behind the eight -/

/-- **The facts behind the eight sub-protocols**, field by field. -/
structure Behind (Q : P14) (sentU : Array OracleNotice) (d : St) : Prop where
  mid : Mid d Q.codes
    ⟨Q.S.fold.u.code, Q.S.sharedMaskCode, #[0, sentU.size + 1], #[false, false]⟩
    ⟨Q.S.omega.code, Q.S.sharedMaskCode, #[sentU.size, sentU.size + 1], #[false, false]⟩
    ((sentU ++ withOmega Q.S).map (·.shape))
  gU : d.loc.gU = 0
  gOmega : d.loc.gOmega = 1
  mask : d.loc.firstMask = some 1

/-- These facts give the public part. -/
theorem Behind.pub {Q : P14} {sentU : Array OracleNotice} {d : St} (B : Behind Q sentU d) :
    pubSt d.st = pubBehind Q sentU := by
  unfold pubSt pubBehind
  rw [B.mid.codes, B.mid.shapes]
  congr 1
  exact map_two pubG _ _ _ B.mid.groups B.mid.g0 B.mid.g1

/-- **From the eight decisions**, one behind the other from the chain's first state. -/
theorem behind_eight (Q : P14) (key : TableKey) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU)
    (d1 d2 d3 d4 d5 d6 d7 d8 : St) (rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView)
    (gs1 gs2 gs3 gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64)))
    (h1 : b1.decide (first Q.codes key) rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (h4 : b4.decide d3 rs4 gs4 = .ok d4)
    (h5 : b5.decide d4 rs5 gs5 = .ok d5) (h6 : b6.decide d5 rs6 gs6 = .ok d6)
    (h7 : b7.decide d6 rs7 gs7 = .ok d7) (h8 : b8.decide d7 rs8 gs8 = .ok d8) :
    Behind Q sentU d8 := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU', hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  obtain rfl : sentU' = sentU := Option.some.inj (hU.symm.trans hw)
  -- "LIN point"
  obtain ⟨r1, _, L1⟩ := laid_point Q.par _ d1 rs1 hS (why_some h1)
  obtain ⟨M1, u1, o1, z1⟩ := mid_point L1
  -- "send o_u"
  obtain ⟨ids2, x2, i0, i1, L2, e2, a0, a1, u2, o2, n2, m2⟩ :=
    sentU_facts Q _ _ _ _ d1 d2 rs2 gs2 hM h2
  have M2 := mid_send (d' := d2) M1 L2 e2
  rw [parK1_sent] at M2
  have k0 : i0 = 0 := by
    have := ids_at L2.idsAre a0
    rw [this]
    show 0 + d1.st.oracles.size = 0
    rw [z1]
  have k1 : i1 = 1 := by
    have := ids_at L2.idsAre a1
    rw [this]
    show 1 + d1.st.oracles.size = 1
    rw [z1]
  have z2 : d2.st.oracles.size = sentU'.size := by
    have := L2.size
    rw [parK1_sent] at this
    rw [e2, this]
    show d1.st.oracles.size + sentU'.size = sentU'.size
    rw [z1, Nat.zero_add]
  -- "(rec_gamma)"
  obtain ⟨GU3, rows3, L3⟩ := laid_rec Q.par d2 d3 rs3 (why_some h3)
  have M3 := mid_rec M2 L3 (u2.trans u1)
  rw [n2, k0, enter_first] at M3
  -- "LOC"
  obtain ⟨r4, c4, GU4, rows4, _, _, L4⟩ := laid_loc Q.par d3 d4 rs4 gs4 (why_some h4)
  have u3 : d3.loc.gU = 0 := by rw [L3.loc]; exact u2.trans u1
  have M4 := mid_loc M3 L4 u3
  have z4 : d4.st.oracles.size = sentU'.size := by rw [L4.oracles, L3.size, z2]
  -- "send o_omega"
  obtain ⟨ids5, x5, j0, j1, L5, e5, c0, c1, u5, o5, m5, n5, s5⟩ :=
    sentO_facts Q _ _ _ _ d4 d5 rs5 gs5 hS h5
  have M5 := mid_send (d' := d5) M4 L5 e5
  rw [parK1_sent] at M5
  have q0 : j0 = sentU'.size := by
    have := ids_at L5.idsAre c0
    rw [this]
    show 0 + d4.st.oracles.size = sentU'.size
    rw [z4, Nat.zero_add]
  have q1 : j1 = sentU'.size + 1 := by
    have := ids_at L5.idsAre c1
    rw [this]
    show 1 + d4.st.oracles.size = sentU'.size + 1
    rw [z4, Nat.add_comm]
  have u4 : d4.loc.gU = 0 := by rw [L4.loc]; exact u3
  have o4 : d4.loc.gOmega = 1 := by rw [L4.loc, L3.loc]; exact o2.trans o1
  have m4 : d4.loc.firstMask = some 1 := by rw [L4.loc, L3.loc, m2, k1]
  -- the joinings
  obtain ⟨GU6, GO6, L6⟩ := joined_joins Q.par d5 d6 rs6 hS (why_some h6)
  have M6 := mid_joined M5 L6 (u5.trans u4) (o5.trans o4)
  rw [n5, s5, q0, q1, enter_second _ _ _ _ (Nat.succ_pos _), enter_first,
    enter_second _ _ _ _ (Nat.lt_succ_self _)] at M6
  -- "LIN zeta"
  obtain ⟨r7, _, L7⟩ := laid_zeta d6 d7 rs7 (why_some (l := []) h7)
  have M7 := mid_zeta M6 L7
  have l7 : d7.loc.gU = 0 ∧ d7.loc.gOmega = 1 ∧ d7.loc.firstMask = some 1 := by
    rw [L7.is]
    show d6.loc.gU = 0 ∧ d6.loc.gOmega = 1 ∧ d6.loc.firstMask = some 1
    rw [L6.loc]
    exact ⟨u5.trans u4, o5.trans o4, m5.trans m4⟩
  -- "SPLIT"
  have k8 := why_some h8
  obtain ⟨r8, rfl⟩ := split_one Q.par d7 d8 rs8 hS k8
  obtain ⟨GU8, GO8, x8, l8, n8, row8, mu8, L8⟩ := laid_split Q.par d7 d8 r8 hS k8
  have M8 := mid_split M7 L8 l7.1 l7.2.1
  refine ⟨?_, by rw [L8.loc]; exact l7.1, by rw [L8.loc]; exact l7.2.1,
    by rw [L8.loc]; exact l7.2.2⟩
  have e : (#[] ++ sentU'.map (·.shape) ++ (withOmega Q.S).map (·.shape) : Array OracleShape) =
      (sentU' ++ withOmega Q.S).map (·.shape) := by
    rw [Array.empty_append, Array.map_append]
  rw [e] at M8
  exact M8

/-- **From the fold over the eight blocks.** -/
theorem behind_fold (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : TableKey)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (x : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 bs (first Q.codes key) rs cols = .ok x) : Behind Q sentU x.1 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := blocks_eight Q bs hb
  obtain ⟨_, d1, k1, s1, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d2, k2, s2, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d3, k3, s3, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d4, k4, s4, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d5, k5, s5, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d6, k6, s6, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d7, k7, s7, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  obtain ⟨_, d8, k8, s8, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
  simp only [foldBlocks, Except.ok.injEq] at h
  subst h
  obtain ⟨_, _, e1⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s1
  obtain ⟨_, _, e2⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s2
  obtain ⟨_, _, e3⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s3
  obtain ⟨_, _, e4⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s4
  obtain ⟨_, _, e5⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s5
  obtain ⟨_, _, e6⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s6
  obtain ⟨_, _, e7⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s7
  obtain ⟨_, _, e8⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s8
  exact behind_eight Q key b1 b2 b3 b4 b5 b6 b7 b8 hb hS hM sentU hw d1 d2 d3 d4 d5 d6 d7 d8
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8

/-! ## 6 The state on entry to the test on G_u -/

/-- **The fold, where it returns, gives the plan's public part**, at the test on G_u: for every key,
all rounds and all columns. -/
theorem pub_at_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : TableKey)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (x : St × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks 0 bs (first Q.codes key) rs cols = .ok x)
    (he : VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) x.1 = .ok t) :
    pubOf t = (pubBehind Q sentU, 0) := by
  have B := behind_fold Q bs hb hS hM sentU hw key rs cols x h
  unfold VerifiableInference.Desc.K12.Seat.enter at he
  cases he
  show (pubSt x.1.st, x.1.loc.gU) = _
  rw [B.pub, B.gU]

section Door
variable {W X : Type}

/-- **The public part of the state on entry to the test on G_u is the plan's, for every input and
whatever precedes the test.** No hypothesis on the run. The state is `doorOf`'s, whose fall-back is
made from that same term: where the fold or `enter` fails, the equation holds by that choice. No
statement that this state is the verifier's. key: the key, read off the input. -/
theorem door_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubOf (doorOf bs (fun w => first Q.codes (key w))
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask)) cols
      (stateOfPub (pubBehind Q sentU, 0)) w fr) = (pubBehind Q sentU, 0) :=
  pubOf_doorOf bs _ _ cols _
    (fun w _ x t hx ht => pub_at_U Q bs hb hS hM sentU hw (key w) _ _ x t hx ht) w fr

/-- The same with the shared chain's front block before the eight. -/
theorem door_U_front (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (c : OnBytes.Model.Verify.Chains)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubOf (doorOf (frontBlock c :: bs) (fun w => first Q.codes (key w))
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask)) cols
      (stateOfPub (pubBehind Q sentU, 0)) w fr) = (pubBehind Q sentU, 0) :=
  pubOf_doorOf _ _ _ cols _
    (fun w _ x t hx ht => by
      obtain ⟨_, d0, k0, s0, h⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 hx
      obtain ⟨_, _, e0⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s0
      obtain rfl : first Q.codes (key w) = d0 := Except.ok.inj e0
      exact pub_at_U Q bs hb hS hM sentU hw (key w) _ _ x t h ht) w fr

end Door

/-! ## 7 The sendings' own lists -/

/-- The messages of "send o_u", as the sending's job has them. -/
theorem sent_jobU (Q : P14) (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) :
    (jobU ⟨Q, 0⟩).Q.sent = sentU := by
  show (Desc.K14.parK1 Q 2 _ ((withU Q.S).getD #[])).sent = sentU
  rw [parK1_sent, hw]
  rfl

/-- The messages of "send o_omega", as the sending's job has them. -/
theorem sent_jobOmega (Q : P14) : (jobOmega ⟨Q, 0⟩).Q.sent = withOmega Q.S := by
  show (Desc.K14.parK1 Q 5 _ (withOmega Q.S)).sent = withOmega Q.S
  rw [parK1_sent]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.shapes_eq
#print axioms ProofFile.Honest.K12.Light.shape_turned
#print axioms ProofFile.Honest.K12.Light.shapes_sent
#print axioms ProofFile.Honest.K12.Light.map_two
#print axioms ProofFile.Honest.K12.Light.ids_at
#print axioms ProofFile.Honest.K12.Light.pubG_entered
#print axioms ProofFile.Honest.K12.Light.enter_first
#print axioms ProofFile.Honest.K12.Light.enter_second
#print axioms ProofFile.Honest.K12.Light.mid_point
#print axioms ProofFile.Honest.K12.Light.mid_send
#print axioms ProofFile.Honest.K12.Light.mid_rec
#print axioms ProofFile.Honest.K12.Light.mid_loc
#print axioms ProofFile.Honest.K12.Light.mid_joined
#print axioms ProofFile.Honest.K12.Light.mid_zeta
#print axioms ProofFile.Honest.K12.Light.mid_split
#print axioms ProofFile.Honest.K12.Light.sent_two
#print axioms ProofFile.Honest.K12.Light.sentU_facts
#print axioms ProofFile.Honest.K12.Light.sentO_facts
#print axioms ProofFile.Honest.K12.Light.Behind.pub
#print axioms ProofFile.Honest.K12.Light.behind_eight
#print axioms ProofFile.Honest.K12.Light.behind_fold
#print axioms ProofFile.Honest.K12.Light.pub_at_U
#print axioms ProofFile.Honest.K12.Light.door_U
#print axioms ProofFile.Honest.K12.Light.door_U_front
#print axioms ProofFile.Honest.K12.Light.sent_jobU
#print axioms ProofFile.Honest.K12.Light.sent_jobOmega
#print axioms ProofFile.Honest.K12.Light.pubG
#print axioms ProofFile.Honest.K12.Light.PubGroup.enter
#print axioms ProofFile.Honest.K12.Light.pubBehind
#print axioms ProofFile.Honest.K12.Light.Mid
#print axioms ProofFile.Honest.K12.Light.Behind
