-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Plays.lean: CONDITIONAL.

Not shown here. No property is claimed. That `K4Seated` (Law/Seated.lean) can be met: no example is
known. THAT THE ROW PLAYS SAYS NOTHING OF WHAT IT SENDS: no move of K4's parts can return an error,
and every list is padded with 0 or cut to its stated length: so the row plays also where its public
data do not fit: neither `k4Fits` nor a tie to a witness is read. Nothing on whether the verifier
accepts. Nothing on soundness, on completeness or on any other property.
WHAT IT IMPORTS, by a walk over import lines: no module under Johnson/Goal/ or Johnson/D/; seven
under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), which come with a module of
the library (Johnson/E/KObj/ProofFile.lean): nothing here names one of them.

What is here: the thread's debt `Plays` (Honest/Thread/Pays.lean) at the member of the layers' own
rounds (the sub-protocol K4): the honest row's play and the laying of the columns return, and no
tree is new. Definitions, and statements with their proofs.

THE ONE PREMISE: `K4Seated`: of its nine fields are read: member, rounds, oracles, own, half. No
test on what the member's rounds state is asked: that they state what the row sends, round by round,
is shown here from the verifier's own table of rounds.

  `PlaysAt T At b`   the sentence of `Plays`, at the stands in front that At names
  `PartPlays p n`   the part p has as many moves as the list n has numbers, and plays at all rounds
      that state these numbers of scalars and no oracle message, at every state
  `row_plays`   GENERAL IN THE ROW: a row of such parts plays at rounds that state the parts'
      numbers one behind the other
  `quiet_plays`, `scalars_plays`, `sum_plays`   the three sorts of K4's parts, seated in a wider
      input: CALLS of general statements on the frame's parts: `plays_lift_quiet`,
      `plays_lift_scalars` (Honest/Small/Plays.lean), `plays_unit_sumPart`
      (Honest/SumLaw/PlaysSum.lean); how stated rounds are cut: `statedBy_split`
      (Honest/Small/Stated.lean)
  `k4Sends`, `k4_row_parts`, `k4_sends_table`   how many scalars each round of each part of K4's row
      sends; the row's parts play by these; one behind the other they are the column "sent" of the
      verifier's table of rounds
  `forall₂_append`, `forall₂_replicate`   two general helpers on lists that are related member by
      member
  `stated_table`, `readsOf_none`   GENERAL IN THE TABLE: the rounds that are made of a table's rows
      state its column "sent"; rounds that open nothing read nothing
  `k4_rounds`, `k4_stated`   the member's rounds in the public data's letters; they state that
      column
  `k4_no_column`, `k4_no_tree`   the member's rounds read no column; behind it no source is new
  `k4_plays_at`, `k4_plays`   **the debt**, at every At; at the thread's own sentence. NO CODE OF
      OURS CALLS `k4_plays`: Law/PlaysAtPure.lean and Law/TopsAt.lean call `k4_plays_half` and
      `k4_playsS_half` (Law/PlaysFive.lean), which ask five fields of the seat in the whole seat's
      stead; these two stay as the form over the whole seat, of which that file's head speaks

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum
import Johnson.Desc.ProofFile.Honest.Small.Stated
import Johnson.Desc.ProofFile.Honest.Small.Plays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (Par k0 rounds)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place Oracle)
open ProofFile.Honest.SumLaw (StatedBy plays_unit_sumPart scalarsOf_length moves_length)
open ProofFile.Honest.Small (statedBy_length statedBy_split plays_lift_quiet plays_lift_scalars)
open VerifiableInference.Desc.Part.MaskedSum (Var)

/-! ## 1 The sentence, and a row that plays -/

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The sentence of `Plays`**, at the stands in front that At names. A definition: nothing is
claimed by it. -/
def PlaysAt (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop) (b : Nat) :
    Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds l, At k s m E → drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs = .ok l →
    ∃ y cols, T.Moved blk k m E ds y cols ∧ T.Trees (T.fresh b) k y.2 (E.add y.1)

/-- **The part plays by the numbers n**: it has as many moves; at all rounds that state these
numbers of scalars and no oracle message, at as many challenges, at every state, its Steps' play
returns. At every list `back` of stored rounds: `Plays` wants the empty one alone; the step from a
part to the row hands the parts behind a shorter list. -/
def PartPlays (p : Part V W X) (n : List Nat) : Prop :=
  p.moves.length = n.length ∧
    ∀ (name : String) (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V)
      (c : p.Coins) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X), StatedBy n rs →
      ds.length = n.length → ∃ y, play (p.steps name a rs v c) ds back m = .ok y

/-- **A ROW OF PARTS THAT PLAY, PLAYS.** General in the row. -/
theorem row_plays (name : String) (a : Place) (v : Option V) : ∀ (ps : List (Part V W X))
    (ns : List (List Nat)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X), List.Forall₂ PartPlays ps ns →
    StatedBy ns.flatten rs → ds.length = ns.flatten.length →
    ∃ y, play (rowSteps name a v ps j rs c) ds back m = .ok y := by
  intro ps ns j rs c ds back m h
  induction h generalizing j rs ds back m with
  | nil =>
    intro _ hl
    have hd : ds = [] := List.eq_nil_of_length_eq_zero hl
    subst hd
    exact ⟨([], m), by simp [rowSteps, play]⟩
  | @cons p n ps ns hp _ ih =>
    intro hs hl
    rw [List.flatten_cons] at hs hl
    obtain ⟨s1, s2⟩ := statedBy_split n ns.flatten rs hs
    have hrl := statedBy_length _ _ hs
    rw [List.length_append] at hl hrl
    have l1 : (ds.take n.length).length = n.length := by
      rw [List.length_take]
      omega
    have l2 : (ds.drop n.length).length = ns.flatten.length := by
      rw [List.length_drop]
      omega
    obtain ⟨y1, h1⟩ := hp.2 name ⟨a, j⟩ (rs.take n.length) v
      (show p.Coins × RowCoins ps from c).1 (ds.take n.length) back m s1 l1
    have hsl : (p.steps name ⟨a, j⟩ (rs.take n.length) v
        (show p.Coins × RowCoins ps from c).1).length = n.length := by
      rw [steps_length, List.length_take, hp.1]
      omega
    obtain ⟨y2, h2⟩ := ih (j + 1) (rs.drop n.length) (show p.Coins × RowCoins ps from c).2
      (ds.drop n.length) (back.drop n.length) y1.2 s2 l2
    refine ⟨(y1.1 ++ y2.1, y2.2), ?_⟩
    show play (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v
        (show p.Coins × RowCoins ps from c).1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length)
        (show p.Coins × RowCoins ps from c).2) ds back m = _
    rw [hp.1, ← List.take_append_drop n.length ds, play_append _ _ _ _ _ _ (l1.trans hsl.symm), h1,
      hsl]
    show (play _ _ _ y1.2).map _ = _
    rw [h2]
    rfl

end

/-! ## 2 K4's three sorts of part -/

section
variable {V W X : Type} (see : V → Unit) (wit : W → K4In)

/-- A round in which nothing is sent. -/
theorem quiet_plays :
    PartPlays (k4Quiet.lift see wit (fun _ : X => ()) fun x _ => x) [0] :=
  ⟨rfl, fun nm a rs v c ds back m hs hl =>
    ⟨_, plays_lift_quiet see wit (fun _ : X => ()) (fun x _ => x) (fun _ => rfl) 1 c nm a rs hs v ds
      hl back m⟩⟩

/-- A round that sends n scalars. -/
theorem scalars_plays (Q : K4Pub) (n : Nat) (f : K4Pub → K4In → Pts → List OnBytes.E) (i : Nat) :
    PartPlays ((k4Scalars Q n f i).lift see wit (fun _ : X => ()) fun x _ => x) [n] :=
  ⟨rfl, fun nm a rs v c ds back m hs hl =>
    match ds, hl with
    | [d], _ =>
      ⟨_, plays_lift_scalars see wit (fun _ : X => ()) (fun x _ => x) (fun _ => rfl) _ n _ c nm a rs
        hs v d back m⟩⟩

/-- A masked sumcheck each of whose variables has at least two coefficients. -/
theorem sum_plays (name endName : String) (J : SumJob K4In Unit)
    (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) :
    PartPlays ((sumPart (V := Unit) name endName J).lift see wit (fun _ : X => ()) fun x _ => x)
      (scalarsOf J.shape) := by
  refine ⟨?_, fun nm a rs v c ds back m hs hl => ?_⟩
  · show ((sumPart (V := Unit) name endName J).moves.map _).length = _
    rw [List.length_map, moves_length, scalarsOf_length name endName J]
  · exact ⟨_, plays_unit_sumPart see wit name endName J c h2 nm a rs hs v ds
      (hl.trans (scalarsOf_length name endName J)) back m⟩

end

/-! ## 3 K4's row against the verifier's table of rounds -/

/-- **How many scalars each round of each part of K4's row sends.** Numbers typed anew: they are
held against the row's own text by `k4_row_parts` and against the verifier's table by
`k4_sends_table`. -/
def k4Sends (Q : K4Pub) : List (List Nat) :=
  List.replicate (k0 Q.g) [0] ++
    [[ledNS Q.P.y.h.xl * Q.P.y.NI], [0], scalarsOf (k4LevelShape Q.P.rd.muV), [0],
     [ledNP Q.P.y.h.xl * Q.P.y.NI],
     scalarsOf (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)),
     scalarsOf (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)), [0],
     scalarsOf (k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)),
     scalarsOf (k4LevelShape Q.P.rd.muH), [0], [0], scalarsOf (k4LevelShape Q.P.rd.muH2), [0],
     [if Q.g == 0 then 1 else 0], scalarsOf (k4PlainShape Q.P.wsLay.lk 1 1)]

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- Two lists that are related member by member, one behind the other. -/
theorem forall₂_append {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {m₁ : List β}
    {l₂ : List α} {m₂ : List β}, List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ →
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (forall₂_append t h)

/-- n times one pair of related members. -/
theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => .cons h (forall₂_replicate h n)

/-- **The row's parts play by these numbers.** -/
theorem k4_row_parts (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (lk : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    List.Forall₂ PartPlays (k4Row (Rc := Rc) (X := X) Q cells weights tokens lk) (k4Sends Q) := by
  have hq : PartPlays (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens lk k4Quiet) [0] :=
    quiet_plays _ _
  have hs : ∀ n f i,
      PartPlays (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens lk (k4Scalars Q n f i)) [n] :=
    fun n f i => scalars_plays _ _ Q n f i
  have h3 : ∀ (n : Nat) (v : Var), v ∈ List.replicate n (Var.point OnBytes.zeroE 3) → 2 ≤ v.d := by
    intro n v hv
    rw [List.eq_of_mem_replicate hv]
    exact Nat.le_succ 2
  have h3' : ∀ (n : Nat) (v : Var), v ∈ List.replicate n (Var.plain 3) → 2 ≤ v.d := by
    intro n v hv
    rw [List.eq_of_mem_replicate hv]
    exact Nat.le_succ 2
  unfold k4Row k4Sends
  rw [k4RowIn_all, List.map_append, List.map_replicate]
  refine forall₂_append (forall₂_replicate hq _) ?_
  refine .cons (hs _ _ _) (.cons hq (.cons (sum_plays _ _ _ _ _ (h3 _)) (.cons hq (.cons (hs _ _ _)
    (.cons (sum_plays _ _ _ _ _ (h3 _)) (.cons (sum_plays _ _ _ _ _ (h3 _)) (.cons hq
    (.cons (sum_plays _ _ _ _ _ (h3' _)) (.cons (sum_plays _ _ _ _ _ (h3 _)) (.cons hq (.cons hq
    (.cons (sum_plays _ _ _ _ _ (h3 _)) (.cons hq (.cons ?_
    (.cons (sum_plays _ _ _ _ _ (h3' _)) .nil)))))))))))))))
  split
  · exact hs _ _ _
  · exact hq

/-- **One behind the other they are the column "sent" of the verifier's table of rounds.** -/
theorem k4_sends_table (Q : K4Pub) :
    (k4Sends Q).flatten = (rounds Q.P Q.hp Q.g).map (·.sent) := by
  rcases k0_cases Q.g with ⟨hg, hk⟩ | ⟨hg, hk⟩ <;>
    simp [k4Sends, rounds, OnBytes.Desc.First.K4.masked, OnBytes.Desc.First.K4.layerRds,
      OnBytes.Desc.First.K4.pointRd, OnBytes.Desc.First.K4.batchRd, scalarsOf, k4LevelShape,
      k4TokenShape, k4PlainShape, nStack, hg, hk, Var.d]

section
variable {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block S Cl}

/-- The rounds that are made of a table's rows state the table's column "sent". -/
theorem stated_table : ∀ L : List OnBytes.Desc.First.K4.Rd,
    StatedBy (L.map (·.sent))
      (((L.map OnBytes.Desc.First.K4.entryOf).map fun e => ({ entry := e } : Fmt.DeclaredRound)).zip
        ((((L.map OnBytes.Desc.First.K4.entryOf).map fun e =>
          ({ entry := e } : Fmt.DeclaredRound))).map fun _ => ([] : List Oracle)))
  | [] => trivial
  | d :: L => by
    refine ⟨?_, rfl, stated_table L⟩
    show (Fmt.Entry.cut (OnBytes.Desc.First.K4.entryOf d)).filter (· != .root) = _
    unfold Fmt.Entry.cut OnBytes.Desc.First.K4.entryOf
    simp

/-- Rounds that open nothing read nothing. -/
theorem readsOf_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    readsOf chain ft stored tree (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds = []
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: es, _ :: ds => readsOf_none chain ft stored tree es ds

/-- The member's rounds, in the public data's letters. -/
theorem k4_rounds (Se : K4Seated T b cells weights tokens look Q p blk) :
    blk.rounds = ((rounds Q.P Q.hp Q.g).map OnBytes.Desc.First.K4.entryOf).map fun e =>
      ({ entry := e } : Fmt.DeclaredRound) := by
  obtain ⟨eP, eh, eg, _, _⟩ := Se.own
  rw [Se.rounds, ← eP, ← eh, ← eg]
  rfl

/-- **The member's rounds state that column**, and no oracle message. -/
theorem k4_stated (Se : K4Seated T b cells weights tokens look Q p blk) :
    StatedBy ((rounds Q.P Q.hp Q.g).map (·.sent)) (blk.rounds.zip blk.oracles) := by
  rw [Se.oracles, k4_rounds Se]
  exact stated_table _

/-- The member's rounds read no column. -/
theorem k4_no_column (Se : K4Seated T b cells weights tokens look Q p blk) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (ds : List Fmt.Drawn) : readsOf chain ft stored tree blk.rounds ds = [] := by
  rw [k4_rounds Se]
  exact readsOf_none chain ft stored tree _ ds

/-- Behind the member no source is new. -/
theorem k4_no_tree (Se : K4Seated T b cells weights tokens look Q p blk) : T.fresh b = [] := by
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ Se.member, Se.oracles]
    have z : ((blk.rounds.map fun _ => ([] : List Oracle)).flatMap id).length = 0 := by
      induction blk.rounds with
      | nil => rfl
      | cons _ _ ih => exact ih
    rw [z]
    rfl
  refine List.eq_nil_iff_forall_not_mem.2 fun σ hσ => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  rw [e] at h1
  simp [h1] at h2

/-! ## 4 The debt -/

/-- **IT PLAYS, AT K4's MEMBER**, at the stands in front that At names, whichever: At is not read:
the play returns at every state of the prover's run. CONDITIONAL on the seat. -/
theorem k4_plays_at (Se : K4Seated T b cells weights tokens look Q p blk)
    (At : Coins Bk → S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) : PlaysAt T At b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  obtain rfl : blk = blk' := Option.some.inj (Se.member.symm.trans hblk')
  obtain ⟨c, _, rfl, _, _⟩ := chainSteps_one hl Se.half
  have hlen : ds.length = (k4Sends Q).flatten.length := by
    rw [drawsFit_length _ _ hd, k4_rounds Se, k4_sends_table, List.length_map, List.length_map,
      List.length_map]
  obtain ⟨y, hy⟩ := row_plays blk.name blk.place (T.φ.sees m.st.input) _ (k4Sends Q) 0
    (blk.rounds.zip blk.oracles) c ds [] m (k4_row_parts Q cells weights tokens (look Q))
    (by rw [k4_sends_table]; exact k4_stated Se) hlen
  refine ⟨y, [], ⟨⟨_, hl, hy⟩, ?_⟩, ?_⟩
  · rw [k4_no_column Se]
    rfl
  · rw [k4_no_tree Se]
    intro σ hσ
    cases hσ

/-- **The thread's debt `Plays` at K4's member.** CONDITIONAL on the seat. -/
theorem k4_plays (Se : K4Seated T b cells weights tokens look Q p blk) : Plays T b :=
  k4_plays_at Se (Thr T b)

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.row_plays
#print axioms ProofFile.Honest.K4.quiet_plays
#print axioms ProofFile.Honest.K4.scalars_plays
#print axioms ProofFile.Honest.K4.sum_plays
#print axioms ProofFile.Honest.K4.forall₂_append
#print axioms ProofFile.Honest.K4.forall₂_replicate
#print axioms ProofFile.Honest.K4.k4_row_parts
#print axioms ProofFile.Honest.K4.k4_sends_table
#print axioms ProofFile.Honest.K4.stated_table
#print axioms ProofFile.Honest.K4.readsOf_none
#print axioms ProofFile.Honest.K4.k4_rounds
#print axioms ProofFile.Honest.K4.k4_stated
#print axioms ProofFile.Honest.K4.k4_no_column
#print axioms ProofFile.Honest.K4.k4_no_tree
#print axioms ProofFile.Honest.K4.k4_plays_at
#print axioms ProofFile.Honest.K4.k4_plays
