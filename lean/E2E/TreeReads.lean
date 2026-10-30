-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TreeReads.lean: how often the declared rounds of a file's three chains (Fiat-Shamir hash chains)
open a tree that a run sends, held against the encoding randomness of the rows beneath that tree.
Definitions, statements and proofs. General: no size, no public file, no prover, no coin and no
witness occurs here.

The matter. A run sends its rows in trees. Each row is a word of a code with r elements of encoding
randomness. A declared round that samples positions lists the trees that are opened at them. The
property of this file asks, for each tree: the numbers of positions of all rounds that list it add
up to at most r, for each row beneath. A tree that the batch's shared rounds send is also opened by
the own rounds of every request of the batch, each with sampled positions of its own. (Arguments on
hiding take such a count as a premise; none is made here.)

What is defined.
  `Opens`: of three chains, for each round: how many positions it samples, and the numbers of the
    trees that it opens; and how many trees the first and the second chain send. A tree's number
    counts over the whole file: the first chain's trees, then the second's, then the third's.
  `readsOn ps j`: the positions of one chain's rounds that fall on the tree j, REPEATS COUNTED.
  `Opens.inBatch O N j`: the same over the three chains in a batch of N requests. The second chain
    is run once for the batch, the first and the third once for each request. For a tree of the
    second chain: its own reads and N times the other two chains'. For any other tree, which is one
    request's own: the three chains' reads, once.
  `Beneath`, `rowCodes`, `beneathOf`: what lies beneath the trees of one prover's message: by the
    library's own rule that places oracle messages in trees (`layTrees`, OnBytes/Iop/Ground.lean):
    each tree's depth and width, and, for each oracle message in it, the code of its main rows (if
    it has any) and the code of its mask rows (if it has any).
  `along`: lays such lists along a chain's rounds, in the order of sending. IT GIVES NOTHING unless
    every round that sends trees gets as many as it sends, each with the depth and the width that
    the round's data state, and no list is left over.
  **`Within O N T`**: every tree that a round opens stands in the table T; every tree of T has a
    row; and for every tree j of T and every row's code c beneath it: `O.inBatch N j ≤ c.r`.
  `FilledAt`: some row beneath the tree has exactly as much encoding randomness as there are reads
    of the tree. `RoundsFilled`: every round that opens a tree opens one that is filled.
  `more`, `Opens.more`: one sampled position more in one round.
  `slackRows`: all rows that have more encoding randomness than there are reads of their tree.
  `FileWithin O N tab n slack`: the table is made and has n trees; `Within`; `RoundsFilled`; and
    `slackRows` is the list `slack`.
  `withinB`, `roundsFilledB`, `fileB`: the same as tests with code.
  `SameOpens D O`: a whole file's data D and short lists O have the same rounds that open something.

What is shown.
  `leaves_len`: of what a chain's sampled positions ask for (`wantsOf`, OnBytes/Maker/Whole.lean),
    at most `readsOn` are leaves of the tree j, if no round's list of positions is longer than its
    entry says.
  **`Within.points_shared`**, **`Within.points_own`**: under `Within`, in a batch of at most N
    requests, whatever was sampled: for every tree and every row's code c beneath it, the leaves
    that all rounds of all requests ask of that tree, REDUCED MODULO THE LENGTH 2 ^ c.logN OF THE
    ROW'S OWN CODE, are at most c.r distinct positions. (The library reduces a leaf to a position of
    a shorter row's code so: `posIn`, OnBytes/Slice/LinkAt.lean.)
  **`one_more_breaks`**: under `RoundsFilled`, with N at least 1: one sampled position more in ANY
    round that opens a tree makes `Within` false.
  **`one_request_more_breaks`**: if a filled tree of the second chain is opened by the first or the
    third chain, `Within` is false at N + 1 requests.
  `filled_of_not_slack`: under `Within`, every row that `slackRows` does not list is filled.
  `FileWithin.filledAt`, `FileWithin.more_breaks`, `FileWithin.request_breaks`,
    `SameOpens.request_breaks`: the same three facts from `FileWithin`.
  **`Within.batch_points`**, **`Within.run_points`**: the two theorems on positions at the verifier
    of a whole file itself (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean): at every verifier randomness; the
    leaves are taken out of the very list from which its field `reads` is made; a batch is a list of
    runs with the same verifier messages in the second chain (`reads_eq`: that list).
    **`Within.slots_points`**: the first of them over the requests of the library's own batch, its
    slots (`BRho`, Iop/Batch.lean; by `BRho.sh_slot`, Iop/BatchOne.lean, and `rho₂_of_sh`,
    E2E/ReadsCount.lean). Asked: the kit samples no more positions than a round's entry says
    (`DrawnFitsT`, OnBytes/Maker/WireLaws.lean).
  `inBatch_mono`, `Within.mono`: fewer requests: no more reads, and the property stays.
  `along_length`, `tableOf_length`: the table has a member for each tree that the rounds' data send.
  `within_of_test`, `roundsFilled_of_test`, `file_of_test`: a test's yes gives the property.
  `SameOpens.file`: what is said of the short lists holds of the file's data.
  `readsOn_thin`, `thinIs_readsOn`: rounds that open nothing do not count; a walk that holds a long
    list of rounds against the short list of those that open something.

Limits.
- Sampled positions are counted with repeats: two equal ones count twice, and so do two that are
  equal modulo a shorter row's length. So `Within` asks more than the two theorems on positions
  conclude.
- `Within` holds for nothing at rounds that open no tree together with an empty table. The clause on
  rows shuts out a tree without a row. Where T is made by `tableOf`, it has a member for each tree
  of the rounds' data (`tableOf_length`).
- THE COUNT IS BY TREE, NOT BY ORACLE MESSAGE. A protocol may send one message's content again, in a
  new tree. Each tree is counted by itself here. That each sending is encoded with encoding
  randomness of its own is a matter of the prover, of which nothing is said here.
- Positions of trees alone are counted. What else a prover sends that hangs on a row (OOD answers,
  plain parts of messages, sums) is not counted.
- `FilledAt` asks ONE filled row. Other rows beneath the same tree may have more encoding randomness
  than there are reads.
- `one_more_breaks` speaks of the rounds that there are. A NEW round that opened only trees that are
  not filled need not break `Within`.
- A code that a shape names and the list of codes lacks counts as a code with r = 0.
- WHICH CODES LIE BENEATH A TREE IS TAKEN FROM THE LISTS THAT ARE LAID ALONG THE ROUNDS; IT IS NOT
  SHOWN. `along` compares the number of trees of each sending round, each tree's depth (the length
  of its main rows; of its mask rows if it has no other) and its width. It does not tell two codes
  of one length apart, and in a tree with main rows it sees nothing of the mask rows' code, not even
  its length.
- Nothing says what follows from `Within`. Nothing on hiding or zero knowledge is stated here.

`Within`, `FilledAt`, `RoundsFilled`, `FileWithin`, `SameOpens` and `Fits` may be read as part of a
goal. They count as none.


-/
import OnBytes.Maker.WireLaws
import OnBytes.Maker.ViewOrder
import OnBytes.Iop.Ground
import E2E.ReadsCount

set_option autoImplicit false

namespace AtPublicFiles.TreeReads
open OnBytes OnBytes.Maker

/-! ## 1. The reads of a tree -/

/-- One chain's rounds: how many positions each samples, and the numbers of the trees that it
opens. -/
abbrev Pairs : Type := List (ℕ × List ℕ)

/-- The sampled positions of a chain's rounds that fall on the tree j: each round's number of
positions, once for each time that the round lists j. Repeats are counted. -/
def readsOn (ps : Pairs) (j : ℕ) : ℕ := (ps.map fun p => p.1 * p.2.count j).sum

theorem readsOn_nil (j : ℕ) : readsOn [] j = 0 := rfl

theorem readsOn_cons (p : ℕ × List ℕ) (ps : Pairs) (j : ℕ) :
    readsOn (p :: ps) j = p.1 * p.2.count j + readsOn ps j := by
  unfold readsOn
  rw [List.map_cons, List.sum_cons]

/-- The rounds that open something. -/
def thin (ps : Pairs) : Pairs := ps.filter fun p => !p.2.isEmpty

/-- Rounds that open nothing do not count. -/
theorem readsOn_thin (j : ℕ) : ∀ ps : Pairs, readsOn (thin ps) j = readsOn ps j
  | [] => rfl
  | p :: ps => by
      have ih := readsOn_thin j ps
      unfold thin at ih ⊢
      cases h : p.2 with
      | nil =>
          rw [List.filter_cons_of_neg (by simp [h]), ih, readsOn_cons, h]
          simp
      | cons a l =>
          rw [List.filter_cons_of_pos (by simp [h]), readsOn_cons, readsOn_cons, ih]

/-- What three chains' rounds open. -/
structure Opens where
  first : Pairs
  shared : Pairs
  second : Pairs
  /-- the trees that the first chain sends -/
  t₁ : ℕ
  /-- the trees that the second chain, which a batch shares, sends -/
  t₂ : ℕ

/-- **The reads of the tree j in a batch of N requests.** -/
def Opens.inBatch (O : Opens) (N j : ℕ) : ℕ :=
  if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then
    readsOn O.shared j + N * (readsOn O.first j + readsOn O.second j)
  else readsOn O.first j + (readsOn O.shared j + readsOn O.second j)

/-- More requests: no fewer reads. -/
theorem inBatch_mono (O : Opens) {N N' : ℕ} (h : N ≤ N') (j : ℕ) :
    O.inBatch N j ≤ O.inBatch N' j := by
  unfold Opens.inBatch
  split
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  · exact Nat.le_refl _

/-- All rounds. -/
def Opens.all (O : Opens) : Pairs := O.first ++ (O.shared ++ O.second)

/-- A chain's rounds' data as pairs. -/
def pairsT (ds : List RDT) : Pairs := ds.map fun d => (d.entry.poss, d.opens)

/-- The same for rounds' data without stored entries. -/
def pairsR (ds : List TypedOracleCompiler.Run.PQ.RD) : Pairs := ds.map fun d => (d.entry.poss, d.opens)

/-- What the rounds of a whole file open. -/
def opensOf (D : WholeD) : Opens := ⟨pairsT D.ds₁, pairsT D.ds₂, pairsT D.ds₃, D.t₁, D.t₂⟩

/-- What the rounds of a file with one chain open. -/
def opensOne (ds : List TypedOracleCompiler.Run.PQ.RD) : Opens := ⟨pairsR ds, [], [], 0, 0⟩

/-! ## 2. What lies beneath a tree -/

/-- A tree that a run sends: its depth, the words of a column, and the codes of the rows beneath
it. -/
structure Beneath where
  a : ℕ
  W : ℕ
  rows : List Code
  deriving DecidableEq, Repr

/-- The codes of an oracle message's rows: that of its main rows, if it has any, and that of its
mask rows, if it has any. -/
def rowCodes (codes : Codes) (n : OracleNotice) : List Code :=
  (if n.shape.mainRows = 0 then [] else [codes.base.getD n.shape.code default]) ++
    (if n.shape.maskRows = 0 then [] else [codes.mask.getD n.shape.maskCode default])

/-- The trees of one prover's message, by the library's `layTrees`. -/
def beneathOf (codes : Codes) (sent : List OracleNotice) : Option (List Beneath) :=
  (layTrees codes sent.toArray).map fun T =>
    T.shapes.toList.zipIdx.map fun t =>
      ⟨t.1.logN, t.1.mainWidth + t.1.maskWidth,
        (sent.zipIdx.filter fun x => T.tree.getD x.2 0 == t.2).flatMap fun x => rowCodes codes x.1⟩

/-- The same for a list of prover's messages. -/
def beneathAll (codes : Codes) : List (List OracleNotice) → Option (List (List Beneath))
  | [] => some []
  | s :: ss =>
    match beneathOf codes s, beneathAll codes ss with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- As many trees, each with the stated depth and width. -/
def fitsTrees (ts : List Fmt.Shape) (bs : List Beneath) : Bool :=
  ts.length == bs.length && (ts.zip bs).all fun x => x.1.a == x.2.a && x.1.W == x.2.W

/-- Lays the prover's messages along the rounds: for each round the trees that it sends. -/
def along : List (List Fmt.Shape) → List (List Beneath) → Option (List Beneath)
  | [], [] => some []
  | [], _ :: _ => none
  | ts :: rest, B =>
    if ts.isEmpty then along rest B
    else
      match B with
      | [] => none
      | b :: B' => if fitsTrees ts b then (along rest B').map (b ++ ·) else none

theorem fitsTrees_length {ts : List Fmt.Shape} {bs : List Beneath} (h : fitsTrees ts bs = true) :
    bs.length = ts.length := by
  unfold fitsTrees at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.symm

/-- **What `along` gives has a member for each tree that the rounds send.** -/
theorem along_length : ∀ (tss : List (List Fmt.Shape)) (B : List (List Beneath)) (T : List Beneath),
    along tss B = some T → T.length = (tss.map (·.length)).sum
  | [], [], T, h => by
      obtain rfl : [] = T := Option.some.inj h
      rfl
  | [], _ :: _, _, h => by cases h
  | ts :: rest, B, T, h => by
      unfold along at h
      rw [List.map_cons, List.sum_cons]
      split at h
      · rename_i he
        rw [along_length rest B T h, List.isEmpty_iff.1 he]
        simp
      · match B, h with
        | [], h => cases h
        | b :: B', h =>
            dsimp only at h
            split at h
            · rename_i hf
              obtain ⟨T', hT', rfl⟩ := Option.map_eq_some_iff.1 h
              rw [List.length_append, along_length rest B' T' hT', fitsTrees_length hf]
            · cases h

/-- **The table of a whole file's trees**, in the order of their numbers. codes: the file's codes.
S₁, S₂, S₃: the prover's messages with trees of the three chains, in the order of sending. -/
def tableOf (D : WholeD) (codes : Codes) (S₁ S₂ S₃ : List (List OracleNotice)) :
    Option (List Beneath) :=
  match (beneathAll codes S₁).bind (along (D.ds₁.map (·.trees))),
      (beneathAll codes S₂).bind (along (D.ds₂.map (·.trees))),
      (beneathAll codes S₃).bind (along (D.ds₃.map (·.trees))) with
  | some T₁, some T₂, some T₃ => some (T₁ ++ (T₂ ++ T₃))
  | _, _, _ => none

/-- **The table has as many members as the three chains send trees.** -/
theorem tableOf_length {D : WholeD} {codes : Codes} {S₁ S₂ S₃ : List (List OracleNotice)}
    {T : List Beneath} (h : tableOf D codes S₁ S₂ S₃ = some T) :
    T.length = D.t₁ + (D.t₂ + (D.ds₃.map (·.trees.length)).sum) := by
  unfold tableOf at h
  split at h
  · rename_i T₁ T₂ T₃ h₁ h₂ h₃
    obtain rfl : T₁ ++ (T₂ ++ T₃) = T := Option.some.inj h
    obtain ⟨B₁, _, a₁⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨B₂, _, a₂⟩ := Option.bind_eq_some_iff.1 h₂
    obtain ⟨B₃, _, a₃⟩ := Option.bind_eq_some_iff.1 h₃
    rw [List.length_append, List.length_append, along_length _ _ _ a₁, along_length _ _ _ a₂,
      along_length _ _ _ a₃, List.map_map, List.map_map, List.map_map]
    rfl
  · cases h

/-- The table of the trees of a file with one chain. -/
def tableOne (ds : List TypedOracleCompiler.Run.PQ.RD) (codes : Codes) (S : List (List OracleNotice)) :
    Option (List Beneath) :=
  (beneathAll codes S).bind (along (ds.map (·.trees)))

/-! ## 3. The property -/

/-- **The declared rounds' reads of every tree lie within the encoding randomness of every row
beneath it**, in a batch of N requests. -/
structure Within (O : Opens) (N : ℕ) (T : List Beneath) : Prop where
  /-- every tree that a round opens stands in the table -/
  listed : ∀ p ∈ O.all, ∀ j ∈ p.2, j < T.length
  /-- every tree of the table has a row -/
  rows : ∀ B ∈ T, B.rows ≠ []
  /-- the reads of a tree are at most r, for each row beneath it -/
  le : ∀ j B, T[j]? = some B → ∀ c ∈ B.rows, O.inBatch N j ≤ c.r

/-- Fewer requests: the property stays. -/
theorem Within.mono {O : Opens} {N N' : ℕ} {T : List Beneath} (hW : Within O N' T) (h : N ≤ N') :
    Within O N T :=
  ⟨hW.listed, hW.rows, fun j B hB c hc => le_trans (inBatch_mono O h j) (hW.le j B hB c hc)⟩

/-- Some row beneath the tree j has exactly as much encoding randomness as there are reads of j. -/
def FilledAt (O : Opens) (N : ℕ) (T : List Beneath) (j : ℕ) : Prop :=
  ∃ B, T[j]? = some B ∧ ∃ c ∈ B.rows, O.inBatch N j = c.r

/-- Every round that opens a tree opens one that is filled. -/
def RoundsFilled (O : Opens) (N : ℕ) (T : List Beneath) : Prop :=
  ∀ p ∈ O.all, p.2 ≠ [] → ∃ j ∈ p.2, FilledAt O N T j

/-- The test for `Within`. -/
def withinB (O : Opens) (N : ℕ) (T : List Beneath) : Bool :=
  (O.all.all fun p => p.2.all fun j => decide (j < T.length)) &&
    (T.all fun B => !B.rows.isEmpty) &&
    (T.zipIdx.all fun x => x.1.rows.all fun c => decide (O.inBatch N x.2 ≤ c.r))

/-- The test for `FilledAt`. -/
def filledB (O : Opens) (N : ℕ) (T : List Beneath) (j : ℕ) : Bool :=
  match T[j]? with
  | some B => B.rows.any fun c => O.inBatch N j == c.r
  | none => false

/-- The test for `RoundsFilled`. -/
def roundsFilledB (O : Opens) (N : ℕ) (T : List Beneath) : Bool :=
  O.all.all fun p => p.2.isEmpty || p.2.any fun j => filledB O N T j

theorem within_of_test {O : Opens} {N : ℕ} {T : List Beneath} (h : withinB O N T = true) :
    Within O N T := by
  unfold withinB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun B hB e => ?_, fun j B hj c hc => ?_⟩
  · have := h2 B hB
    rw [e] at this
    cases this
  · exact h3 (B, j) (List.mem_zipIdx_iff_getElem?.2 hj) c hc

theorem filledAt_of_test {O : Opens} {N : ℕ} {T : List Beneath} {j : ℕ}
    (h : filledB O N T j = true) : FilledAt O N T j := by
  unfold filledB at h
  cases e : T[j]? with
  | none => rw [e] at h; cases h
  | some B =>
      rw [e] at h
      obtain ⟨c, hc, hr⟩ := List.any_eq_true.1 h
      exact ⟨B, e, c, hc, beq_iff_eq.1 hr⟩

theorem roundsFilled_of_test {O : Opens} {N : ℕ} {T : List Beneath}
    (h : roundsFilledB O N T = true) : RoundsFilled O N T := by
  intro p hp hne
  have h1 := List.all_eq_true.1 h p hp
  rcases Bool.or_eq_true _ _ ▸ h1 with h2 | h2
  · exact absurd (List.isEmpty_iff.1 h2) hne
  · obtain ⟨j, hj, hf⟩ := List.any_eq_true.1 h2
    exact ⟨j, hj, filledAt_of_test hf⟩

/-! ## 4. It can fail: one read more -/

/-- One sampled position more in the round number i, from 0. -/
def more : Pairs → ℕ → Pairs
  | [], _ => []
  | p :: ps, 0 => (p.1 + 1, p.2) :: ps
  | p :: ps, i + 1 => p :: more ps i

theorem readsOn_more (j : ℕ) : ∀ (ps : Pairs) (i : ℕ) (p : ℕ × List ℕ), ps[i]? = some p →
    readsOn (more ps i) j = readsOn ps j + p.2.count j
  | [], _, _, h => by simp at h
  | q :: ps, 0, p, h => by
      obtain rfl : q = p := by simpa using h
      show readsOn ((q.1 + 1, q.2) :: ps) j = _
      rw [readsOn_cons, readsOn_cons]
      show (q.1 + 1) * q.2.count j + readsOn ps j = q.1 * q.2.count j + readsOn ps j + q.2.count j
      rw [Nat.add_mul, Nat.one_mul]
      omega
  | q :: ps, i + 1, p, h => by
      have ih := readsOn_more j ps i p (by simpa using h)
      show readsOn (q :: more ps i) j = _
      rw [readsOn_cons, readsOn_cons, ih]
      omega

/-- One sampled position more in the round number i of the chain number c: 0 the first, 1 the
second, else the third. -/
def Opens.more (O : Opens) (c i : ℕ) : Opens :=
  match c with
  | 0 => { O with first := TreeReads.more O.first i }
  | 1 => { O with shared := TreeReads.more O.shared i }
  | _ => { O with second := TreeReads.more O.second i }

/-- The rounds of the chain number c. -/
def Opens.chain (O : Opens) (c : ℕ) : Pairs :=
  match c with
  | 0 => O.first
  | 1 => O.shared
  | _ => O.second

theorem Opens.chain_sub (O : Opens) (c : ℕ) : ∀ p ∈ O.chain c, p ∈ O.all := by
  intro p hp
  unfold Opens.all
  match c, hp with
  | 0, hp => exact List.mem_append_left _ hp
  | 1, hp => exact List.mem_append_right _ (List.mem_append_left _ hp)
  | _ + 2, hp => exact List.mem_append_right _ (List.mem_append_right _ hp)

/-- One position more in a round that lists j: at least one read more of j. -/
theorem inBatch_more (O : Opens) {N : ℕ} (hN : 0 < N) (c i : ℕ) (p : ℕ × List ℕ)
    (hp : (O.chain c)[i]? = some p) (j : ℕ) (hj : j ∈ p.2) :
    O.inBatch N j + 1 ≤ (O.more c i).inBatch N j := by
  have h1 : 1 ≤ p.2.count j := List.count_pos_iff.2 hj
  have hm : ∀ a b : ℕ, a + 1 ≤ b → N * a + 1 ≤ N * b := fun a b hab =>
    le_trans (by rw [Nat.mul_add, Nat.mul_one]; omega) (Nat.mul_le_mul_left N hab)
  match c, hp with
  | 0, hp =>
      have e := readsOn_more j O.first i p hp
      show (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then _ else _) + 1 ≤
        (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then
          readsOn O.shared j + N * (readsOn (TreeReads.more O.first i) j + readsOn O.second j)
        else readsOn (TreeReads.more O.first i) j + (readsOn O.shared j + readsOn O.second j))
      rw [e]
      split
      · have := hm (readsOn O.first j + readsOn O.second j)
          (readsOn O.first j + p.2.count j + readsOn O.second j) (by omega)
        omega
      · omega
  | 1, hp =>
      have e := readsOn_more j O.shared i p hp
      show (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then _ else _) + 1 ≤
        (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then
          readsOn (TreeReads.more O.shared i) j + N * (readsOn O.first j + readsOn O.second j)
        else readsOn O.first j + (readsOn (TreeReads.more O.shared i) j + readsOn O.second j))
      rw [e]
      split <;> omega
  | _ + 2, hp =>
      have e := readsOn_more j O.second i p hp
      show (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then _ else _) + 1 ≤
        (if O.t₁ ≤ j ∧ j < O.t₁ + O.t₂ then
          readsOn O.shared j + N * (readsOn O.first j + readsOn (TreeReads.more O.second i) j)
        else readsOn O.first j + (readsOn O.shared j + readsOn (TreeReads.more O.second i) j))
      rw [e]
      split
      · have := hm (readsOn O.first j + readsOn O.second j)
          (readsOn O.first j + (readsOn O.second j + p.2.count j)) (by omega)
        omega
      · omega

/-- **One sampled position more in any round that opens a tree makes the property false**, where
every such round opens a filled tree. -/
theorem one_more_breaks {O : Opens} {N : ℕ} {T : List Beneath} (hF : RoundsFilled O N T)
    (hN : 0 < N) (c i : ℕ) (p : ℕ × List ℕ) (hp : (O.chain c)[i]? = some p) (hne : p.2 ≠ []) :
    ¬ Within (O.more c i) N T := by
  intro hW
  obtain ⟨j, hj, B, hB, k, hk, e⟩ := hF p (O.chain_sub c p (List.mem_of_getElem? hp)) hne
  have h1 := hW.le j B hB k hk
  have h2 := inBatch_more O hN c i p hp j hj
  omega

/-- **One request more makes the property false**, if a filled tree of the second chain is opened by
the first or the third chain. -/
theorem one_request_more_breaks {O : Opens} {N : ℕ} {T : List Beneath} {j : ℕ}
    (hF : FilledAt O N T j) (hj : O.t₁ ≤ j ∧ j < O.t₁ + O.t₂)
    (hd : 0 < readsOn O.first j + readsOn O.second j) : ¬ Within O (N + 1) T := by
  intro hW
  obtain ⟨B, hB, k, hk, e⟩ := hF
  have h1 := hW.le j B hB k hk
  unfold Opens.inBatch at h1 e
  rw [if_pos hj] at h1 e
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-! ## 5. From reads, repeats counted, to distinct positions -/

/-- The leaf, if the want is a leaf of the tree j. -/
def pick (j : ℕ) : Want → Option ℕ
  | .tree i x => if i = j then some x else none
  | .table _ _ => none

/-- The leaves of the tree j among wants. -/
def leavesOf (j : ℕ) (ws : List Want) : List ℕ := ws.filterMap (pick j)

theorem leavesOf_append (j : ℕ) (u v : List Want) :
    leavesOf j (u ++ v) = leavesOf j u ++ leavesOf j v := List.filterMap_append

theorem treeWants_len (dep : ℕ → Option ℕ) (poss : List ℕ) (i : ℕ) :
    (treeWants dep poss i).length ≤ poss.length := by
  unfold treeWants
  cases dep i with
  | none => exact Nat.zero_le _
  | some b =>
      show ((Fmt.listOf (poss.map (· % 2 ^ b))).map fun x => Want.tree i x).length ≤ poss.length
      rw [List.length_map]
      exact le_trans (Fmt.listOf_len _) (Nat.le_of_eq (List.length_map _))

theorem treeWants_other (dep : ℕ → Option ℕ) (poss : List ℕ) {i j : ℕ} (h : i ≠ j) :
    leavesOf j (treeWants dep poss i) = [] := by
  unfold treeWants leavesOf
  cases dep i with
  | none => rfl
  | some b =>
      refine List.filterMap_eq_nil_iff.2 fun w hw => ?_
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hw
      exact if_neg h

theorem opens_len (dep : ℕ → Option ℕ) (poss : List ℕ) (n : ℕ) (h : poss.length ≤ n) (j : ℕ) :
    ∀ l : List ℕ, (leavesOf j (l.flatMap (treeWants dep poss))).length ≤ n * l.count j
  | [] => Nat.zero_le _
  | i :: l => by
      have ih := opens_len dep poss n h j l
      rw [List.flatMap_cons, leavesOf_append, List.length_append]
      by_cases e : i = j
      · subst e
        have h1 : (leavesOf i (treeWants dep poss i)).length ≤ n :=
          le_trans (List.length_filterMap_le _ _) (le_trans (treeWants_len dep poss i) h)
        rw [List.count_cons_self, Nat.mul_succ]
        omega
      · rw [treeWants_other dep poss e, List.count_cons_of_ne e]
        simpa using ih

theorem tables_none (a : ℕ) (poss : List ℕ) (j : ℕ) (ss : List Fmt.Stored) :
    leavesOf j (ss.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ a))).map fun x => Want.table s.item x) =
      [] := by
  refine List.filterMap_eq_nil_iff.2 fun w hw => ?_
  obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 hw
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hs
  rfl

/-- No round's list of sampled positions is longer than its entry says. -/
def Fits (ds : List RDT) (Rs : List Fmt.Drawn) : Prop :=
  ∀ p ∈ ds.zip Rs, p.2.poss.length ≤ p.1.entry.poss

/-- **Of what a chain's sampled positions ask for, at most `readsOn` are leaves of the tree j.** -/
theorem leaves_len (a : ℕ) (dep : ℕ → Option ℕ) (j : ℕ) :
    ∀ (ds : List RDT) (Rs : List Fmt.Drawn), Fits ds Rs →
      (leavesOf j (wantsOf a dep ds Rs)).length ≤ readsOn (pairsT ds) j
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], _ => Nat.zero_le _
  | d :: ds, R :: Rs, h => by
      have ih := leaves_len a dep j ds Rs fun p hp => h p (List.mem_cons_of_mem _ hp)
      have h0 : R.poss.length ≤ d.entry.poss := h (d, R) List.mem_cons_self
      rw [wantsOf_cons, leavesOf_append, leavesOf_append, tables_none, List.nil_append,
        List.length_append]
      show _ ≤ readsOn ((d.entry.poss, d.opens) :: pairsT ds) j
      rw [readsOn_cons]
      exact Nat.add_le_add (opens_len dep R.poss _ h0 j d.opens) ih

/-- Reduced modulo any number, a list has at most as many distinct members as it is long. -/
theorem card_mod_le (l : List ℕ) (m : ℕ) : ((l.map (· % m)).toFinset).card ≤ l.length :=
  le_trans (List.toFinset_card_le _) (Nat.le_of_eq (List.length_map _))

/-- The leaves of the tree j that a batch asks for. R₂: what the second chain's rounds sampled, once
for the batch. Rs: for each request, what its first and its third chain's rounds sampled. -/
def batchLeaves (D : WholeD) (j : ℕ) (R₂ : List Fmt.Drawn)
    (Rs : List (List Fmt.Drawn × List Fmt.Drawn)) : List ℕ :=
  leavesOf j (wantsOf D.a D.depth D.ds₂ R₂) ++
    Rs.flatMap fun R => leavesOf j (wantsOf D.a D.depth D.ds₁ R.1) ++
      leavesOf j (wantsOf D.a D.depth D.ds₃ R.2)

theorem batchLeaves_len (D : WholeD) (j : ℕ) (R₂ : List Fmt.Drawn) (h₂ : Fits D.ds₂ R₂) :
    ∀ Rs : List (List Fmt.Drawn × List Fmt.Drawn),
      (∀ R ∈ Rs, Fits D.ds₁ R.1 ∧ Fits D.ds₃ R.2) →
      (batchLeaves D j R₂ Rs).length ≤ readsOn (pairsT D.ds₂) j +
        Rs.length * (readsOn (pairsT D.ds₁) j + readsOn (pairsT D.ds₃) j)
  | [], _ => by
      unfold batchLeaves
      simpa using leaves_len D.a D.depth j D.ds₂ R₂ h₂
  | R :: Rs, h => by
      have ih := batchLeaves_len D j R₂ h₂ Rs fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
      have h1 := leaves_len D.a D.depth j D.ds₁ R.1 (h R List.mem_cons_self).1
      have h3 := leaves_len D.a D.depth j D.ds₃ R.2 (h R List.mem_cons_self).2
      unfold batchLeaves at ih ⊢
      rw [List.flatMap_cons, List.length_append, List.length_append, List.length_append,
        List.length_cons, Nat.succ_mul]
      rw [List.length_append] at ih
      omega

/-- **A tree that the batch shares: at most r distinct positions of every row beneath it**, modulo
the row's own code's length, over the second chain's rounds and the own rounds of all requests of a
batch of at most N, whatever was sampled. -/
theorem Within.points_shared {D : WholeD} {N : ℕ} {T : List Beneath} (hW : Within (opensOf D) N T)
    {j : ℕ} (hj : D.t₁ ≤ j ∧ j < D.t₁ + D.t₂) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (R₂ : List Fmt.Drawn) (h₂ : Fits D.ds₂ R₂)
    (Rs : List (List Fmt.Drawn × List Fmt.Drawn)) (hN : Rs.length ≤ N)
    (hs : ∀ R ∈ Rs, Fits D.ds₁ R.1 ∧ Fits D.ds₃ R.2) :
    (((batchLeaves D j R₂ Rs).map (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  refine le_trans (card_mod_le _ _) (le_trans (batchLeaves_len D j R₂ h₂ Rs hs) ?_)
  have h := hW.le j B hB c hc
  have hj' : (opensOf D).t₁ ≤ j ∧ j < (opensOf D).t₁ + (opensOf D).t₂ := hj
  unfold Opens.inBatch at h
  rw [if_pos hj'] at h
  exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hN) _) h

/-- **A request's own tree: at most r distinct positions of every row beneath it**, modulo the row's
own code's length, over the rounds of the three chains, whatever was sampled. -/
theorem Within.points_own {D : WholeD} {N : ℕ} {T : List Beneath} (hW : Within (opensOf D) N T)
    {j : ℕ} (hj : ¬ (D.t₁ ≤ j ∧ j < D.t₁ + D.t₂)) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (R₁ R₂ R₃ : List Fmt.Drawn) (h₁ : Fits D.ds₁ R₁) (h₂ : Fits D.ds₂ R₂)
    (h₃ : Fits D.ds₃ R₃) :
    (((batchLeaves D j R₂ [(R₁, R₃)]).map (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  refine le_trans (card_mod_le _ _) (le_trans (batchLeaves_len D j R₂ h₂ [(R₁, R₃)] ?_) ?_)
  · intro R hR
    obtain rfl : R = (R₁, R₃) := by simpa using hR
    exact ⟨h₁, h₃⟩
  · have h := hW.le j B hB c hc
    have hj' : ¬ ((opensOf D).t₁ ≤ j ∧ j < (opensOf D).t₁ + (opensOf D).t₂) := hj
    unfold Opens.inBatch at h
    rw [if_neg hj'] at h
    show readsOn (pairsT D.ds₂) j + 1 * (readsOn (pairsT D.ds₁) j + readsOn (pairsT D.ds₃) j) ≤ c.r
    have h' : readsOn (pairsT D.ds₁) j + (readsOn (pairsT D.ds₂) j + readsOn (pairsT D.ds₃) j) ≤
        c.r := h
    omega

/-! ## 6. A long list of rounds against the short list of those that open something -/

/-- Walks the rounds' data: those that open something are, in order, the pairs ps. -/
def thinIs : List RDT → Pairs → Bool
  | [], [] => true
  | [], _ :: _ => false
  | d :: ds, ps =>
    if d.opens.isEmpty then thinIs ds ps
    else
      match ps with
      | [] => false
      | p :: ps' => (d.entry.poss == p.1 && d.opens == p.2) && thinIs ds ps'

theorem thinIs_thin : ∀ (ds : List RDT) (ps : Pairs), thinIs ds ps = true → thin (pairsT ds) = ps
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | d :: ds, ps, h => by
      unfold thinIs at h
      show thin ((d.entry.poss, d.opens) :: pairsT ds) = ps
      unfold thin
      split at h
      · rename_i he
        rw [List.filter_cons_of_neg (by simpa using he)]
        exact thinIs_thin ds ps h
      · rename_i he
        rw [List.filter_cons_of_pos (by simpa using he)]
        match ps, h with
        | p :: ps', h =>
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨⟨e1, e2⟩, h3⟩ := h
            have ih := thinIs_thin ds ps' h3
            unfold thin at ih
            rw [ih]
            cases p
            simp only at e1 e2
            rw [e1, e2]

/-- Where the walk gives true, the reads are those of the short list. -/
theorem thinIs_readsOn {ds : List RDT} {ps : Pairs} (h : thinIs ds ps = true) (j : ℕ) :
    readsOn (pairsT ds) j = readsOn ps j := by
  rw [← readsOn_thin j (pairsT ds), thinIs_thin ds ps h]

/-! ## 7. The rows with more encoding randomness than reads -/

/-- The rows that have more encoding randomness than there are reads of their tree: the tree's
number, the row's code, the reads of the tree. A code stands once for each sort of row of each
oracle message that is under it. -/
def slackRows (O : Opens) (N : ℕ) (T : List Beneath) : List (ℕ × Code × ℕ) :=
  T.zipIdx.flatMap fun x =>
    (x.1.rows.filter fun c => decide (O.inBatch N x.2 < c.r)).map fun c => (x.2, c, O.inBatch N x.2)

/-- **Every row that is not listed there is filled**: it has exactly as much encoding randomness as
there are reads of its tree. -/
theorem filled_of_not_slack {O : Opens} {N : ℕ} {T : List Beneath} (hW : Within O N T) {j : ℕ}
    {B : Beneath} (hB : T[j]? = some B) {c : Code} (hc : c ∈ B.rows)
    (hs : ∀ s ∈ slackRows O N T, ¬ (s.1 = j ∧ s.2.1 = c)) : O.inBatch N j = c.r := by
  refine Nat.le_antisymm (hW.le j B hB c hc) (Nat.not_lt.1 fun hlt => ?_)
  refine hs (j, c, O.inBatch N j) ?_ ⟨rfl, rfl⟩
  exact List.mem_flatMap.2 ⟨(B, j), List.mem_zipIdx_iff_getElem?.2 hB,
    List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, decide_eq_true hlt⟩, rfl⟩⟩

/-- **What is said of one file.** tab: the table of its trees, if one is made. n: the number
of its trees. slack: all rows with more encoding randomness than reads. -/
def FileWithin (O : Opens) (N : ℕ) (tab : Option (List Beneath)) (n : ℕ)
    (slack : List (ℕ × Code × ℕ)) : Prop :=
  ∃ T, tab = some T ∧ T.length = n ∧ Within O N T ∧ RoundsFilled O N T ∧ slackRows O N T = slack

/-- The test for it. -/
def fileB (O : Opens) (N : ℕ) (tab : Option (List Beneath)) (n : ℕ)
    (slack : List (ℕ × Code × ℕ)) : Bool :=
  match tab with
  | none => false
  | some T =>
    T.length == n && withinB O N T && roundsFilledB O N T && decide (slackRows O N T = slack)

theorem file_of_test {O : Opens} {N : ℕ} {tab : Option (List Beneath)} {n : ℕ}
    {slack : List (ℕ × Code × ℕ)} (h : fileB O N tab n slack = true) :
    FileWithin O N tab n slack := by
  unfold fileB at h
  cases tab with
  | none => cases h
  | some T =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨T, rfl, h.1.1.1, within_of_test h.1.1.2, roundsFilled_of_test h.1.2, h.2⟩

namespace FileWithin
variable {O : Opens} {N : ℕ} {tab : Option (List Beneath)} {n : ℕ} {slack : List (ℕ × Code × ℕ)}

/-- A tree of which `slack` lists no row is filled. -/
theorem filledAt (h : FileWithin O N tab n slack) {T : List Beneath} (e : tab = some T) {j : ℕ}
    (hj : j < n) (hs : ∀ s ∈ slack, s.1 ≠ j) : FilledAt O N T j := by
  obtain ⟨T', e', hn, hW, -, hS⟩ := h
  obtain rfl : T' = T := Option.some.inj (e'.symm.trans e)
  have hj' : j < T'.length := hn ▸ hj
  have hB : T'[j]? = some T'[j] := List.getElem?_eq_getElem hj'
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (hW.rows _ (List.getElem_mem hj'))
  exact ⟨_, hB, c, hc, filled_of_not_slack hW hB hc fun s hs' a => hs s (hS ▸ hs') a.1⟩

/-- **One sampled position more in any round that opens a tree makes `Within` false.** -/
theorem more_breaks (h : FileWithin O N tab n slack) (hN : 0 < N) {T : List Beneath}
    (e : tab = some T) (c i : ℕ) (p : ℕ × List ℕ) (hp : (O.chain c)[i]? = some p)
    (hne : p.2 ≠ []) : ¬ Within (O.more c i) N T := by
  obtain ⟨T', e', -, -, hR, -⟩ := h
  obtain rfl : T' = T := Option.some.inj (e'.symm.trans e)
  exact one_more_breaks hR hN c i p hp hne

/-- **One request more makes `Within` false**, if the first or the third chain opens a tree of the
second chain of which `slack` lists no row. -/
theorem request_breaks (h : FileWithin O N tab n slack) {T : List Beneath} (e : tab = some T)
    {j : ℕ} (hj : j < n) (hs : ∀ s ∈ slack, s.1 ≠ j) (h2 : O.t₁ ≤ j ∧ j < O.t₁ + O.t₂)
    (hd : 0 < readsOn O.first j + readsOn O.second j) : ¬ Within O (N + 1) T :=
  one_request_more_breaks (h.filledAt e hj hs) h2 hd

end FileWithin

/-! ## 8. A whole file's data against short lists -/

/-- The rounds of D that open something are those of O, chain by chain, and the two numbers of trees
are the same. -/
structure SameOpens (D : WholeD) (O : Opens) : Prop where
  h₁ : thinIs D.ds₁ O.first = true
  h₂ : thinIs D.ds₂ O.shared = true
  h₃ : thinIs D.ds₃ O.second = true
  e₁ : D.t₁ = O.t₁
  e₂ : D.t₂ = O.t₂

namespace SameOpens
variable {D : WholeD} {O : Opens}

theorem inBatch (h : SameOpens D O) (N j : ℕ) : (opensOf D).inBatch N j = O.inBatch N j := by
  show (if D.t₁ ≤ j ∧ j < D.t₁ + D.t₂ then
      readsOn (pairsT D.ds₂) j + N * (readsOn (pairsT D.ds₁) j + readsOn (pairsT D.ds₃) j)
    else readsOn (pairsT D.ds₁) j + (readsOn (pairsT D.ds₂) j + readsOn (pairsT D.ds₃) j)) = _
  rw [thinIs_readsOn h.h₁, thinIs_readsOn h.h₂, thinIs_readsOn h.h₃, h.e₁, h.e₂]
  rfl

theorem mem_thin {ds : List RDT} {ps : Pairs} (h : thinIs ds ps = true) {p : ℕ × List ℕ}
    (hp : p ∈ pairsT ds) (hne : p.2 ≠ []) : p ∈ ps := by
  rw [← thinIs_thin ds ps h]
  exact List.mem_filter.2 ⟨hp, by simpa using hne⟩

theorem mem (h : SameOpens D O) {p : ℕ × List ℕ} (hp : p ∈ (opensOf D).all) (hne : p.2 ≠ []) :
    p ∈ O.all := by
  have hp' : p ∈ pairsT D.ds₁ ++ (pairsT D.ds₂ ++ pairsT D.ds₃) := hp
  unfold Opens.all
  rcases List.mem_append.1 hp' with a | a
  · exact List.mem_append_left _ (mem_thin h.h₁ a hne)
  · rcases List.mem_append.1 a with b | b
    · exact List.mem_append_right _ (List.mem_append_left _ (mem_thin h.h₂ b hne))
    · exact List.mem_append_right _ (List.mem_append_right _ (mem_thin h.h₃ b hne))

theorem within (h : SameOpens D O) {N : ℕ} {T : List Beneath} (hW : Within O N T) :
    Within (opensOf D) N T where
  listed := fun p hp j hj => hW.listed p (h.mem hp (List.ne_nil_of_mem hj)) j hj
  rows := hW.rows
  le := fun j B hB c hc => by rw [h.inBatch]; exact hW.le j B hB c hc

theorem roundsFilled (h : SameOpens D O) {N : ℕ} {T : List Beneath} (hF : RoundsFilled O N T) :
    RoundsFilled (opensOf D) N T := by
  intro p hp hne
  obtain ⟨j, hj, B, hB, c, hc, e⟩ := hF p (h.mem hp hne) hne
  exact ⟨j, hj, B, hB, c, hc, by rw [h.inBatch]; exact e⟩

theorem slackRows (h : SameOpens D O) (N : ℕ) (T : List Beneath) :
    TreeReads.slackRows (opensOf D) N T = TreeReads.slackRows O N T := by
  unfold TreeReads.slackRows
  simp only [h.inBatch]

/-- **What is said of the short lists holds of the file's data.** -/
theorem file (h : SameOpens D O) {N : ℕ} {tab : Option (List Beneath)} {n : ℕ}
    {slack : List (ℕ × Code × ℕ)} (hF : FileWithin O N tab n slack) :
    FileWithin (opensOf D) N tab n slack := by
  obtain ⟨T, e, hn, hW, hR, hs⟩ := hF
  exact ⟨T, e, hn, h.within hW, h.roundsFilled hR, (h.slackRows N T).trans hs⟩

/-- **One request more makes `Within` false at the file's data**, from facts on the short lists. -/
theorem request_breaks (h : SameOpens D O) {N : ℕ} {tab : Option (List Beneath)} {n : ℕ}
    {slack : List (ℕ × Code × ℕ)} (hF : FileWithin O N tab n slack) {T : List Beneath}
    (e : tab = some T) {j : ℕ} (hj : j < n) (hs : ∀ s ∈ slack, s.1 ≠ j)
    (h2 : O.t₁ ≤ j ∧ j < O.t₁ + O.t₂) (hd : 0 < readsOn O.first j + readsOn O.second j) :
    ¬ Within (opensOf D) (N + 1) T := by
  refine (h.file hF).request_breaks e hj hs ?_ ?_
  · show D.t₁ ≤ j ∧ j < D.t₁ + D.t₂
    rw [h.e₁, h.e₂]
    exact h2
  · show 0 < readsOn (pairsT D.ds₁) j + readsOn (pairsT D.ds₃) j
    rw [thinIs_readsOn h.h₁, thinIs_readsOn h.h₃]
    exact hd

end SameOpens

/-! ## 9. At a whole file's own verifier -/

section Whole
open Iop
variable (C : _root_.Run.PQ.CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- What a chain's verifier messages give as sampled positions is no longer than the entries say, if
the kit C keeps to the entries. -/
theorem fits_sampled : ∀ (ds : List RDT), DrawnFitsT C ds → ∀ ρ : Rho (uLT C ds),
    Fits ds (drawnT C ds ρ)
  | [], _, _ => fun _ hp => by cases hp
  | d :: ds, h, (c, ρ) => fun p hp => by
      rcases List.mem_cons.1 (show p ∈ _ :: ds.zip (drawnT C ds ρ) from hp) with rfl | hp''
      · exact h d List.mem_cons_self _
      · exact fits_sampled ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ p hp''

/-- The leaves of the tree j that the verifier of a whole file asks for at the verifier randomness
ρ: out of the very list from which its field `reads` is made (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean).
-/
def runLeaves (j : ℕ) (ρ : Rho (chainsOf C D tF tJ t3).sh) : List ℕ :=
  leavesOf j (wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ))

/-- The verifier's field `reads` is made of that list: the positions of the prover's oracles at its
members. -/
theorem reads_eq {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
    (run : Xi → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ =
      ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)).filterMap
        (ownPosOf C D tF tJ t3)).toFinset := rfl

/-- What runs with one second chain's verifier messages ask of a tree is among the batch's leaves.
-/
theorem runs_subset (j : ℕ) (ρs : List (Rho (chainsOf C D tF tJ t3).sh))
    (r₂ : Rho (uLT C D.ds₂)) (hsh : ∀ ρ ∈ ρs, (chainsOf C D tF tJ t3).rho₂ ρ = r₂) :
    ∀ x ∈ ρs.flatMap (runLeaves C D tF tJ t3 j),
      x ∈ batchLeaves D j (drawnT C D.ds₂ r₂) (ρs.map fun ρ =>
        (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ),
          drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ))) := by
  intro x hx
  obtain ⟨ρ, hρ, hx⟩ := List.mem_flatMap.1 hx
  unfold runLeaves at hx
  rw [leavesOf_append, leavesOf_append] at hx
  unfold batchLeaves
  rcases List.mem_append.1 hx with a | a
  · exact List.mem_append_right _ (List.mem_flatMap.2
      ⟨_, List.mem_map.2 ⟨ρ, hρ, rfl⟩, List.mem_append_left _ a⟩)
  · rcases List.mem_append.1 a with b | b
    · refine List.mem_append_left _ ?_
      rw [← hsh ρ hρ]
      exact b
    · exact List.mem_append_right _ (List.mem_flatMap.2
        ⟨_, List.mem_map.2 ⟨ρ, hρ, rfl⟩, List.mem_append_right _ b⟩)

theorem card_mod_mono {l l' : List ℕ} (h : ∀ x ∈ l, x ∈ l') (m : ℕ) :
    ((l.map (· % m)).toFinset).card ≤ ((l'.map (· % m)).toFinset).card := by
  refine Finset.card_le_card fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨x, h x hx, rfl⟩)

variable {C D}

/-- **A tree that the batch shares, at the verifier itself**: over at most N runs with the same
verifier messages in the second chain, at every verifier randomness: at most r distinct positions of
every row beneath the tree, modulo the row's own code's length. -/
theorem Within.batch_points {N : ℕ} {T : List Beneath} (hW : Within (opensOf D) N T)
    (f₁ : DrawnFitsT C D.ds₁) (f₂ : DrawnFitsT C D.ds₂) (f₃ : DrawnFitsT C D.ds₃) {j : ℕ}
    (hj : D.t₁ ≤ j ∧ j < D.t₁ + D.t₂) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (ρs : List (Rho (chainsOf C D tF tJ t3).sh)) (hN : ρs.length ≤ N)
    (r₂ : Rho (uLT C D.ds₂)) (hsh : ∀ ρ ∈ ρs, (chainsOf C D tF tJ t3).rho₂ ρ = r₂) :
    ((((ρs.flatMap (runLeaves C D tF tJ t3 j))).map (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  refine le_trans (card_mod_mono (runs_subset C D tF tJ t3 j ρs r₂ hsh) _)
    (hW.points_shared hj hB hc _ (fits_sampled C D.ds₂ f₂ r₂) _
      (by rw [List.length_map]; exact hN) ?_)
  intro R hR
  obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 hR
  exact ⟨fits_sampled C D.ds₁ f₁ _, fits_sampled C D.ds₃ f₃ _⟩

/-- **The same over the slots of the library's batch**: β: the verifier randomness of a batch of N
slots (`BRho`, Iop/Batch.lean) under the file's own marks, by which the second chain's rounds are
shared; `β.slot i`: that of the slot i. -/
theorem Within.slots_points {N : ℕ} {T : List Beneath} (hW : Within (opensOf D) N T)
    (f₁ : DrawnFitsT C D.ds₁) (f₂ : DrawnFitsT C D.ds₂) (f₃ : DrawnFitsT C D.ds₃) {j : ℕ}
    (hj : D.t₁ ≤ j ∧ j < D.t₁ + D.t₂) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows)
    (β : BRho N (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :
    (((((List.finRange N).map fun i => β.slot i).flatMap (runLeaves C D tF tJ t3 j)).map
      (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  cases N with
  | zero => simp
  | succ n =>
      refine hW.batch_points tF tJ t3 f₁ f₂ f₃ hj hB hc _ (by simp)
        ((chainsOf C D tF tJ t3).rho₂ (β.slot 0)) fun ρ hρ => ?_
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hρ
      exact AtPublicFiles.Reads.rho₂_of_sh (chainsOf C D tF tJ t3) (BRho.sh_slot i 0 _ β)

/-- **A request's own tree, at the verifier itself**: at every verifier randomness of one run: at
most r distinct positions of every row beneath the tree, modulo the row's own code's length. -/
theorem Within.run_points {N : ℕ} {T : List Beneath} (hW : Within (opensOf D) N T)
    (f₁ : DrawnFitsT C D.ds₁) (f₂ : DrawnFitsT C D.ds₂) (f₃ : DrawnFitsT C D.ds₃) {j : ℕ}
    (hj : ¬ (D.t₁ ≤ j ∧ j < D.t₁ + D.t₂)) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (((runLeaves C D tF tJ t3 j ρ).map (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  have hs := runs_subset C D tF tJ t3 j [ρ] _ (fun ρ' hρ' => by
    obtain rfl : ρ' = ρ := by simpa using hρ'
    rfl)
  refine le_trans (card_mod_mono (fun x hx => hs x (by simpa using hx)) _)
    (hW.points_own hj hB hc _ _ _ (fits_sampled C D.ds₁ f₁ _) (fits_sampled C D.ds₂ f₂ _)
      (fits_sampled C D.ds₃ f₃ _))

end Whole

end AtPublicFiles.TreeReads

#print axioms AtPublicFiles.TreeReads.readsOn_thin
#print axioms AtPublicFiles.TreeReads.within_of_test
#print axioms AtPublicFiles.TreeReads.filledAt_of_test
#print axioms AtPublicFiles.TreeReads.roundsFilled_of_test
#print axioms AtPublicFiles.TreeReads.readsOn_more
#print axioms AtPublicFiles.TreeReads.inBatch_more
#print axioms AtPublicFiles.TreeReads.one_more_breaks
#print axioms AtPublicFiles.TreeReads.one_request_more_breaks
#print axioms AtPublicFiles.TreeReads.leaves_len
#print axioms AtPublicFiles.TreeReads.batchLeaves_len
#print axioms AtPublicFiles.TreeReads.Within.points_shared
#print axioms AtPublicFiles.TreeReads.Within.points_own
#print axioms AtPublicFiles.TreeReads.thinIs_thin
#print axioms AtPublicFiles.TreeReads.thinIs_readsOn
#print axioms AtPublicFiles.TreeReads.filled_of_not_slack
#print axioms AtPublicFiles.TreeReads.file_of_test
#print axioms AtPublicFiles.TreeReads.FileWithin.filledAt
#print axioms AtPublicFiles.TreeReads.FileWithin.more_breaks
#print axioms AtPublicFiles.TreeReads.FileWithin.request_breaks
#print axioms AtPublicFiles.TreeReads.SameOpens.inBatch
#print axioms AtPublicFiles.TreeReads.SameOpens.within
#print axioms AtPublicFiles.TreeReads.SameOpens.roundsFilled
#print axioms AtPublicFiles.TreeReads.SameOpens.slackRows
#print axioms AtPublicFiles.TreeReads.SameOpens.file
#print axioms AtPublicFiles.TreeReads.SameOpens.request_breaks
#print axioms AtPublicFiles.TreeReads.fits_sampled
#print axioms AtPublicFiles.TreeReads.runs_subset
#print axioms AtPublicFiles.TreeReads.Within.batch_points
#print axioms AtPublicFiles.TreeReads.Within.slots_points
#print axioms AtPublicFiles.TreeReads.Within.run_points
#print axioms AtPublicFiles.TreeReads.inBatch_mono
#print axioms AtPublicFiles.TreeReads.Within.mono
#print axioms AtPublicFiles.TreeReads.along_length
#print axioms AtPublicFiles.TreeReads.tableOf_length
#print axioms AtPublicFiles.TreeReads.reads_eq
