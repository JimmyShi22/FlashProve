--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyTakeOver.lean: THE FIRST SUB-PROTOCOL OF THE KEY FILE's THIRD CHAIN ("K14, second part")
ACCEPTS, FROM NAMED CLAUSES ON THE STATE IN FRONT OF IT, and what it leaves. It has no round and no
part of a prover: Omega, a message of the shared chain, is taken over and joins the own group; the
row (Dot) is laid as that group's last open row. Statements and proofs, by unfolding the ground's
functions. One step of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on
what a view shows.

The direction is that of E2E/KeyEnds.lean: what holds in front GIVES the acceptance.

What is shown.
  `ok_of_all`; `adoptP_some`, `elsewhereP_some`, `joinP_some`, `addRowP_some`: four of the ground's
    plain functions return, and what, where their lists of named clauses hold.
  `Taken S s x q t y G lay`: ALL THAT THE TAKING-OVER ASKS, as clauses on the state s in front and
    on the copy x of the shared chain's end that s holds. On the shared chain's end: Omega has a
    place in its book, a tree to itself, the public shape, and is sampled. On public values and the
    codes: that shape fits the codes, counts an answer, and makes one tree. On s: statement and
    book are in step; the own group is there, its test has not begun, its two codes are Omega's;
    the two statements' codes agree at Omega's two codes.
  `stTaken`: the statement behind the taking-over, written out: one message more, at the next free
    number, with Omega's shape, sample rows (renamed) and pad, sampled; it has joined the own group.
  **`takeOver_passes`**: under `Taken` and `Listed s.st` (E2E/KeyListed.lean): the taking-over
    returns the next free number and a state with the statement `stTaken`, the roots and named
    values as they were. `Listed` pays "no member twice": the next free number is no member of any
    group.
  **`k14Second_passes`**: so the sub-protocol accepts, where besides: the two ends are at hand, the
    shape does not split the row (Dot), no root is received yet and the first own tree's number
    counts one tree more; AND TWO NAMED PREMISES ON THE ROW: `linDotRow` returns a row at the next
    free number; the ground's eight clauses on a new open row (`rowL`) hold of it at `stTaken`.

Limits.
- THE TWO PREMISES ON THE ROW (Dot) ARE NOT SHOWN. Among `rowL`'s eight clauses is the ground's one
  test on values: no coefficient of the row lies on an entry that masks a sample's answers.
- That a run's state in front meets `Taken` is not shown. The library's tests on this chain's
  book-keeping hold no message's shape, no group's code and nothing of the books' trees' parts.
- A member of `Taken`, at the full size's shapes and codes: E2E/KeySecondMember.lean.


-/
import E2E.KeyListed
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Third (S₃ Loc₃ Border SharedOut P₁₄ takeOver batchLinearConstraintsSecondPart plainArm
  firstStepB)

/-- A list of named clauses that all hold passes. -/
theorem ok_of_all (l : Clauses) (h : ∀ c ∈ l, c.2 = true) : ok l = true := List.all_eq_true.2 h

section Ground
variable {L : Type}

theorem adoptP_some (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (lay : TreeLay) (h : ok (adoptL d.st d.book sent given) = true)
    (hl : VerifiableInference.Desc.Own.treesMade d.st.codes sent = some lay) :
    ∃ d', adoptP d sent given = some ((Array.range sent.size).map (· + d.st.oracles.size), d') ∧
      d'.st = stSent d.st sent ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold adoptP
  rw [if_pos h, hl]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem elsewhereP_some (d : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (y : OnBytes.Oracle) (h : ok (elsewhereL d.st mine other theirs) = true)
    (hy : other.oracles[theirs]? = some y) :
    elsewhereP d mine other theirs = some { d with st := { d.st with
      oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine)
                 pad := y.pad } } } := by
  unfold elsewhereP
  rw [if_pos h, hy]
  rfl

theorem joinP_some (d : DState L) (g o : Nat) (kept : Bool) (G : OnBytes.Group)
    (h : ok (joinL d.st g o kept) = true) (hG : d.st.groups[g]? = some G) :
    joinP d g o kept = some { d with st := withMessageInGroup d.st g o kept G } := by
  unfold joinP
  rw [if_pos h, hG]
  rfl

theorem addRowP_some (d : DState L) (g : Nat) (row : OnBytes.Row)
    (h : ok (rowL d.st g row) = true) :
    addRowP d g row = some { d with st := withRow d.st g row } := by
  unfold addRowP
  rw [if_pos h]

end Ground

/-! ## The taking-over -/

/-- **All that the taking-over asks**, on the state s in front and the shared chain's end o. -/
structure Taken (S : LinShape) (s : S₃) (o : SharedOut) (q : Nat × Nat) (t : Tree)
    (y : OnBytes.Oracle) (G : OnBytes.Group) (lay : TreeLay) : Prop where
  place : o.book.place[o.omega]? = some q
  tree : o.book.trees[q.1]? = some t
  alone : t.parts.size = 1
  omega : o.st.oracles[o.omega]? = some y
  shape : y.shape = S.omega
  sampled : y.sampled = true
  fits : VerifiableInference.Desc.Own.sentShapeFits s.st.codes y.shape = true
  answers : y.shape.answers ≠ 0
  step : s.st.oracles.size = s.book.place.size
  made : VerifiableInference.Desc.Own.treesMade s.st.codes
    #[{ shape := y.shape, leafClass := S.omegaLeafClass }] = some lay
  one : lay.shapes.size = 1
  mainSame : y.shape.mainRows = 0 ∨ ∃ c, s.st.codes.base[y.shape.code]? = some c ∧
    o.st.codes.base[y.shape.code]? = some c
  maskSame : y.shape.maskRows = 0 ∨ ∃ z, s.st.codes.mask[y.shape.maskCode]? = some z ∧
    o.st.codes.mask[y.shape.maskCode]? = some z
  group : s.st.groups[s.loc.own]? = some G
  fresh : G.inRun = false
  mainCode : y.shape.mainRows = 0 ∨ y.shape.code = G.code
  maskCode : y.shape.maskRows = 0 ∨ y.shape.maskCode = G.maskCode

/-- The statement with Omega come in, without its sample. -/
def stCome (S : LinShape) (s : S₃) (y : OnBytes.Oracle) : Statement :=
  stSent s.st #[{ shape := y.shape, leafClass := S.omegaLeafClass }]

/-- The same with Omega's sample rows and pad copied under the number here. -/
def stCopied (S : LinShape) (s : S₃) (y : OnBytes.Oracle) : Statement :=
  { stCome S s y with
    oracles := (stCome S s y).oracles.modify s.st.oracles.size fun x =>
      { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size)
               pad := y.pad } }

/-- **The statement behind the taking-over.** -/
def stTaken (S : LinShape) (s : S₃) (y : OnBytes.Oracle) (G : OnBytes.Group) : Statement :=
  withMessageInGroup (stCopied S s y) s.loc.own s.st.oracles.size false G

/-- The new message, as it has come in. -/
theorem stCome_new (S : LinShape) (s : S₃) (y : OnBytes.Oracle) :
    (stCome S s y).oracles[s.st.oracles.size]? = some { shape := y.shape } := by
  simp [stCome, stSent]

/-- The new message, with the copy. -/
theorem stCopied_new (S : LinShape) (s : S₃) (y : OnBytes.Oracle) :
    (stCopied S s y).oracles[s.st.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size), pad := y.pad } := by
  show ((stCome S s y).oracles.modify s.st.oracles.size _)[s.st.oracles.size]? = _
  rw [Array.getElem?_modify, if_pos rfl, stCome_new]
  rfl

section Take
variable {S : LinShape} {s : S₃} {o : SharedOut} {q : Nat × Nat} {t : Tree} {y : OnBytes.Oracle}
  {G : OnBytes.Group} {lay : TreeLay} (h : Taken S s o q t y G lay)
include h

theorem Taken.adopts : ok (adoptL s.st s.book #[{ shape := y.shape, leafClass := S.omegaLeafClass }]
    #[(t.number, t.src)]) = true := by
  refine ok_of_all _ fun c hc => ?_
  unfold adoptL at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · refine Array.all_eq_true_iff_forall_mem.2 fun n hn => ?_
    obtain rfl := Array.mem_singleton.1 hn
    exact h.fits
  · refine Array.all_eq_true_iff_forall_mem.2 fun n hn => ?_
    obtain rfl := Array.mem_singleton.1 hn
    exact bne_iff_ne.2 h.answers
  · exact beq_iff_eq.2 h.step
  · show (VerifiableInference.Desc.Own.treesMade _ _).isSome = true
    rw [h.made]
    rfl
  · show has (VerifiableInference.Desc.Own.treesMade _ _) _ = true
    rw [h.made]
    exact beq_iff_eq.2 h.one

theorem Taken.copies : ok (elsewhereL (stCome S s y) s.st.oracles.size o.st o.omega) = true := by
  refine ok_of_all _ fun c hc => ?_
  unfold elsewhereL at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, stCome_new, h.omega] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact h.sampled
  · rfl
  · simp [has]
  · rcases h.mainSame with e | ⟨c, e1, e2⟩
    · simp [has, e]
    · have e1' : (stCome S s y).codes.base[y.shape.code]? = some c := e1
      simp [has, e1', e2]
  · rcases h.maskSame with e | ⟨z, e1, e2⟩
    · simp [has, e]
    · have e1' : (stCome S s y).codes.mask[y.shape.maskCode]? = some z := e1
      simp [has, e1', e2]

theorem Taken.joins (hL : Listed s.st) :
    ok (joinL (stCopied S s y) s.loc.own s.st.oracles.size false) = true := by
  have hG : (stCopied S s y).groups[s.loc.own]? = some G := h.group
  have hnew : s.st.oracles.size ∉ G.members := fun hm => by
    obtain ⟨x, hx, -⟩ := hL s.loc.own G s.st.oracles.size h.group hm
    exact absurd (Array.getElem?_eq_some_iff.1 hx).1 (Nat.lt_irrefl _)
  refine ok_of_all _ fun c hc => ?_
  unfold joinL at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, stCopied_new, hG] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · simp [has, h.fresh]
  · rcases h.mainCode with e | e
    · simp [has, e]
    · simp [has, e]
  · rcases h.maskCode with e | e
    · simp [has, e]
    · simp [has, e]
  · simp [has, hnew]
  · simp [has]

/-- **The taking-over returns**: the next free number, and a state with the statement written out.
-/
theorem takeOver_passes (hL : Listed s.st) :
    ∃ d', takeOver S s.loc.own o (s.withCols []) = .ok (s.st.oracles.size, d') ∧
      d'.st = stTaken S s y G ∧ d'.roots = s.roots ∧ d'.loc = s.loc := by
  obtain ⟨d₁, e₁, s₁, r₁, l₁⟩ := adoptP_some (s.withCols [])
    #[{ shape := y.shape, leafClass := S.omegaLeafClass }] #[(t.number, t.src)] lay h.adopts h.made
  have s₁' : d₁.st = stCome S s y := s₁
  have e₂ := elsewhereP_some d₁ s.st.oracles.size o.st o.omega y (by rw [s₁']; exact h.copies)
    h.omega
  have e₃ := joinP_some { d₁ with st := { d₁.st with
      oracles := d₁.st.oracles.modify s.st.oracles.size fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size)
                 pad := y.pad } } } s.loc.own s.st.oracles.size false G
    (by
      show ok (joinL { d₁.st with oracles := _ } _ _ _) = true
      rw [s₁']
      exact h.joins hL)
    (by
      show d₁.st.groups[s.loc.own]? = some G
      rw [s₁']
      exact h.group)
  have a1 : (t.parts.size == 1) = true := beq_iff_eq.2 h.alone
  have a2 : decide (y.shape = S.omega) = true := decide_eq_true h.shape
  have a3 : ((Array.range (#[{ shape := y.shape, leafClass := S.omegaLeafClass }] :
      Array OracleNotice).size).map (· + (s.withCols []).st.oracles.size))[0]? =
      some s.st.oracles.size := by
    simp [S₃.withCols]
  refine ⟨{ d₁ with st := withMessageInGroup { d₁.st with
                  oracles := d₁.st.oracles.modify s.st.oracles.size fun x =>
                    { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size)
                             pad := y.pad } } s.loc.own s.st.oracles.size false G }, ?_, ?_, r₁, l₁⟩
  · unfold takeOver
    simp only [h.place, h.tree, h.omega, named, need, a1, a2, e₁, a3, e₂, e₃, bind, Except.bind,
      pure, Except.pure, if_true]
  · show withMessageInGroup { d₁.st with oracles := _ } _ _ _ _ = _
    rw [s₁']
    rfl

end Take

/-! ## The sub-protocol -/

/-- **"K14, second part" accepts**, with two named premises on the row (Dot). -/
theorem k14Second_passes {Cl : Type} (p : P₁₄) (s : S₃) (x : Border) (q : Nat × Nat) (t : Tree)
    (y : OnBytes.Oracle) (G : OnBytes.Group) (lay : TreeLay) (dot : OnBytes.Row)
    (hb : s.loc.border = some x) (ha : plainArm p.S = true)
    (hf : firstStepB s.roots s.loc.firstTree s.book = true)
    (h : Taken p.S s x.shared q t y G lay) (hL : Listed s.st)
    (hd : linDotRow p.S x.g x.shared.psi s.st.oracles.size
      (linLayOmega (stTaken p.S s y G).codes p.S) s.loc.w
      (linLayW (stTaken p.S s y G).codes p.S) = some dot)
    (hr : ok (rowL (stTaken p.S s y G) s.loc.own dot) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s' ∧
      s'.st = withRow (stTaken p.S s y G) s.loc.own dot ∧ s'.roots = s.roots ∧
      s'.loc = { s.loc with border := none, omega := s.st.oracles.size } := by
  obtain ⟨d', e, st', r', l'⟩ := takeOver_passes h hL
  have e₄ := addRowP_some d' s.loc.own dot (by rw [st']; exact hr)
  have hd' : linDotRow p.S x.g x.shared.psi s.st.oracles.size (linLayOmega d'.st.codes p.S) s.loc.w
      (linLayW d'.st.codes p.S) = some dot := by
    rw [st']
    exact hd
  refine ⟨{ st := withRow d'.st s.loc.own dot, book := d'.book, roots := d'.roots
            loc := { s.loc with border := none, omega := s.st.oracles.size } }, ?_, ?_, r', rfl⟩
  · simp only [batchLinearConstraintsSecondPart, hb, ha, hf, e, hd', e₄, named, need, bind, Except.bind, pure,
      Except.pure, if_true]
  · show withRow d'.st _ _ = _
    rw [st']

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.ok_of_all
#print axioms AtPublicFiles.AtFiles.adoptP_some
#print axioms AtPublicFiles.AtFiles.elsewhereP_some
#print axioms AtPublicFiles.AtFiles.joinP_some
#print axioms AtPublicFiles.AtFiles.addRowP_some
#print axioms AtPublicFiles.AtFiles.stCome_new
#print axioms AtPublicFiles.AtFiles.stCopied_new
#print axioms AtPublicFiles.AtFiles.Taken.adopts
#print axioms AtPublicFiles.AtFiles.Taken.copies
#print axioms AtPublicFiles.AtFiles.Taken.joins
#print axioms AtPublicFiles.AtFiles.takeOver_passes
#print axioms AtPublicFiles.AtFiles.k14Second_passes
