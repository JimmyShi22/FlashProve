-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BookAppends.lean: **WHAT THE PROXIMITY TEST's OWN SWITCHES APPEND TO THE
BOOK** (first arm: the first fold's mask has come from outside): a yes of the test's decision leaves
the book with the places and the trees' shapes that it had, and behind them just what the verifier's
own layout lays for the test's sendings, one for each switch, in turn. Definitions, statements and
proofs. It stands over the kind's files' closed forms (Johnson/Desc/K12/Law/OutK.lean, OutK2.lean,
OutK3.lean, SwDid.lean, SwTies.lean) and goes along the stages as `stages_book` does.
  `Appends codes sends B B'`: B' has B's places and shapes, and behind them what `laidFrom` lays
    for sends from B's number of trees on (BookRides.lean). `Appends.nil`, `Appends.trans`,
    `appends_recv`, `appends_same`.
  `sendAt p j nxt last`, `sendsFrom p j rest`: THE TEST's SENDINGS, OFF THE PLACE's NUMBERS ALONE:
    at the switch into stage j + 1: the target and the one mask that rides with it.
  `fold_appends`, `switch_appends`, `stages_appends`, `k12_appends`: part by part; along the stages;
    the whole test.
  `seatsPrefix_appends`: "the seats are carried" rides through `Appends` where the plan's lists go
    on so; `goesOnB`: that, as a test with code. `atFinish_seats`: so through the test's block at
    the first chain's finish.
Limits. Nothing on soundness. THE OWN MASK's ARM IS NOT HERE (its first fold's sending hangs on the
record's layout). That the plan's lists go on with `sendsFrom`'s layouts at the record's codes is a
premise: a test on the plan, and "the record's codes are the plan's".

-/
import Johnson.Desc.K12.Coin.BookRides
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.SwTies
import Johnson.Desc.K12.AtFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Sw H2K.Out

/-- B' has B's places and shapes, and behind them what the sendings lay. -/
def Appends (codes : Codes) (sends : List (Array OracleNotice)) (B B' : TreeBook) : Prop :=
  ∃ A : Laid, laidFrom codes B.trees.size sends = some A ∧
    B'.place.toList = B.place.toList ++ A.places ∧
    B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ A.shapes

theorem size_of_shapes {B B' : TreeBook} {A : Laid}
    (es : B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ A.shapes) :
    B'.trees.size = B.trees.size + A.shapes.length := by
  have := congrArg List.length es
  rw [List.length_append, List.length_map, List.length_map, Array.length_toList,
    Array.length_toList] at this
  exact this

/-- The converse of `laidFrom_append`. -/
theorem laidFrom_join (codes : Codes) : ∀ (pre post : List (Array OracleNotice)) (base : ℕ)
    (A R : Laid), laidFrom codes base pre = some A →
    laidFrom codes (base + A.shapes.length) post = some R →
    laidFrom codes base (pre ++ post) =
      some { places := A.places ++ R.places, shapes := A.shapes ++ R.shapes }
  | [], post, base, A, R, hA, hR => by
    cases hA
    simpa using hR
  | sent :: pre, post, base, A, R, hA, hR => by
    have hA' : ((layTrees codes sent).bind fun lay =>
        (laidFrom codes (base + lay.shapes.size) pre).map fun R' =>
          ({ places := placesOf base sent.size lay ++ R'.places
             shapes := lay.shapes.toList ++ R'.shapes } : Laid)) = some A := hA
    obtain ⟨lay, hl, h1⟩ := Option.bind_eq_some_iff.1 hA'
    obtain ⟨A0, hA0, rfl⟩ := Option.map_eq_some_iff.1 h1
    have e : base + (lay.shapes.toList ++ A0.shapes).length =
        base + lay.shapes.size + A0.shapes.length := by
      rw [List.length_append, Array.length_toList]
      omega
    have hR' : laidFrom codes (base + lay.shapes.size + A0.shapes.length) post = some R := by
      rw [← e]
      exact hR
    have ih := laidFrom_join codes pre post _ A0 R hA0 hR'
    show ((layTrees codes sent).bind fun lay => _) = _
    rw [hl]
    show ((laidFrom codes (base + lay.shapes.size) (pre ++ post)).map _) = _
    rw [ih]
    simp [List.append_assoc]

theorem Appends.nil (codes : Codes) (B B' : TreeBook) (e1 : B'.place = B.place)
    (e2 : B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape)) :
    Appends codes [] B B' :=
  ⟨{}, rfl, by rw [e1]; simp, by rw [e2]; simp⟩

theorem Appends.trans {codes : Codes} {s1 s2 : List (Array OracleNotice)} {B B' B'' : TreeBook}
    (h1 : Appends codes s1 B B') (h2 : Appends codes s2 B' B'') :
    Appends codes (s1 ++ s2) B B'' := by
  obtain ⟨A, a1, a2, a3⟩ := h1
  obtain ⟨R, r1, r2, r3⟩ := h2
  rw [size_of_shapes a3] at r1
  exact ⟨_, laidFrom_join codes s1 s2 _ A R a1 r1, by rw [r2, a2, List.append_assoc],
    by rw [r3, a3, List.append_assoc]⟩

/-- A step that makes no tree, moves no place and keeps what is public of the trees appends nothing.
-/
theorem appends_same (codes : Codes) (B B' : TreeBook) (hs : SameN B B') (hk : BookKeeps B B') :
    Appends codes [] B B' := by
  refine Appends.nil codes B B' hs.2 ?_
  apply List.ext_getElem?
  intro z
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  cases hz : B.trees[z]? with
  | none =>
    have : B'.trees[z]? = none := by
      rw [Array.getElem?_eq_none_iff] at hz ⊢
      rw [hs.1]
      exact hz
    rw [this]
  | some T =>
    obtain ⟨T', h1, h2, _⟩ := hk.tree z T hz
    rw [h1]
    show some T'.shape = some T.shape
    rw [h2]

/-- A receiving appends its own layout. -/
theorem appends_recv (codes : Codes) (ft roots : ℕ) (S : Statement) (Bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (hl : layTrees codes sent = some lay) :
    Appends codes [sent] Bk (bookSentP ft roots S Bk sent lay) := by
  refine ⟨{ places := placesOf Bk.trees.size sent.size lay ++ []
            shapes := lay.shapes.toList ++ [] }, ?_, ?_, ?_⟩
  · show ((layTrees codes sent).bind fun lay => _) = _
    rw [hl]
    rfl
  · show _ = _ ++ (placesOf Bk.trees.size sent.size lay ++ [])
    rw [List.append_nil]
    exact recv_places ft Bk sent lay S.oracles.size roots
  · show _ = _ ++ (lay.shapes.toList ++ [])
    rw [List.append_nil]
    exact recv_shapes ft Bk sent lay S.oracles.size roots

/-- The sending at the switch into stage j + 1, off the place's numbers. -/
def sendAt (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (last : Bool) : Array OracleNotice :=
  match stageAt p (j + 1) nxt with
  | some nx => Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx)
  | none => #[]

/-- The test's sendings from stage j on. -/
def sendsFrom (p : P12) : ℕ → List Fmt.M1.Stage → List (Array OracleNotice)
  | _, [] => []
  | j, nxt :: rest => sendAt p j nxt rest.isEmpty :: sendsFrom p (j + 1) rest

/-- The fold's part, where the mask has come: it appends nothing. -/
theorem fold_appends (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t.mask.isSome = true)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : t1.book = t.book := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨hn, _⟩
  · rfl
  · rw [hn] at hm
    cases hm

/-- The switch's part and the batching behind it append the switch's sending. -/
theorem switch_appends (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    Appends t1.st.codes [sendAt p j nxt last] t1.book t3.book := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, _⟩ := H2K.FoldLaw.bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    obtain ⟨i, left, _, hb, _, _, _, hread⟩ := hd.read
    have s := readOld_same i _ _ _ _ hread
    have k := readOld_keeps i _ _ _ _ hread
    rw [hb] at s k
    have es : sendAt p j nxt last =
        Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx) := by
      unfold sendAt
      rw [e2]
    rw [es]
    have a1 := appends_recv t1.st.codes p.nums.firstTree t1.roots t1.st t1.book _ D.lay hd.trees
    have a2 := appends_same t1.st.codes _ _ s k
    have := a1.trans a2
    rwa [List.append_nil] at this
  · cases h1'

/-- **Along the stages.** -/
theorem stages_appends (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : K12.Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs), t.mask.isSome = true →
      (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE →
      Appends t.st.codes (sendsFrom p j rest) t.book tE.book
  | [], j, cur, l, t, tE, rs, gs, _, h => by
    rw [stagesFrom_last] at h
    have h' := (ranged_ok _ _ _ _ _ _ h).1
    exact appends_same _ _ _ (baseJ5_bk p j cur _ t tE rs gs h').1
      (baseJ5_keeps p j cur _ t tE rs gs h').1.book
  | nxt :: rest, j, cur, l, t, tE, rs, gs, hm, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, f4, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
    have hX := like_P5 p
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur l : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := hX.fold _ _ _ _ _ _ _ f1
    have e1 := fold_appends p j cur _ t t1 _ _ hm f1'
    have c1 := (foldJ_keeps p j cur _ t t1 _ _ f1').codes
    have a2 := switch_appends p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    have c2 := (switch_keeps p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)).codes
    have hm3 : t3.mask.isSome = true := by
      rw [he] at f4
      simpa using f4
    have a3 := stages_appends p he ha rest (j + 1) nxt _ t3 tE _ _ hm3 f5
    rw [c2, c1] at a3
    rw [c1, e1] at a2
    exact a2.trans a3

/-- **The whole test**: from a record at which the first fold's mask has come. -/
theorem k12_appends (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t0.mask.isSome = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ first rest, p.nums.stages = first :: rest ∧
      Appends t0.st.codes (sendsFrom p 0 rest) t0.book tE.book := by
  have hX := like_P5 p
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := H2K.FoldLaw.bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have a := stages_appends p he ha rest 0 first _
    { tF with st := begun tF.st tF.g G, pass := .claim row L } tE _ _ hm hst
  have hc : (begun tF.st tF.g G).codes = tF.st.codes := closeLedgers_codes _ _
  dsimp only at a
  rw [hc] at a
  exact ⟨first, rest, hs, a⟩

/-- **"The seats are carried" rides through what is appended**, where the plan's lists go on so. -/
theorem seatsPrefix_appends (L : Laid) (codes : Codes) (sends : List (Array OracleNotice))
    (B B' : TreeBook) (h : SeatsPrefix L B) (ha : Appends codes sends B B')
    (hgo : ∀ A, laidFrom codes B.trees.size sends = some A →
      (L.places.drop B.place.size).take A.places.length = A.places ∧
      (L.shapes.drop B.trees.size).take A.shapes.length = A.shapes) : SeatsPrefix L B' := by
  obtain ⟨A, a1, a2, a3⟩ := ha
  obtain ⟨g1, g2⟩ := hgo A a1
  exact seatsPrefix_append L B B' A.places A.shapes h a2 a3 g1 g2

/-- A TEST WITH CODE: the plan's lists go on, behind n places and m trees, with what these sendings
lay. -/
def goesOnB (L : Laid) (codes : Codes) (n m : ℕ) (sends : List (Array OracleNotice)) : Bool :=
  match laidFrom codes m sends with
  | some A =>
    (L.places.drop n).take A.places.length == A.places &&
      (L.shapes.drop m).take A.shapes.length == A.shapes
  | none => false

theorem goesOn_of_B {L : Laid} {codes : Codes} {n m : ℕ} {sends : List (Array OracleNotice)}
    (h : goesOnB L codes n m sends = true) (A : Laid) (hA : laidFrom codes m sends = some A) :
    (L.places.drop n).take A.places.length = A.places ∧
      (L.shapes.drop m).take A.shapes.length = A.shapes := by
  unfold goesOnB at h
  rw [hA] at h
  simpa using h

/-- **Through the test's block at the first chain's finish.** -/
theorem atFinish_seats (L : Laid) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (s s' : First.S) (rs : List Fmt.RoundView) (gs : Gs) (h : (atFinish p).decide s rs gs = .ok s')
    (hm : ∀ t, enterFinish s = .ok t → t.mask.isSome = true) (hS : SeatsPrefix L s.book)
    (hgo : ∀ first rest A, p.nums.stages = first :: rest →
      laidFrom s.st.codes s.book.trees.size (sendsFrom p 0 rest) = some A →
      (L.places.drop s.book.place.size).take A.places.length = A.places ∧
      (L.shapes.drop s.book.trees.size).take A.shapes.length = A.shapes) :
    SeatsPrefix L s'.book := by
  have h' : ((enterFinish s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (leaveFinish s)) = .ok s' := h
  obtain ⟨t, ht, h1⟩ := H2K.FoldLaw.bind_ok h'
  obtain ⟨tE, hk, h2⟩ := H2K.FoldLaw.bind_ok h1
  have e2 : s' = { s with st := tE.st, book := tE.book, roots := tE.roots } :=
    (Except.ok.inj h2).symm
  have et : t.book = s.book ∧ t.st = s.st := by
    unfold enterFinish at ht
    split at ht
    · obtain ⟨_, _, ht⟩ := H2K.FoldLaw.bind_ok ht
      obtain ⟨_, _, ht⟩ := H2K.FoldLaw.bind_ok ht
      cases ht
      exact ⟨rfl, rfl⟩
    · cases ht
  obtain ⟨first, rest, hs, a⟩ := k12_appends p he ha t tE rs gs (hm t ht) hk
  rw [et.1, et.2] at a
  rw [e2]
  exact seatsPrefix_appends L _ _ _ _ hS a fun A hA => hgo first rest A hs hA

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.Appends.trans
#print axioms VerifiableInference.Desc.K12.Coin.switch_appends
#print axioms VerifiableInference.Desc.K12.Coin.stages_appends
#print axioms VerifiableInference.Desc.K12.Coin.k12_appends
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_seats
